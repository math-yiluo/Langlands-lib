import Langlands.Global.AdelicParabolicSpectrum
import Langlands.Global.AdelicCharacterParameterEquivalences
import Langlands.Global.PositiveRealTorusLog
import Langlands.GroupScheme.Rational.NestedSplitComponentFactorization
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness

/-! # The relative and ambient factors of the actual parabolic parameter space -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicGroupPoints

open GroupScheme RestrictionSplitCentre PositiveRealTorus

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local notation "T₀" => canonicalTorus F G
local notation "i₀" => canonicalComponent F G
local notation "hi₀" => isSplitComponent_canonicalComponent F G

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem isClosedSubgroup_id : IsClosedSubgroup (𝟙 G) := by
  change IsClosedImmersion (𝟙 G.X.left)
  infer_instance

/-- The ambient split component lifted into the actual parabolic through its Levi. -/
def splitCentreParabolicLift : (T₀).toGrp ⟶ P :=
  r.intermediateCentralFactor (𝟙 G) isClosedSubgroup_id (l ≫ p) (Category.comp_id _)
    i₀ (hi₀).isCentralSplitTorus.isCentral ≫ l

omit [NumberField F] in
@[simp] theorem splitCentreParabolicLift_comp : splitCentreParabolicLift r ≫ p = i₀ := by
  exact (Category.assoc _ _ _).trans
    (r.intermediateCentralFactor_comp (𝟙 G) isClosedSubgroup_id (l ≫ p) (Category.comp_id _)
      i₀ (hi₀).isCentralSplitTorus.isCentral)

/-- Restriction from `G` to its split component is an isomorphism of real parameters. -/
def ambientSplitComponentParameterEquiv (hG : IsConnectedReductive G) :
    RealCharacterParameter F G ≃ₗ[ℝ] RealCharacterParameter F (T₀).toGrp :=
  realCharacterParameterPullbackEquiv i₀
    (characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hG hi₀)
    ((hi₀).finiteIndex_range_characterRestrict hG)

/-- Choose one real coordinate chart in the actual ambient parameters for all parabolics.
Finiteness follows from restriction to the ambient split component. -/
def ambientParameterChart (hG : IsConnectedReductive G) :
    (Fin (Module.finrank ℝ (RealCharacterParameter F G)) → ℝ) ≃ₗ[ℝ]
      RealCharacterParameter F G := by
  let : Module.Finite ℤ (characterLattice T₀) :=
    (hi₀).isCentralSplitTorus.isSplitSubtorus.1.finite_characterLattice
  let e := (rationalCharacters.equivCharacterLattice T₀).symm
  let : Module.Finite ℤ (rationalCharacters (T₀).toGrp) :=
    Module.Finite.of_surjective e.toAddMonoidHom.toIntLinearMap e.surjective
  let : FiniteDimensional ℝ (RealCharacterParameter F (T₀).toGrp) :=
    inferInstanceAs (Module.Finite ℝ (ℝ ⊗[ℤ] rationalCharacters (T₀).toGrp))
  let : FiniteDimensional ℝ (RealCharacterParameter F G) :=
    (ambientSplitComponentParameterEquiv (F := F) hG).symm.finiteDimensional
  exact (Module.finBasis ℝ (RealCharacterParameter F G)).equivFun.symm

variable [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]

/-- The published relative parameter space is exactly the kernel of restriction to the lifted
ambient split component. The actual positive subgroup detects all its real parameters. -/
theorem relativeParameterSpace_eq_ker_centralRestriction :
    relativeParameterSpace (F := F) p = LinearMap.ker (realCharacterParameterPullback (splitCentreParabolicLift r)) := by
  apply Submodule.ext
  intro x
  simp only [relativeParameterSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  constructor
  · intro h
    apply (realParameterPairing_eq_zero_iff _).mp
    intro H
    obtain ⟨I, hI, ⟨e⟩⟩ := (hi₀).isCentralSplitTorus.isSplitSubtorus.1
    let : Fintype I := Fintype.ofFinite I
    let E := positiveLogEquiv F T₀ I e
    let z := E.symm (Multiplicative.ofAdd H)
    have hz : characterLog F (T₀).toGrp z.val = H :=
      congrArg Multiplicative.toAdd (E.apply_symm_apply (Multiplicative.ofAdd H))
    have hm : map F P G p (map F (T₀).toGrp P (splitCentreParabolicLift r) z.val) ∈ canonicalSubgroup F G := by
      rw [← map_comp_apply_of_hom, splitCentreParabolicLift_comp, canonicalSubgroup_eq_imageSubgroup]
      exact ⟨z.val, z.property, rfl⟩
    rw [← hz, realParameterPairing_pullback, ← characterLog_map]
    exact h _ hm
  · intro h q hq
    rw [canonicalSubgroup_eq_imageSubgroup] at hq
    obtain ⟨z, _, hq⟩ := hq
    have hq' : map F P G p (map F (T₀).toGrp P (splitCentreParabolicLift r) z) = map F P G p q := by
      rw [← map_comp_apply_of_hom, splitCentreParabolicLift_comp]
      exact hq
    have heq := (isClosedEmbedding_map F P G p).injective hq'
    rw [← heq, characterLog_map, ← realParameterPairing_pullback, h, map_zero, LinearMap.zero_apply]

/-- The ambient coordinate of a full parabolic parameter, by restriction to the lifted split
centre followed by inverse restriction from `G`. -/
def ambientParameterProjection (hG : IsConnectedReductive G) :
    RealCharacterParameter F P →ₗ[ℝ] RealCharacterParameter F G :=
  (ambientSplitComponentParameterEquiv (F := F) hG).symm.toLinearMap.comp
    (realCharacterParameterPullback (splitCentreParabolicLift r))

omit [NumberField F] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
@[simp] theorem ambientParameterProjection_pullback (hG : IsConnectedReductive G)
    (z : RealCharacterParameter F G) :
    ambientParameterProjection r hG (realCharacterParameterPullback p z) = z := by
  change (ambientSplitComponentParameterEquiv hG).symm
    ((realCharacterParameterPullback (splitCentreParabolicLift r)).comp (realCharacterParameterPullback p) z) = z
  rw [← realCharacterParameterPullback_comp, splitCentreParabolicLift_comp,
    ← realCharacterParameterPullbackEquiv_apply i₀
      (characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hG hi₀)
      ((hi₀).finiteIndex_range_characterRestrict hG)]
  exact (ambientSplitComponentParameterEquiv hG).symm_apply_apply z

/-- The ambient projection vanishes precisely on the existing relative parameter space. -/
theorem ambientParameterProjection_eq_zero_iff (hG : IsConnectedReductive G)
    (x : RealCharacterParameter F P) :
    ambientParameterProjection r hG x = 0 ↔ x ∈ relativeParameterSpace (F := F) p := by
  rw [relativeParameterSpace_eq_ker_centralRestriction r, LinearMap.mem_ker]
  change (ambientSplitComponentParameterEquiv (F := F) hG).symm
    (realCharacterParameterPullback (splitCentreParabolicLift r) x) = 0 ↔
    realCharacterParameterPullback (splitCentreParabolicLift r) x = 0
  simp only [LinearEquiv.map_eq_zero_iff]

/-- The intrinsic direct product of the relative parameters and ambient parameters is the
whole parameter space. The map adds the existing relative inclusion to actual ambient pullback. -/
def relativeAmbientParameterEquiv (hG : IsConnectedReductive G) :
    (relativeParameterSpace (F := F) p × RealCharacterParameter F G) ≃ₗ[ℝ] RealCharacterParameter F P where
  toFun z := z.1.val + realCharacterParameterPullback p z.2
  invFun x :=
    (⟨x - realCharacterParameterPullback p (ambientParameterProjection r hG x),
      (ambientParameterProjection_eq_zero_iff r hG _).mp (by
        rw [map_sub, ambientParameterProjection_pullback, sub_self])⟩,
      ambientParameterProjection r hG x)
  left_inv := by
    rintro ⟨x, z⟩
    have hx := (ambientParameterProjection_eq_zero_iff r hG x.val).mpr x.property
    have hz : ambientParameterProjection r hG (x.val + realCharacterParameterPullback p z) = z := by
      rw [map_add, hx, ambientParameterProjection_pullback, zero_add]
    refine Prod.ext (Subtype.ext ?_) hz
    change x.val + realCharacterParameterPullback p z -
      realCharacterParameterPullback p (ambientParameterProjection r hG
        (x.val + realCharacterParameterPullback p z)) = x.val
    rw [hz, add_sub_cancel_right]
  right_inv x := sub_add_cancel _ _
  map_add' x y := by
    change x.1.val + y.1.val + realCharacterParameterPullback p (x.2 + y.2) = _
    rw [map_add]
    ac_rfl
  map_smul' c x := by
    change c • x.1.val + realCharacterParameterPullback p (c • x.2) = c • (_ + _)
    rw [map_smul, smul_add]

@[simp] theorem relativeAmbientParameterEquiv_apply (hG : IsConnectedReductive G)
    (x : relativeParameterSpace (F := F) p) (z : RealCharacterParameter F G) :
    relativeAmbientParameterEquiv r hG (x, z) = x.val + realCharacterParameterPullback p z := rfl

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- Imaginary inclusion commutes with the actual character pullbacks. -/
theorem imaginaryParameter_pullback (z : RealCharacterParameter F G) :
    imaginaryParameter F P (realCharacterParameterPullback p z) =
      parameterRestrict p (imaginaryParameter F G z) := by
  induction z using TensorProduct.inductionOn with
  | tmul t χ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- In imaginary parameters, the product map is exactly relative inclusion followed by ambient
shift. -/
theorem imaginaryParameter_relativeAmbientParameterEquiv (hG : IsConnectedReductive G)
    (x : relativeParameterSpace (F := F) p) (z : RealCharacterParameter F G) :
    imaginaryParameter F P (relativeAmbientParameterEquiv r hG (x, z)) =
      imaginaryParameter F P x.val + parameterRestrict p (imaginaryParameter F G z) := by
  rw [relativeAmbientParameterEquiv_apply, map_add, imaginaryParameter_pullback]

end Langlands.Global.AdelicGroupPoints
