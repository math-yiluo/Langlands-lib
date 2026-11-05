import Langlands.Representation.Plancherel.ParabolicIntertwiningStatement
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Topology of actual intertwining cones and twist-class orbits -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uL uI uV uX

section Orbit

variable {L : Type uL} [Group L] [TopologicalSpace L] [NonarchimedeanGroup L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
  (π : SmoothRep.{0, uL, uV} ℂ L)

theorem unramifiedTwistClass_one :
    unramifiedTwistClass ν π 1 = SmoothRep.isoClass π :=
  SmoothRep.IsoClass.twist_one (unramifiedCharacter_isOpen_ker ν 1) (SmoothRep.isoClass π)

theorem unramifiedTwistClass_mul (χ ψ : unramifiedCharacters ν) :
    unramifiedTwistClass ν π (χ * ψ) =
      SmoothRep.IsoClass.twist χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν χ) (unramifiedTwistClass ν π ψ) :=
  (SmoothRep.IsoClass.twist_twist χ.val.toMonoidHom ψ.val.toMonoidHom
    (unramifiedCharacter_isOpen_ker ν χ) (unramifiedCharacter_isOpen_ker ν ψ)
    (unramifiedCharacter_isOpen_ker ν (χ * ψ)) (SmoothRep.isoClass π)).symm

/-- The subgroup of characters whose actual twists are isomorphic to the input. -/
def smoothRepUnramifiedTwistStabilizer : Subgroup (unramifiedCharacters ν) where
  carrier := {χ | unramifiedTwistClass ν π χ = SmoothRep.isoClass π}
  one_mem' := unramifiedTwistClass_one ν π
  mul_mem' := by
    intro χ ψ hχ hψ
    change unramifiedTwistClass ν π (χ * ψ) = _
    rw [unramifiedTwistClass_mul, hψ]
    exact hχ
  inv_mem' := by
    intro χ hχ
    have ht := congrArg
      (SmoothRep.IsoClass.twist (χ⁻¹).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν χ⁻¹)) hχ
    change _ = unramifiedTwistClass ν π χ⁻¹ at ht
    rw [← unramifiedTwistClass_mul, inv_mul_cancel, unramifiedTwistClass_one] at ht
    exact ht.symm

theorem unramifiedTwistClass_eq_iff (χ ψ : unramifiedCharacters ν) :
    unramifiedTwistClass ν π χ = unramifiedTwistClass ν π ψ ↔
      χ⁻¹ * ψ ∈ smoothRepUnramifiedTwistStabilizer ν π := by
  constructor
  · intro h
    change unramifiedTwistClass ν π (χ⁻¹ * ψ) = _
    rw [unramifiedTwistClass_mul, ← h, ← unramifiedTwistClass_mul,
      inv_mul_cancel, unramifiedTwistClass_one]
  · intro h
    change unramifiedTwistClass ν π (χ⁻¹ * ψ) = SmoothRep.isoClass π at h
    have ht := congrArg
      (SmoothRep.IsoClass.twist χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν χ)) h
    change _ = unramifiedTwistClass ν π χ at ht
    rw [← unramifiedTwistClass_mul, mul_inv_cancel_left] at ht
    exact ht.symm

/-- The full orbit saturation is the union of all stabilizer translates. -/
theorem unramifiedTwistOrbitSaturation_eq_mul (Ω : Set (unramifiedCharacters ν)) :
    unramifiedTwistOrbitSaturation ν π Ω = Ω * (smoothRepUnramifiedTwistStabilizer ν π : Set _) := by
  ext χ
  constructor
  · rintro ⟨ψ, hψ, heq⟩
    have hc : unramifiedTwistClass ν π ψ = unramifiedTwistClass ν π χ :=
      congrArg Subtype.val heq
    exact ⟨ψ, hψ, ψ⁻¹ * χ, (unramifiedTwistClass_eq_iff ν π ψ χ).mp hc,
      mul_inv_cancel_left ψ χ⟩
  · rintro ⟨ψ, hψ, ζ, hζ, rfl⟩
    refine ⟨ψ, hψ, Subtype.ext ?_⟩
    apply (unramifiedTwistClass_eq_iff ν π ψ (ψ * ζ)).mpr
    change unramifiedTwistClass ν π ζ = SmoothRep.isoClass π at hζ
    change unramifiedTwistClass ν π (ψ⁻¹ * (ψ * ζ)) = SmoothRep.isoClass π
    simpa only [inv_mul_cancel_left] using hζ

theorem isOpen_unramifiedTwistOrbitSaturation {Ω : Set (unramifiedCharacters ν)}
    (hΩ : IsOpen Ω) : IsOpen (unramifiedTwistOrbitSaturation ν π Ω) := by
  rw [unramifiedTwistOrbitSaturation_eq_mul]
  exact hΩ.mul_right

/-- The actual twist-class parameter map is open for every smooth input. -/
theorem isOpenMap_unramifiedTwistOrbitMap : IsOpenMap (unramifiedTwistOrbitMap ν π) := by
  intro Ω hΩ
  apply isOpen_coinduced.mpr
  exact isOpen_unramifiedTwistOrbitSaturation ν π hΩ

theorem isOpen_unramifiedTwistOrbitRegion {Ω : Set (unramifiedCharacters ν)}
    (hΩ : IsOpen Ω) : IsOpen (unramifiedTwistOrbitRegion ν π Ω) :=
  isOpenMap_unramifiedTwistOrbitMap ν π Ω hΩ

end Orbit

namespace SplitTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- Every real linear functional of the normalized real part varies continuously
when all character evaluations vary continuously. -/
theorem continuous_normalizedRealPart_apply {X : Type uX} [TopologicalSpace X]
    (hA : IsSplitTorus A.toGrp) (f : X → (rationalPoints A.toGrp →* ℂˣ))
    (hf : ∀ a, Continuous (fun x => f x a))
    (ℓ : RealTorusSpace.Vstar A →ₗ[ℝ] ℝ) :
    Continuous (fun x => ℓ (normalizedRealPart hA (f x))) := by
  obtain ⟨v, hv⟩ := (RealTorusSpace.isPerfPair_of_isSplitTorus hA).bijective_right.surjective ℓ
  have hcont (v : RealTorusSpace.V A) :
      Continuous (fun x => extendLatticeLog (sectionLog (f x)) v) := by
    induction v using TensorProduct.inductionOn with
    | tmul r c =>
      simp only [extendLatticeLog_tmul]
      refine continuous_const.mul ?_
      change Continuous (fun x =>
        -Real.log ‖(f x (CocharacterUniformizer.latticeSection F A (.ofAdd c)) : ℂ)‖ /
          Real.log (LocalField.residueCardinality F : ℝ))
      exact (((Units.continuous_val.comp (hf _)).norm.log
        (fun x => norm_ne_zero_iff.mpr (Units.ne_zero _))).neg).div_const _
    | add v w hv hw =>
      convert hv.add hw using 1
      ext x
      exact map_add _ v w
  simpa only [← hv, LinearMap.flip_apply, pair_normalizedRealPart] using hcont v

end SplitTorus

section Cones

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffine M.X.left]

local instance coneLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

/-- Finitely many actual-root inequalities define an open subset of the existing
continuous unramified-character space. -/
theorem isOpen_canonicalUnramifiedIntertwiningRegion
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M) (i : A.toGrp ⟶ G)
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) :
    IsOpen (canonicalUnramifiedIntertwiningRegion hA j i B U Uop' R) := by
  have heq : canonicalUnramifiedIntertwiningRegion hA j i B U Uop' R =
      ⋂ α ∈ intertwiningRelativeRoots i U Uop',
        {χ | R < B (SplitTorus.normalizedRealPart hA
          (χ.val.toMonoidHom.comp (rationalPoints.map j))) ((1 : ℝ) ⊗ₜ[ℤ] α)} := by
    ext χ
    simp only [canonicalUnramifiedIntertwiningRegion, characterIntertwiningRegion,
      intertwiningRegion, rootThresholdRegion, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  apply (finite_intertwiningRelativeRoots i hA U Uop').isOpen_biInter
  intro α _
  apply isOpen_lt continuous_const
  exact SplitTorus.continuous_normalizedRealPart_apply hA _
    (fun a => (continuous_eval_const (rationalPoints.map j a)).comp continuous_subtype_val)
    (B.flip ((1 : ℝ) ⊗ₜ[ℤ] α))

end Cones

section ParabolicCones

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P Q U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance parabolicConeAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance parabolicConeAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance parabolicConeLeviTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

theorem isOpen_parabolicUnramifiedIntertwiningRegion
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ) :
    IsOpen (parabolicUnramifiedIntertwiningRegion r B n q v R) :=
  isOpen_canonicalUnramifiedIntertwiningRegion
    r.isCompatible.splitComponent.1.isSplitSubtorus.1 a (a ≫ l ≫ p) B
    (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q)) R

/-- Openness on the literal ambient Levi point subgroup, with its full
rational-character norm family. -/
theorem isOpen_parabolicPointUnramifiedIntertwiningRegion
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ) :
    IsOpen (parabolicPointUnramifiedIntertwiningRegion r B n q v R) :=
  (isOpen_parabolicUnramifiedIntertwiningRegion r B n q v R).preimage
    (parabolicLeviUnramifiedCharactersHomeomorph r).symm.continuous

variable [NonarchimedeanGroup (rationalPoints G)]

/-- The actual-class orbit image is open for every inducing representation. -/
theorem isOpen_parabolicPointUnramifiedTwistOrbitRegion
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    IsOpen (unramifiedTwistOrbitRegion (parabolicLeviRationalNormCharacters r) π
      (parabolicPointUnramifiedIntertwiningRegion r B n q v R)) :=
  isOpen_unramifiedTwistOrbitRegion _ π
    (isOpen_parabolicPointUnramifiedIntertwiningRegion r B n q v R)

end ParabolicCones

end Langlands.Plancherel
