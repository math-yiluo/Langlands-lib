import Langlands.Representation.Geometric.CoefficientSupportJacquet
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetFinitenessStatement
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.Representation.Plancherel.UnramifiedRationalCoefficientAlgebra
import Langlands.Representation.Smooth.Admissibility.Extension

/-! The actual universal rational family and its native output support grades. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance supportAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance supportPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance supportFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

local instance supportTensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

/-- The actual tensor action over the complete rational-norm algebra, functorially
in the original complex inducing representation. -/
def universalTensorRepFunctor :
    SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l) ⥤
      Rep.{max u uV} (RegularAlgebra r) (parabolicLeviPointSubgroup p l) where
  obj π := Rep.of (universalRepresentation r π.representation)
  map f := Rep.ofHom
    (UnramifiedNormalized.tensorMap (parabolicLeviRationalNormCharacters r) (SmoothRep.hom f))
  map_id π := by
    apply Rep.hom_ext
    exact UnramifiedNormalized.tensorMap_id _ π.representation
  map_comp f g := by
    apply Rep.hom_ext
    exact UnramifiedNormalized.tensorMap_comp _ (SmoothRep.hom f) (SmoothRep.hom g)

variable {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  (hr : Continuous h.projection)

/-- Inflation and the exact positive full-parabolic half modulus on the actual
universal tensor; projection continuity supplies its smoothness. -/
def universalInducingSmoothFunctor :
    SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l) ⥤
      SmoothRep.{u, u, max u uV} (RegularAlgebra r) (ParabolicPoints p) :=
  (smoothRepProperty (RegularAlgebra r) (ParabolicPoints p)).lift
    (universalTensorRepFunctor r ⋙ Rep.resFunctor h.projection ⋙
      (UnramifiedNormalized.inductionCharacter (parabolicLeviRationalNormCharacters r)
        _ _ hU h.le_normalizer).twistFunctor)
    (fun π => isSmooth_inducingRepresentation r h hU hr π.representation π.isSmooth)

/-- The literal output dynamic parabolic at the identity test scheme. -/
abbrev outputParabolicPoints (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    Subgroup (rationalPoints G) :=
  (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The native quotient and actual inverse-half output normalization. -/
def outputNativeJacquetFunctor :
    Rep.{max u uV} (RegularAlgebra r) (rationalPoints G) ⥤
      Rep.{max u uV} (RegularAlgebra r) (outputLeviPoints χ) :=
  let d := Aubert.General.dynamic_isSemidirectDecomposition χ
    (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  let hc := BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ
  Jacquet.Localization.functor
    (BruhatTits.DynamicUnipotentContainment.unipotentPoints χ) 1
    (outputLeviPoints χ) d.levi_le_normalizer
    (Jacquet.Localization.isInvariant_one _ _ d.levi_le_normalizer) ⋙
      (UnramifiedNormalized.jacquetCharacter (parabolicLeviRationalNormCharacters r)
        _ _ hc d.levi_le_normalizer).twistFunctor

/-- The exact universal output Jacquet family, on its original function and
native relation-quotient carriers. -/
def universalOutputJacquetFunctor :
    SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l) ⥤
      Rep.{max u uV} (RegularAlgebra r) (outputLeviPoints χ) :=
  universalInducingSmoothFunctor r h hU hr ⋙
    Geometric.fullSmoothInductionRepFunctor (ParabolicPoints p) ⋙
      outputNativeJacquetFunctor r χ

/-- This functor uses precisely the action in the published finiteness target. -/
theorem universalOutputJacquetFunctor_obj
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    ((universalOutputJacquetFunctor r h hU hr χ).obj π).ρ =
      outputJacquetRepresentation r h hU π.representation χ := rfl

variable {m : ℕ}
  (s : Geometric.OrderedDoubleCosets (ParabolicPoints p) (outputParabolicPoints χ) m)

/-- Actual support images inside the published native normalized quotient.
Only ordered orbit geometry is supplied; the filtration itself is constructed. -/
def universalOutputJacquetSupportFiltration :
    RepFunctorFiltration (universalOutputJacquetFunctor.{u, uV} r h hU hr χ) m :=
  let d := Aubert.General.dynamic_isSemidirectDecomposition χ
    (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  let hc := BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ
  (s.nativeSmoothJacquetSupportFiltration
    (BruhatTits.DynamicUnipotentContainment.unipotentPoints χ) (outputLeviPoints χ)
    d.levi_le_normalizer d.levi_le
    (UnramifiedNormalized.jacquetCharacter (parabolicLeviRationalNormCharacters r)
      _ _ hc d.levi_le_normalizer)).precomp
    (universalInducingSmoothFunctor r h hU hr)

/-- Membership means that the same actual Jacquet class has a representative
whose projected nonzero support lies in the specified initial orbit union. -/
theorem mem_universalOutputJacquetSupportFiltration_step
    (k : Fin (m + 1)) (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (q : Jacquet.Localization.Coinvariants (inducedRepresentation r h hU π.representation)
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints χ) 1) :
    q ∈ ((universalOutputJacquetSupportFiltration r h hU hr χ s).step k).obj π ↔
      ∃ f : Induced r h hU π.representation,
        (∀ x : rationalPoints G,
          Induction.eval (ParabolicPoints p) (inducingRepresentation r h hU π.representation)
            f x ≠ 0 → Induction.quotientMap (ParabolicPoints p) x ∈ s.initialOrbits k) ∧
        Jacquet.Localization.mk (inducedRepresentation r h hU π.representation)
          (BruhatTits.DynamicUnipotentContainment.unipotentPoints χ) 1 f = q :=
  Iff.rfl

/-- The native quotient of the actual compact stabilizer orbit induction,
with the original output Levi and its exact inverse-half normalization. -/
def universalOutputOrbitJacquetFunctor (w : rationalPoints G) :
    SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l) ⥤
      Rep.{max u uV} (RegularAlgebra r) (outputLeviPoints χ) :=
  let d := Aubert.General.dynamic_isSemidirectDecomposition χ
    (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  let hc := BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ
  universalInducingSmoothFunctor r h hU hr ⋙
    Geometric.orbitPiece (ParabolicPoints p) (outputParabolicPoints χ) w ⋙
      Jacquet.Localization.Coefficient.subgroupFunctor
        (BruhatTits.DynamicUnipotentContainment.unipotentPoints χ)
        (outputLeviPoints χ) d.levi_le_normalizer (outputParabolicPoints χ)
        d.unipotent_le d.levi_le ⋙
      (UnramifiedNormalized.jacquetCharacter (parabolicLeviRationalNormCharacters r)
        _ _ hc d.levi_le_normalizer).twistFunctor

variable [CompactSpace (Induction.LeftQuotient (ParabolicPoints p))]

set_option maxHeartbeats 800000 in
/-- Every actual native support grade is the normalized native quotient of its
compact orbit piece. Rational finite orbit geometry remains an explicit input. -/
def universalOutputJacquetSupportGradedOrbitIso (hG : IsConnectedReductive G) (i : Fin m) :
    (universalOutputJacquetSupportFiltration.{u, uV} r h hU hr χ s).graded i ≅
      universalOutputOrbitJacquetFunctor.{u, uV} r h hU hr χ (s.representative i) := by
  letI : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  letI : SecondCountableTopology (rationalPoints G) :=
    Aubert.General.RationalPointFamily.reductiveRationalPoint_secondCountable F G hG
  letI : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : Smooth G.X.hom := hG.smooth
  have hc : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
  letI : IsClosedImmersion p.hom.hom.left := hc
  have hrep : (SubgroupFunctor.range p).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hP : IsClosed (ParabolicPoints p : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (SubgroupFunctor.range p) p hrep hc
  let d := Aubert.General.dynamic_isSemidirectDecomposition χ
    (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  have hlim : Jacquet.Localization.IsLimitOfCompactSubgroups
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints χ) := by
    intro C hC
    obtain ⟨K, hK, hCK⟩ :=
      BruhatTits.DynamicUnipotentContainment.exists_compactOpenSubgroup χ C hC
    exact ⟨K.toSubgroup, hK, hCK⟩
  exact
    (s.nativeSmoothJacquetSupportFiltration _ _ d.levi_le_normalizer d.levi_le
      (UnramifiedNormalized.jacquetCharacter (parabolicLeviRationalNormCharacters r)
        _ _ (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ)
        d.levi_le_normalizer)).precompGradedIso
          (universalInducingSmoothFunctor r h hU hr) i ≪≫
      Functor.isoWhiskerLeft (universalInducingSmoothFunctor r h hU hr)
        (s.nativeSmoothJacquetSupportGradedOrbitIso _ _ d.levi_le_normalizer d.levi_le
          d.unipotent_le hlim hP (Aubert.General.isClosed_dynamic_parabolic F G χ) _ i)

/-- The actual rational coefficient ring is Noetherian, so admissibility of
these computed orbit quotients suffices for admissibility of the original
normalized native Jacquet family. The orbit admissibility premise remains open. -/
theorem universalOutputJacquet_isAdmissible_of_orbits (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (horbits : ∀ i : Fin m,
      IsAdmissible ((universalOutputOrbitJacquetFunctor r h hU hr χ
        (s.representative i)).obj π).ρ) :
    IsAdmissible (outputJacquetRepresentation r h hU π.representation χ) := by
  let := regularAlgebra_isNoetherianRing r
  let t := universalOutputJacquetSupportFiltration.{u, uV} r h hU hr χ s
  let f := ObjectRepFiltration.ofSubrepresentations (fun k => (t.step k).obj π)
    (t.monotone π) (t.zero π) (t.top π)
  apply isAdmissible_of_objectRepFiltration f
  · exact UnramifiedNormalized.isSmooth_jacquetRepresentation _
      (Aubert.General.dynamic_isSemidirectDecomposition χ
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
      (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ)
      (inducedRepresentation r h hU π.representation)
      (isSmooth_inducedRepresentation r h hU π.representation)
  · intro i
    let e := (universalOutputJacquetSupportGradedOrbitIso r h hU hr χ s hG i).app π
    exact isAdmissible_of_injective e.hom.hom
      (Representation.equivOfIso e).injective (horbits i)

end Langlands.Plancherel.RationalNormalized
