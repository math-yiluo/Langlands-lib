import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitNormalizedCoefficient
import Langlands.AllFieldBZ.Representation.Induction.Equivalences
import Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.Representation.Geometric.ParabolicOrbitInductionTransport

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitInductionTransport`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitInductionTransport` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem refinedLeviModulus_of_diagonal
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.Induction
universe uG uH uV uW

section Pullback
variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

end Pullback
section Induction
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Induction
section Coefficient
variable (F : Type uG) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] {n : ℕ} [LocallyCompactSpace (GeneralLinear n F)]
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Coefficient
end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open CategoryTheory
open Langlands.GeneralLinear hiding SupercuspidalClass blockSum rankInclusion
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem refinedLeviModulus_of_diagonal
open Langlands.AllFieldBZ.Geometric
open Langlands.Induction
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : MinimalRepresentatives B C) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
  (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The literal geometric piece has the explicit inverse-conjugation pullbacks. -/
theorem geometricPieceFunctor_eq_pullback :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    Langlands.AllFieldBZ.Geometric.geometricPieceFunctor.{uF, uV} T B C w.val S R hS.2.1 hR.2.1 =
      T.normalizedRefinedJacquetFunctor B S ⋙
        smoothPullbackFunctor (MulEquiv.subgroupCongr hS.2.1).toMonoidHom
          (continuous_subtype_val.subtype_mk _) ⋙
        intersectionTransportFunctor F.Carrier B C w.val ⋙
        smoothPullbackFunctor (MulEquiv.subgroupCongr hR.2.1.symm).toMonoidHom
          (continuous_subtype_val.subtype_mk _) ⋙
        T.normalizedRefinedInductionFunctor C R ⋙ SmoothRep.toRep := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  unfold Langlands.AllFieldBZ.Geometric.geometricPieceFunctor
  rw [subgroupEqualityFunctor_eq_pullback, subgroupEqualityFunctor_eq_pullback]

/-- Move the target inverse half through induction, identify the normalized
coefficient, and use compactness of the actual refined parabolic quotient. -/
def parabolicOrbitInductionTransportEquiv
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    (twist (Jacquet.inverseHalfCharacter (T.leviModulus C))
      (compactInduced (parabolicOrbitStagesQuotient F.Carrier B C w.val)
        (parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ))).Equiv
      (T.normalizedRefinedInduced C R
        (refinedIntersectionTransport F.Carrier B C w.val S R hS.2.1 hR.2.1
          (T.normalizedRefinedJacquet B S ρ))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let K := parabolicOrbitStagesQuotient F.Carrier B C w.val
  have hK : K = refinedParabolic F.Carrier C R :=
    (parabolicOrbitStages_comap_section F.Carrier B C w.val).trans hR.1
  have : CompactSpace (LeftQuotient K) := by
    rw [hK]
    exact Parabolic.refinedParabolicQuotientCompact F T C R
  let χ : SmoothCharacter ℂ (C.Levi F.Carrier) :=
    ⟨Jacquet.inverseHalfCharacter (T.leviModulus C),
      Jacquet.isOpen_ker_inverseHalfCharacter _ (T.isOpen_ker_leviModulus C)⟩
  let e₁ := compactInductionTwistEquiv K χ
    (parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ)
  let e₂ := compactSmoothEquiv K (T.parabolicOrbitNormalizedNestedCoefficient B C w ρ)
  let e₃ := smoothInducedEquiv K
    (T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ)
  let e₄ := smoothInducedSubgroupCongr K (refinedParabolic F.Carrier C R) hK
    (twist (T.refinedParabolicHalfModulus C R)
      ((refinedIntersectionTransport F.Carrier B C w.val S R hS.2.1 hR.2.1
        (T.normalizedRefinedJacquet B S ρ)).comp (refinedLeviProjection F.Carrier C R)))
  exact ((e₁.trans e₂).trans e₃).trans e₄

/-- Evaluation of the transport is coefficient transport after multiplication
by the target inverse half modulus. -/
theorem parabolicOrbitInductionTransportEquiv_eval
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (f : CompactFunctions (parabolicOrbitStagesQuotient F.Carrier B C w.val)
      (parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ))
      (x : C.Levi F.Carrier),
    eval _ _ (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR ρ f) x =
      T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ
        ((Jacquet.inverseHalfCharacter (T.leviModulus C) x : ℂ) •
          eval _ _ f.val x) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro f x
  let K := parabolicOrbitStagesQuotient F.Carrier B C w.val
  let σ := parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ
  let τ := twist (T.refinedParabolicHalfModulus C R)
    ((refinedIntersectionTransport F.Carrier B C w.val S R hS.2.1 hR.2.1
      (T.normalizedRefinedJacquet B S ρ)).comp (refinedLeviProjection F.Carrier C R))
  have hK : K = refinedParabolic F.Carrier C R :=
    (parabolicOrbitStages_comap_section F.Carrier B C w.val).trans hR.1
  have : CompactSpace (LeftQuotient K) := by
    rw [hK]
    exact Parabolic.refinedParabolicQuotientCompact F T C R
  let χ : SmoothCharacter ℂ (C.Levi F.Carrier) :=
    ⟨Jacquet.inverseHalfCharacter (T.leviModulus C),
      Jacquet.isOpen_ker_inverseHalfCharacter _ (T.isOpen_ker_leviModulus C)⟩
  let e₁ := compactInductionTwistEquiv K χ σ
  let e₂ := compactSmoothEquiv K (T.parabolicOrbitNormalizedNestedCoefficient B C w ρ)
  let e₃ := smoothInducedEquiv K
    (T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ)
  exact (smoothInducedSubgroupCongr_eval K (refinedParabolic F.Carrier C R) hK
    τ (e₃ (e₂ (e₁ f))) x).trans (by rfl)

/-- The induction transport commutes with every original source intertwiner. -/
theorem parabolicOrbitInductionTransportEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ z : CompactFunctions (parabolicOrbitStagesQuotient F.Carrier B C w.val)
      (parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ),
    T.parabolicOrbitInductionTransportEquiv B C w S R hS hR τ
      (compactInducedMap (parabolicOrbitStagesQuotient F.Carrier B C w.val)
        (parabolicOrbitIntegratedCoefficientMap F.Carrier B C w.val
          (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedInducedMap C R
        (refinedIntersectionTransportMap F.Carrier B C w.val S R hS.2.1 hR.2.1
          (T.normalizedRefinedJacquetMap B S f))
        (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR ρ z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro z
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change eval _ _ (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR τ
      (compactInducedMap (parabolicOrbitStagesQuotient F.Carrier B C w.val)
        (parabolicOrbitIntegratedCoefficientMap F.Carrier B C w.val
          (T.leviHalfModulus B) f) z)) x =
    T.normalizedRefinedJacquetMap B S f
      (eval _ _ (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR ρ z) x)
  have hτ := T.parabolicOrbitInductionTransportEquiv_eval B C w S R hS hR τ
    (compactInducedMap (parabolicOrbitStagesQuotient F.Carrier B C w.val)
      (parabolicOrbitIntegratedCoefficientMap F.Carrier B C w.val
        (T.leviHalfModulus B) f) z) x
  have hρ := T.parabolicOrbitInductionTransportEquiv_eval B C w S R hS hR ρ z x
  refine Eq.trans hτ (Eq.trans ?_ (congrArg (T.normalizedRefinedJacquetMap B S f) hρ).symm)
  change T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR τ
      ((Jacquet.inverseHalfCharacter (T.leviModulus C) x : ℂ) •
        Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F.Carrier B C w.val (T.leviHalfModulus B) f)
          (eval _ _ z.val x)) =
    T.normalizedRefinedJacquetMap B S f
      (T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ
        ((Jacquet.inverseHalfCharacter (T.leviModulus C) x : ℂ) • eval _ _ z.val x))
  simpa only [map_smul] using
    T.parabolicOrbitNormalizedNestedCoefficientEquiv_natural B C w S R hS hR f
      ((Jacquet.inverseHalfCharacter (T.leviModulus C) x : ℂ) • eval _ _ z.val x)

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
