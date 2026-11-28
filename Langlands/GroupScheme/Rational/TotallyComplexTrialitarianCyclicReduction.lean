import Langlands.Algebra.NumberFieldReducedNormLocalityProof
import Langlands.GroupScheme.Rational.NumberFieldTrialitarianQuadraticKernel
import Langlands.GroupScheme.Rational.NumberFieldTypeE6LeviReduction
import Langlands.GroupScheme.Rational.TotallyComplexQuasiSplitTrialitarian
import Langlands.GroupScheme.Rational.TrialitarianStarSign
import Langlands.GroupScheme.Rational.InnerFormTrivialityBaseChange

/-! # Reduction of quasi-split trialitarian vanishing to a cyclic cubic diagram field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Quasi-split trialitarian vanishing over totally imaginary number fields
with even star permutations, equivalently with a cyclic cubic diagram field. -/
def TotallyComplexQuasiSplitCyclicTrialitarianCocycleVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → IsQuasiSplit G →
    (∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) →
    (∀ a : d.Vertex, e a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) →
    (∀ σ, d.starSign e σ = 1) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial

/-- Vanishing in the cyclic cubic case suffices for both diagram actions.
In the symmetric-group case restrict to the field of the sign kernel, then
apply the relative quadratic Hasse kernel over the original field. -/
theorem totallyComplexQuasiSplitTrialitarian_of_cyclic
    (hcyc : TotallyComplexQuasiSplitCyclicTrialitarianCocycleVanishingStatement.{u}) :
    TotallyComplexQuasiSplitTrialitarianCocycleVanishingStatement.{u} := by
  classical
  intro F _ _ _ G _ _ d e hsc hAbs hG hD hno L _ _ _ _ ξ
  by_cases heven : ∀ σ, d.starSign e σ = 1
  · exact hcyc F G d e hsc hAbs hG hD hno heven L ξ
  obtain ⟨Q, hfd, hg, hdeg, he⟩ := d.exists_evenStarQuadratic e heven
  let : FiniteDimensional F Q := hfd
  let : IsGalois F Q := hg
  let : NumberField Q := NumberField.of_module_finite F Q
  let : IsTotallyComplex Q := isTotallyComplex_of_algebra F Q
  let b := algebraBaseMap F Q
  let GQ := (GroupScheme.baseChange b).obj G
  let : IsAffineHom GQ.X.hom := inferInstanceAs
    (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : LocallyOfFiniteType GQ.X.hom := inferInstanceAs
    (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : Algebra Q (SeparableClosure Q) := (separableClosure Q (AlgebraicClosure Q)).algebra
  let C := d.prescribedStabilizerIndexComparison Q
  let eQ := C.vertices.symm.trans e
  have hqs := hG.fieldExtension (K := Q)
  obtain ⟨hDQ, hnoQ⟩ := d.prescribedStabilizerIndex_D4_of_not_three_dvd_finrank Q e hD hno (by simp [hdeg])
  have heQ (τ : SeparableClosure Q ≃ₐ[Q] SeparableClosure Q) : C.index.starSign eQ τ = 1 := by
    let s := (AlgEquiv.autCongr (TitsIndexData.prescribedStabilizerClosureEquiv Q) τ)
    let σ := (IntermediateField.fixingSubgroupEquiv Q).symm s
    exact (d.starSign_prescribedStabilizerIndex Q e τ).trans (he σ.val σ.property)
  have hξ := ξ.locallyTrivial_of_totallyComplex (inferInstance : IsTotallyComplex F) hsc
  have hsplit : (ξ.baseChangePullback b).IsTrivial := by
    apply ξ.isTrivial_baseChangePullback_of_numberFieldKernel hξ
    intro M _ _ _ _ ζ _
    exact hcyc Q GQ C.index eQ (isSimplyConnectedFieldExtension F Q G hsc)
      (hAbs.baseChange_of_algebraicExtension (K := Q)) hqs hDQ hnoQ heQ M ζ
  exact ξ.isTrivial_of_trialitarian_quadratic_quasiSplit d e hsc hAbs hD hno
    Langlands.CentralSimple.numberFieldReducedNormLocality Q hdeg hqs hξ hsplit

end Langlands.GroupScheme
