import Langlands.Algebra.NumberFieldRelativeBrauerProfiles
import Langlands.Algebra.NumberFieldBrauerFiniteSupport
import Langlands.Algebra.BrauerComparison.PeriodDegree
import Langlands.Algebra.DivisionSplittingDegree
import Langlands.Algebra.LocalReducedCharpolyNeighborhood
import Langlands.ClassFieldTheory.Local.LocalDivisionSplittingDegree
import Langlands.ClassFieldTheory.Local.BrauerLocalInvariant
import Langlands.Global.FiniteCompletionLocalField

/-! # Degree bounds for central simple representatives of number-field profiles -/

noncomputable section

universe u

namespace Langlands.Brauer

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local Langlands.LocalField
open Langlands.BrauerComparison Langlands.CentralSimple Langlands.CentralDivision
open scoped FiniteExtension TensorProduct WithZero

section Representatives

variable {F T : Type u} [Field F] [Field T] [Algebra F T] [FiniteDimensional F T]

/-- A splitting extension of degree `n` gives a degree-`n` representative
of the same Brauer class. -/
theorem exists_csa_finrank_of_splitting_field (A : CSA.{u, u} F) {n : ℕ} (hn : 0 < n)
    (hT : Module.finrank F T = n) (hsl : IsSplit (baseChange T A)) :
    ∃ B : CSA.{u, u} F, Module.finrank F B = n * n ∧ classOf B = classOf A := by
  have := IsArtinianRing.of_finite F A
  obtain ⟨r, hr, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A
  let : NeZero r := hr
  let : Algebra.IsCentral F D := isCentral_of_algEquiv_matrix e
  let C := divisionAlgebraCSA F D
  have hC : classOf A = classOf C :=
    (classOf_eq_of_algEquiv (B := matrix C r) e).trans (classOf_matrix C r)
  have hslC : IsSplit (baseChange T C) := by
    apply (classOf_eq_zero_iff _).mp
    rw [← scalarExtension_classOf, ← hC, scalarExtension_classOf]
    exact (classOf_eq_zero_iff _).mpr hsl
  obtain ⟨d, hd, ⟨eD⟩⟩ := hslC
  let e' : T ⊗[F] D ≃ₐ[T] Matrix (Fin d) (Fin d) T := eD
  have hdvd : d ∣ n := hT ▸ division_splitting_size_dvd_field_degree hd e'
  have hdim : Module.finrank F D = d * d := finrank_eq_matrix_size F D T d e'
  obtain ⟨m, hm⟩ := hdvd
  have hm₀ : m ≠ 0 := by
    intro h
    simp [h, hn.ne'] at hm
  let : NeZero m := ⟨hm₀⟩
  refine ⟨matrix C m, ?_, (classOf_matrix C m).trans hC.symm⟩
  change Module.finrank F (Matrix (Fin m) (Fin m) D) = n * n
  rw [Module.finrank_matrix, Fintype.card_fin, hdim, hm]
  ac_rfl

end Representatives

section NumberFields

variable {F : Type u} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem exists_splitting_field_of_local_exponent
    (S : Finset (Langlands.Global.FinitePlace F)) (A : CSA.{u, u} F)
    {n : ℕ} (hn : 0 < n)
    (hA : ∀ v ∈ S, n • classOf (baseChange (FiniteCompletion F v) A) = 0)
    (hS : ∀ v ∉ S, IsSplit (baseChange (FiniteCompletion F v) A)) :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra F T) (_ : FiniteDimensional F T),
      Module.finrank F T = n ∧ IsSplit (baseChange T A) := by
  classical
  obtain ⟨T, _, _, _, hd, hloc⟩ := exists_numberFieldExtension_exactLocalDegree S hn
  let : IsTotallyComplex T := isTotallyComplex_of_algebra F T
  refine ⟨T, inferInstance, inferInstance, inferInstance, hd, ?_⟩
  apply numberFieldBrauerSplitting T (baseChange T A)
  · intro w
    let v := placeBelow F w
    let : w.asIdeal.LiesOver v.asIdeal := liesOver_placeBelow F w
    let K := FiniteCompletion F v
    let M := FiniteCompletion T w
    have hsl : IsSplit (baseChange M (baseChange K A)) := by
      by_cases hv : v ∈ S
      · let : ValuativeRel K := FiniteCompletion.valuativeRel v
        let : ValuativeRel M := FiniteCompletion.valuativeRel w
        let : IsNonarchimedeanLocalField K := FiniteCompletion.isNonarchimedeanLocalField v
        let : IsNonarchimedeanLocalField M := FiniteCompletion.isNonarchimedeanLocalField w
        let : FiniteDimensional K M := FiniteExtension.local_finite v w
        let : ValuativeExtension K M := ⟨by
          intro a b
          rw [FiniteCompletion.valuativeRel_vle, FiniteCompletion.valuativeRel_vle]
          change Valued.v (FiniteExtension.completionMap v w a) ≤
            Valued.v (FiniteExtension.completionMap v w b) ↔ Valued.v a ≤ Valued.v b
          rw [FiniteExtension.valuation_completionMap, FiniteExtension.valuation_completionMap]
          exact pow_le_pow_iff_left₀ zero_le zero_le
            (w.asIdeal.ramificationIdx_pos (𝓞 F)).ne'⟩
        apply (classOf_eq_zero_iff _).mp
        apply (localBrauerInvariant M).injective
        rw [map_zero, ← scalarExtension_classOf,
          localBrauerInvariant_scalarExtension K M (FiniteExtension.continuous_completionMap v w),
          hloc v hv w, ← map_nsmul, hA v hv, map_zero]
      · exact (hS v hv).baseChange M
    obtain ⟨d, hd, ⟨e⟩⟩ := hsl
    exact ⟨d, hd, ⟨(baseChangeTowerEquiv T M A).trans
      ((baseChangeTowerEquiv K M A).symm.trans e)⟩⟩
  · intro w
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    let : IsAlgClosed w.Completion := ⟨fun f => Polynomial.Splits.of_splits_map
      e.toRingHom (IsAlgClosed.splits _) (fun x _ => e.surjective x)⟩
    exact isSplit_of_isAlgClosed (baseChange w.Completion (baseChange T A))

end NumberFields

/-- The reduced degree of a central division algebra over a totally complex
number field equals the additive order of its Brauer class. -/
def NumberFieldTotallyComplexBrauerPeriodIndexStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [IsTotallyComplex F]
    [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D],
    addOrderOf (classOf (divisionAlgebraCSA F D)) = reducedDegree F D

/-- Prescribe local splitting degrees equal to the Brauer period, then use
divisibility of the degree of a division-algebra splitting field. -/
theorem numberFieldTotallyComplexBrauerPeriodIndex :
    NumberFieldTotallyComplexBrauerPeriodIndexStatement.{u} := by
  intro F D _ _ _ _ _ _ _
  classical
  let A := divisionAlgebraCSA F D
  let n := addOrderOf (classOf A)
  have hperiod : n ∣ reducedDegree F D := addOrderOf_classOf_dvd_reducedDegree A
  have hn : 0 < n := Nat.pos_of_dvd_of_pos hperiod (reducedDegree_pos F D)
  let S := (finite_nonsplitFinitePlaces A).toFinset
  obtain ⟨T, _, _, _, hT, d, hd, ⟨e⟩⟩ :=
    exists_splitting_field_of_local_exponent S A hn
      (fun v _ => by
        rw [← scalarExtension_classOf, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero])
      (fun v hv => by
        have hv' : v ∉ nonsplitFinitePlaces A := by
          simpa only [S, Set.Finite.mem_toFinset] using hv
        exact Classical.not_not.mp hv')
  let e' : T ⊗[F] D ≃ₐ[T] Matrix (Fin d) (Fin d) T := e
  have hD : d ∣ Module.finrank F T := division_splitting_size_dvd_field_degree hd e'
  rw [matrix_size_eq_reducedDegree F D T d e', hT] at hD
  exact Nat.dvd_antisymm hperiod hD

/-- Over a totally complex number field, a zero-sum profile killed by `n`
is realized by a degree-`n` CSA with the specified relative invariants. -/
def NumberFieldBrauerProfileDegreeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F]
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p),
    (∀ (p : ℕ) [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
    ∀ (S : Finset (Langlands.Global.FinitePlace F)) (a : Langlands.Global.FinitePlace F →
      RationalModIntegers), (∀ v ∉ S, a v = 0) →
    ∀ (n : ℕ), 0 < n → (∀ v ∈ S, n • a v = 0) → (∑ v ∈ S, a v = 0) →
      ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L) (_ : IsGalois F L)
        (B : CSA.{u, u} F)
        (f : L ⊗[F] B ≃ₐ[L] Matrix (Fin (reducedDegree F B)) (Fin (reducedDegree F B)) L),
        Module.finrank F B = n * n ∧
        ∀ v : Langlands.Global.FinitePlace F,
          finiteRelativeBrauerInvariant I f v (placeAbove L v).val = a v

theorem exists_csa_degree_with_finiteRelativeInvariants : NumberFieldBrauerProfileDegreeStatement.{u} := by
  intro F _ _ _ I hCF S a ha₀ n hn ha hsum
  obtain ⟨L, _, _, _, _, A, e, he⟩ :=
    exists_csa_with_finiteRelativeInvariants_of_exponent I hCF S a ha₀ hn ha hsum
  have hI (p : ℕ) [Fact p.Prime] : (I p).RelativeImages := (hCF p).1.2.1
  have hA (v : Langlands.Global.FinitePlace F) (hv : v ∈ S) :
      n • classOf (baseChange (FiniteCompletion F v) A) = 0 :=
    nsmul_classOf_baseChange_eq_zero_of_finiteRelativeBrauerInvariant I e v (placeAbove L v).val
      hI n (by rw [he v]; exact ha v hv)
  have hS (v : Langlands.Global.FinitePlace F) (hv : v ∉ S) :
      IsSplit (baseChange (FiniteCompletion F v) A) := by
    apply (classOf_eq_zero_iff _).mp
    have h := nsmul_classOf_baseChange_eq_zero_of_finiteRelativeBrauerInvariant
      I e v (placeAbove L v).val hI 1 (by rw [he v, ha₀ v hv, smul_zero])
    simpa only [one_nsmul] using h
  obtain ⟨T, _, _, _, hT, hsplitT⟩ := exists_splitting_field_of_local_exponent S A hn hA hS
  obtain ⟨B, hd, hclass⟩ := exists_csa_finrank_of_splitting_field A hn hT hsplitT
  have hsplitL : IsSplit (baseChange L B) := by
    apply (classOf_eq_zero_iff _).mp
    rw [← scalarExtension_classOf, hclass, scalarExtension_classOf]
    exact (classOf_eq_zero_iff _).mpr
      ⟨reducedDegree F A, reducedDegree_pos F A, ⟨e⟩⟩
  obtain ⟨d, hd', ⟨f₀⟩⟩ := hsplitL
  let f : L ⊗[F] B ≃ₐ[L] Matrix (Fin (reducedDegree F B)) (Fin (reducedDegree F B)) L :=
    f₀.trans (Matrix.reindexAlgEquiv L L
      (finCongr (matrix_size_eq_reducedDegree F B L d f₀)))
  let : Nonempty (Fin (reducedDegree F A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  let : Nonempty (Fin (reducedDegree F B)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F B)
  have hrel : relativeClass f = relativeClass e :=
    relativeClass_eq_of_brauerEquivalent ((classOf_eq_iff B A).mp hclass) f e
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, B, f, hd, fun v => ?_⟩
  rw [finiteRelativeBrauerInvariant_eq, hrel, ← finiteRelativeBrauerInvariant_eq]
  exact he v

end Langlands.Brauer
