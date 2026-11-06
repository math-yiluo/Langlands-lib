import Langlands.Geometry.Analytic.StrictTestDomain.IdealCoverRefinement
import Langlands.Geometry.Analytic.StrictTestDomain.LaurentSplitIdealDescent
import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalGluingPreparation
import Langlands.Geometry.Analytic.StrictTestDomain.ScalarCoverDescentTransport
import Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalRefinementProof
import Mathlib.Data.Fintype.Card

/-! # Strict rational ideal descent from Laurent and all-unit covers -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K}

/-- The binary Laurent ideal input, uniformly for actual strict base algebras. -/
def LaurentIdealDescentInput (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop :=
  ∀ (P : PresentedStrictAffinoidAlgebra K) (f : P),
    BinaryIdealDescent (laurentUpper f) (laurentLower f)

/-- The all-unit standard rational ideal input, uniformly for actual strict
base algebras, including the empty tuple. -/
def AllUnitIdealDescentInput (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop :=
  ∀ (P : PresentedStrictAffinoidAlgebra K) (n : ℕ) (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0),
    (∀ i, IsUnit (f i)) → IdealCoverDescent (standardRational f hf)

private def idealNonunitCount {n : ℕ} (f : Fin n → P) : ℕ := by
  classical
  exact Fintype.card {i : Fin n // ¬ IsUnit (f i)}

omit [CompleteSpace K] in
private theorem idealNonunitCount_map_reindex_lt {n : ℕ} (f : Fin n → P)
    (e : Fin n ≃ Fin n) (φ : BoundedAlgHom K P Q) (j : Fin n)
    (hj : ¬ IsUnit (f (e j))) (hunit : IsUnit (φ (f (e j)))) :
    idealNonunitCount (fun i => φ (f (e i))) < idealNonunitCount f := by
  classical
  let t : {i : Fin n // ¬ IsUnit (φ (f (e i)))} → {i : Fin n // ¬ IsUnit (f i)} :=
    fun i => ⟨e i.val, fun h => i.property (h.map φ.toAlgHom.toMonoidHom)⟩
  have ht : Function.Injective t := by
    intro a b hab
    exact Subtype.ext (e.injective (congrArg Subtype.val hab))
  have hmiss : (⟨e j, hj⟩ : {i : Fin n // ¬ IsUnit (f i)}) ∉ Set.range t := by
    rintro ⟨a, ha⟩
    have haj : a.val = j := e.injective (congrArg Subtype.val ha)
    exact a.property (by simpa only [haj] using hunit)
  exact Fintype.card_lt_of_injective_of_notMem t ht hmiss

/-- Every strict standard rational point cover has effective ideals provided
the binary Laurent and all-unit standard inputs hold. -/
theorem idealCoverDescent_standard_of_inputs (hK : ∃ c : K, 1 < ‖c‖)
    (hbin : LaurentIdealDescentInput K) (hunits : AllUnitIdealDescentInput K) :
    ∀ n (P : PresentedStrictAffinoidAlgebra K) (f : Fin n → P)
      (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0),
      IdealCoverDescent (standardRational f hf) := by
  classical
  intro n
  induction n with
  | zero =>
      intro P f hf I hI i
      exact Fin.elim0 i
  | succ n ihn =>
      have hk : ∀ k (P : PresentedStrictAffinoidAlgebra K) (f : Fin (n + 1) → P)
          (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0),
          idealNonunitCount f = k → IdealCoverDescent (standardRational f hf) := by
        intro k
        induction k using Nat.strong_induction_on with
        | h k ihk =>
            intro P f hf hcount
            by_cases hu : ∀ j, IsUnit (f j)
            · exact hunits P (n + 1) f hf hu
            · obtain ⟨i, hi⟩ := not_forall.mp hu
              let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap (Fin.last n) i
              let f' : Fin (n + 1) → P := fun j => f (e j)
              have hf' : ∀ x : BanachSpectrum P, ∃ j, x (f' j) ≠ 0 :=
                tuple_no_common_zero_reindex f hf e
              apply IdealCoverDescent.of_refinement hK (standardRational f hf)
                (standardRational f' hf') (standardRational_covers f' hf') e
                (fun j => ⟨(standardRational_locus_reindex f hf e hf' j).le⟩)
              let threshold := scalarUniformThreshold hK f' hf'
              let c : K := threshold.val
              have hc : c ≠ 0 := threshold.property.1
              have hthreshold : ∀ x : BanachSpectrum P, ∃ j, ‖c‖ < x (f' j) :=
                threshold.property.2
              let U := StandardRationalLaurentReduction.upper f' c
              let L := StandardRationalLaurentReduction.lower f' c
              have hchosen : ¬ IsUnit (f (e (Fin.last n))) := by
                simpa only [e, Equiv.swap_apply_left] using hi
              have hU : IdealCoverDescent
                  (fun j => (standardRational f' hf' j).pullback U.baseMap) := by
                let g := StandardRationalLaurentReduction.shortened f' c
                have hg := StandardRationalLaurentReduction.shortened_no_common_zero
                  f' c hc hthreshold
                apply IdealCoverDescent.of_refinement hK
                  (fun j => (standardRational f' hf' j).pullback U.baseMap)
                  (standardRational g hg) (standardRational_covers g hg)
                  (fun j => j.castSucc)
                  (fun j => ⟨(StandardRationalLaurentReduction.shortStandard_locus
                    f' c hc hthreshold hf' j).symm.le⟩)
                exact ihn U.algebra g hg
              have hLcount : idealNonunitCount (fun j => L.baseMap (f' j)) < k := by
                rw [← hcount]
                exact idealNonunitCount_map_reindex_lt f e L.baseMap (Fin.last n) hchosen
                  (StandardRationalLaurentReduction.lower_last_isUnit f' c)
              have hL : IdealCoverDescent
                  (fun j => (standardRational f' hf' j).pullback L.baseMap) :=
                ihk _ hLcount L.algebra (fun j => L.baseMap (f' j))
                  (tuple_no_common_zero_pullback f' hf' L.baseMap) rfl
              exact laurentSplitIdealDescent hK (standardRational f' hf')
                (standardRational_covers f' hf')
                (StandardRationalLaurentReduction.scalarFunction f' c)
                (hbin P _) hU hL
      intro P f hf
      exact hk (idealNonunitCount f) P f hf rfl

/-- A finite rational cover reduces to a standard rational point refinement,
retaining every original actual ideal and its explicit global contraction. -/
theorem idealCoverDescent_finiteRational_of_inputs (hK : ∃ c : K, 1 < ‖c‖)
    (hbin : LaurentIdealDescentInput K) (hunits : AllUnitIdealDescentInput K)
    {n : ℕ} (D : Fin n → RationalData K P)
    (hD : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) : IdealCoverDescent D := by
  classical
  obtain ⟨m, f, hf, href⟩ := finiteRationalRefinement K P (ULift.{u} (Fin n))
    (fun i => D i.down) (by
      intro x
      obtain ⟨i, hi⟩ := hD x
      exact ⟨ULift.up i, hi⟩)
  choose k hk using href
  exact IdealCoverDescent.of_refinement hK D (standardRational f hf)
    (standardRational_covers f hf) (fun j => (k j).down) (fun j => ⟨hk j⟩)
    (idealCoverDescent_standard_of_inputs hK hbin hunits m P f hf)

end Langlands.Analytic.StrictTestDomain
