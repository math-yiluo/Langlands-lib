import Langlands.Geometry.Analytic.StrictTestDomain.NontrivialStandardRationalGluingStatement
import Langlands.Geometry.Analytic.StrictTestDomain.AllUnitStandardRationalGluingProof
import Langlands.Geometry.Analytic.StrictTestDomain.LaurentSplitScalarDescentProof
import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalGluingPreparation
import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalLaurentReduction
import Mathlib.Data.Fintype.Card

/-! # Nontrivial-scalar standard rational descent -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K}

private def nonunitCount {n : ℕ} (f : Fin n → P) : ℕ := by
  classical
  exact Fintype.card {i : Fin n // ¬ IsUnit (f i)}

omit [CompleteSpace K] in
private theorem nonunitCount_map_reindex_lt {n : ℕ} (f : Fin n → P)
    (e : Fin n ≃ Fin n) (φ : BoundedAlgHom K P Q) (j : Fin n)
    (hj : ¬ IsUnit (f (e j))) (hunit : IsUnit (φ (f (e j)))) :
    nonunitCount (fun i => φ (f (e i))) < nonunitCount f := by
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

private theorem standard_descent (hK : ∃ c : K, 1 < ‖c‖) :
    ∀ n (P : PresentedStrictAffinoidAlgebra K) (f : Fin n → P)
      (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0),
      ScalarCoverDescent (standardRational f hf) := by
  classical
  intro n
  induction n with
  | zero =>
      intro P f hf s _
      exact existsUnique_standard_gluing_empty f hf s
  | succ n ihn =>
      have hk : ∀ k (P : PresentedStrictAffinoidAlgebra K) (f : Fin (n+1) → P)
          (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0),
          nonunitCount f = k → ScalarCoverDescent (standardRational f hf) := by
        intro k
        induction k using Nat.strong_induction_on with
        | h k ihk =>
            intro P f hf hcount
            by_cases hu : ∀ j, IsUnit (f j)
            · exact allUnitStandardRationalGluing K P (n+1) f hf hu
            · obtain ⟨i, hi⟩ := not_forall.mp hu
              let e : Fin (n+1) ≃ Fin (n+1) := Equiv.swap (Fin.last n) i
              let f' : Fin (n+1) → P := fun j => f (e j)
              have hf' : ∀ x : BanachSpectrum P, ∃ j, x (f' j) ≠ 0 :=
                tuple_no_common_zero_reindex f hf e
              apply (ScalarCoverDescent.standard_reindex_iff f hf e hf').mp
              let threshold := scalarUniformThreshold hK f' hf'
              let c : K := threshold.val
              have hc : c ≠ 0 := threshold.property.1
              have hthreshold : ∀ x : BanachSpectrum P, ∃ j, ‖c‖ < x (f' j) :=
                threshold.property.2
              let U := StandardRationalLaurentReduction.upper f' c
              let L := StandardRationalLaurentReduction.lower f' c
              let O := StandardRationalLaurentReduction.overlap f' c
              have hchosen : ¬ IsUnit (f (e (Fin.last n))) := by
                simpa only [e, Equiv.swap_apply_left] using hi
              have hU :
                  ScalarCoverDescent (fun j => (standardRational f' hf' j).pullback U.baseMap) := by
                apply ScalarCoverDescent.of_castSucc_locus_empty
                  (fun j => (standardRational f' hf' j).pullback U.baseMap)
                  (StandardRationalLaurentReduction.last_pullback_locus_empty
                    f' c hc hthreshold hf')
                exact (ihn U.algebra
                  (StandardRationalLaurentReduction.shortened f' c)
                  (StandardRationalLaurentReduction.shortened_no_common_zero
                    f' c hc hthreshold)).of_locus_eq
                  (fun j => (StandardRationalLaurentReduction.shortStandard_locus
                    f' c hc hthreshold hf' j).symm)
              have hLcount : nonunitCount (fun j => L.baseMap (f' j)) < k := by
                rw [← hcount]
                exact nonunitCount_map_reindex_lt f e L.baseMap (Fin.last n) hchosen
                  (StandardRationalLaurentReduction.lower_last_isUnit f' c)
              have hL :
                  ScalarCoverDescent (fun j => (standardRational f' hf' j).pullback L.baseMap) :=
                ihk _ hLcount L.algebra (fun j => L.baseMap (f' j))
                  (tuple_no_common_zero_pullback f' hf' L.baseMap) rfl
              have hOcount : nonunitCount (fun j => O.baseMap (f' j)) < k := by
                rw [← hcount]
                exact nonunitCount_map_reindex_lt f e O.baseMap (Fin.last n) hchosen
                  (StandardRationalLaurentReduction.overlap_last_isUnit f' c)
              have hO :
                  ScalarCoverDescent (fun j => (standardRational f' hf' j).pullback O.baseMap) :=
                ihk _ hOcount O.algebra (fun j => O.baseMap (f' j))
                  (tuple_no_common_zero_pullback f' hf' O.baseMap) rfl
              exact laurentSplitScalarDescent K P (Fin (n+1)) (standardRational f' hf')
                (StandardRationalLaurentReduction.scalarFunction f' c) hU hL hO.separated
      intro P f hf
      exact hk (nonunitCount f) P f hf rfl

/-- Compatible scalar sections of the actual standard rational cover uniquely
descend over every complete nontrivially valued ultrametric normed field. -/
theorem nontrivialStandardRationalGluing :
    NontrivialStandardRationalGluingStatement.{u} := by
  intro K _ _ _ hK P n f hf
  exact standard_descent hK n P f hf

end Langlands.Analytic.StrictTestDomain
