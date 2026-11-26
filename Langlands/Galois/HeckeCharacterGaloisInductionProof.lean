import Langlands.Galois.HeckeCharacterGaloisInductionStatement
import Langlands.Galois.HeckeInduction.GoodPlace
import Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness
import Langlands.Global.HeckeCharacterUnramifiedNorm

/-!
# Galois induction of a compatible family of rank-one realizations

Proof of `Langlands.GaloisRepresentation.HeckeCharacterGaloisInductionStatement`: each member of
the family is the finite-index induction `HeckeInduction.inducedObject`, the exceptional set
collects the base places below the exceptional set of the rank-one family and the places ramified
in `E` or in its normal closure, and the Euler polynomials come from
`HeckeInduction.hasEulerPolynomialAt_inducedObject`.
-/

noncomputable section

universe uK uE uL

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.Unramified.WeakInduction Polynomial
open Langlands.GaloisRepresentation.HeckeInduction
open scoped NumberField

/-- Residue characteristics agree for a prime lying over another. -/
theorem residueCharacteristic_eq_of_liesOver {K : Type uK} {E : Type uE} [Field K] [Field E]
    [NumberField K] [NumberField E] [Algebra K E] (v : FinitePlace K) (w : FinitePlace E)
    [w.asIdeal.LiesOver v.asIdeal] :
    residueCharacteristic w = residueCharacteristic v := by
  have := v.isMaximal
  have := w.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  exact (Algebra.ringChar_eq (NumberField.RingOfIntegers K ⧸ v.asIdeal)
    (NumberField.RingOfIntegers E ⧸ w.asIdeal)).symm

/-- **Galois induction of a compatible rank-one family** (Harris 1998, Lemma 1.6). -/
theorem heckeCharacterGaloisInduction : HeckeCharacterGaloisInductionStatement.{uK, uE, uL} := by
  intro K E L _ _ _ _ _ _ _ e ι χ ψ hcompat
  classical
  obtain ⟨SE, hSE⟩ := hcompat
  let a : FinitePlace E → L := fun w => if h : w ∉ SE then (hSE w h).2.choose else 0
  have ha (w : FinitePlace E) (h : w ∉ SE) : (hSE w h).2.choose = a w := by
    simp only [a, h, not_false_eq_true, ↓reduceDIte]
  let M := normalClosureField (K := K) (E := E)
  let : NumberField M := NumberField.of_module_finite K M
  let S : Finset (FinitePlace K) :=
    SE.image (fun w => w.under (𝓞 K)) ∪
      (ClassFieldTheory.Global.Artin.finite_setOf_ramified K E).toFinset ∪
      (ClassFieldTheory.Global.Artin.finite_setOf_ramified K M).toFinset
  let P : FinitePlace K → L[X] := fun v =>
    ∏ w : FinitePlacesAbove E v, (1 - C (a w.1) * X ^ w.1.asIdeal.inertiaDeg (𝓞 K))
  have hgood : ∀ v ∉ S, (∀ w : FinitePlacesAbove E v, w.1 ∉ SE) ∧
      (∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1) ∧
      Algebra.IsUnramifiedAt (𝓞 K) (inducedPlace v M).asIdeal := by
    intro v hv
    refine ⟨fun w hw => hv (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨w.1, hw, finitePlacesAbove_under v w⟩))), fun w => ?_, ?_⟩
    · have hu : Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := by
        by_contra hn
        exact hv (Finset.mem_union_left _ (Finset.mem_union_right _
          ((Set.Finite.mem_toFinset _).mpr ⟨w.1, w.2, hn⟩)))
      exact Ideal.ramificationIdx_eq_one w.1.asIdeal (𝓞 K)
    · by_contra hn
      exact hv (Finset.mem_union_right _
        ((Set.Finite.mem_toFinset _).mpr ⟨inducedPlace v M, inducedPlace_liesOver v M, hn⟩))
  refine ⟨fun lam => inducedObject e (ψ lam.val), S, P, ?_, ?_, ?_, ?_⟩
  · intro lam
    exact ⟨inferInstance, descended e (ψ lam), descendedCharacter_comp_rangeRestrict e _,
      ⟨Representation.Equiv.refl _⟩⟩
  · intro lam
    exact inducedObject_rank e (ψ lam.val)
  · intro lam v hv hchar
    obtain ⟨hSEv, hram, hM⟩ := hgood v hv
    have hcharw (w : FinitePlacesAbove E v) :
        residueCharacteristic w.1 ≠ residueCharacteristic lam.val := by
      rw [residueCharacteristic_eq_of_liesOver v w.1]
      exact hchar
    have hψ (w : FinitePlacesAbove E v) :=
      (hSE w.1 (hSEv w)).2.choose_spec.2 lam.val (hcharw w)
    have hP : (P v).map (NumberField.FinitePlace.embedding lam.val) =
        ∏ w : FinitePlacesAbove E v, (1 - C (NumberField.FinitePlace.embedding lam.val (a w.1)) *
          X ^ w.1.asIdeal.inertiaDeg (𝓞 K)) := by
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rw [hP]
    apply hasEulerPolynomialAt_inducedObject e (ψ lam.val) v hram hM
    · intro w x hx
      exact (hψ w).1 ⟨x, hx⟩
    · intro w x hx
      rw [← ha w.1 (hSEv w)]
      exact (hψ w).2 x hx
  · unfold MatchesHeckeInductionEulerPolynomials
    rw [Filter.eventually_cofinite]
    refine S.finite_toSet.subset fun v hv => ?_
    by_contra hvS
    apply hv
    obtain ⟨hSEv, hram, -⟩ := hgood v hvS
    refine ⟨fun w => ⟨hram w, (hSE w.1 (hSEv w)).1⟩, fun ϖ hϖ => ?_⟩
    simp only [P, inducedEulerPolynomial, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X]
    refine Finset.prod_congr rfl fun w _ => ?_
    obtain ⟨ϖ', hϖ', hχ⟩ := (hSE w.1 (hSEv w)).2.choose_spec.1
    rw [← ha w.1 (hSEv w), ← hχ, HeckeCharacter.finiteComponent_eq_of_valued_eq χ
      (hSE w.1 (hSEv w)).1 (hϖ'.trans (hϖ w).symm)]

end Langlands.GaloisRepresentation
