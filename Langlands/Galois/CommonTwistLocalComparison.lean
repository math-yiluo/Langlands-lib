import Langlands.Galois.CyclotomicTwist
import Langlands.Galois.FrobeniusCharacter
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Weil.Representation.AbsoluteIrreducibility

/-! # Local comparison after a common twist -/

noncomputable section

universe uK uL uM uN uE uV uW uX uY

namespace Langlands.GaloisRepresentation

open Langlands.Global Filter

/-- Two separate Euler comparisons with equivalent auxiliary restrictions give an
actual equivalence on the original coefficient field after cancelling a common twist. -/
def CommonTwistLocalComparisonStatement : Prop :=
  ∀ {K : Type uK} [Field K] [NumberField K]
    {L : Type uL} [Field L] [TopologicalSpace L] [IsTopologicalRing L]
    {M : Type uM} [Field M] [TopologicalSpace M] [IsTopologicalRing M]
    {N : Type uN} [Field N] [TopologicalSpace N] [IsTopologicalRing N]
    {E : Type uE} [Field E] [TopologicalSpace E] [T2Space E] [IsAlgClosed E]
    (v : FinitePlace K) (A : Objects.{uK, uL, uV} K L) (B : Objects.{uK, uL, uW} K L)
    (C : Objects.{uK, uM, uX} K M) (D : Objects.{uK, uN, uY} K N)
    (χ : Field.absoluteGaloisGroup K →* Lˣ) (hχ : Continuous fun g => (χ g : L))
    (i : L →+* E) (j : M →+* E) (k : N →+* E),
    Continuous i → Continuous j → Continuous k →
    (∀ᶠ w : FinitePlace K in Filter.cofinite,
      (frobeniusEulerPolynomial C w).map j = (frobeniusEulerPolynomial (twist χ hχ A) w).map i) →
    (∀ᶠ w : FinitePlace K in Filter.cofinite,
      (frobeniusEulerPolynomial D w).map k = (frobeniusEulerPolynomial (twist χ hχ B) w).map i) →
    C.val.rank = A.val.rank → D.val.rank = B.val.rank →
    (atFinitePlace v C).val.IsAbsolutelyIrreducible →
    (letI : Algebra M E := j.toAlgebra;
      letI : Algebra N E := k.toAlgebra;
      Nonempty (FiniteRepresentation.Equiv ((atFinitePlace v C).val.extendCoefficients E)
        ((atFinitePlace v D).val.extendCoefficients E))) →
    Nonempty (FiniteRepresentation.Equiv (atFinitePlace v A).val (atFinitePlace v B).val)

/-- A cofinite comparison supplies the finite exceptional set for character comparison. -/
private theorem exists_finset_of_eventually_cofinite {α : Type*} {p : α → Prop}
    (h : ∀ᶠ a in Filter.cofinite, p a) : ∃ S : Finset α, ∀ a ∉ S, p a := by
  classical
  have hf := Filter.eventually_cofinite.mp h
  refine ⟨hf.toFinset, fun a ha => ?_⟩
  by_contra hna
  exact ha (hf.mem_toFinset.mpr hna)

theorem localEquiv_of_commonTwist_of_canonicalComparison :
    CommonTwistLocalComparisonStatement.{uK, uL, uM, uN, uE, uV, uW, uX, uY} := by
  intro K _ _ L _ _ _ M _ _ _ N _ _ _ E _ _ _ _ v A B C D χ hχ i j k hi hj hk hS hT hCA hDB hC hCD
  obtain ⟨S, hS⟩ := exists_finset_of_eventually_cofinite hS
  obtain ⟨T, hT⟩ := exists_finset_of_eventually_cofinite hT
  let : Algebra L E := i.toAlgebra
  let : Algebra M E := j.toAlgebra
  let : Algebra N E := k.toAlgebra
  obtain ⟨eCD⟩ := hCD
  have hCext := hC.extendCoefficients E
  have hDext := (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv eCD).mp hCext
  obtain ⟨eCA⟩ := localEquiv_extendCoefficients_of_frobeniusEulerPolynomial_map_eq
    C (twist χ hχ A) j i hj hi S (fun w hw _ => hS w hw) v hCA hCext
  obtain ⟨eDB⟩ := localEquiv_extendCoefficients_of_frobeniusEulerPolynomial_map_eq
    D (twist χ hχ B) k i hk hi T (fun w hw _ => hT w hw) v hDB hDext
  have hAext := (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv eCA).mp hCext
  have hA := FiniteRepresentation.irreducible_of_extendCoefficients E _ hAext
  obtain ⟨eAB⟩ := FiniteRepresentation.nonempty_equiv_of_extendCoefficients E _ _ hA
    ⟨eCA.symm.trans (eCD.trans eDB)⟩
  exact ⟨untwistAtFinitePlaceEquiv χ hχ A v eAB⟩

end Langlands.GaloisRepresentation
