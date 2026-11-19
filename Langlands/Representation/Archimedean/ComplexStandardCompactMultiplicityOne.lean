import Mathlib.Data.Fin.Tuple.Sort
import Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof
import Langlands.Representation.Archimedean.ComplexPermutationKMap

/-!
# A compact multiplicity-one vector in complex standard modules

Use the minor-monomial construction for the sorted list of weights, and transport the
vector by the equivalence of the two compact models.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean ComplexPermutation ComplexTemperedIrreducible
  ComplexStrictLanglandsQuotient

private theorem exists_vector_of_sortedWeights (n : ℕ) (ds : List ComplexCharacterData)
    (hlen : ds.length = n)
    (hmono : ∀ i, i + 1 < n → complexPositionWeight ds i ≤ complexPositionWeight ds (i + 1)) :
    ∃ f : KF n ds, f ≠ 0 ∧
      ∀ E : Module.End ℂ (KF n ds),
        (∀ k x, E (complexStandardRep n ds k x) = complexStandardRep n ds k (E x)) →
        ∃ c : ℂ, E f = c • f := by
  obtain ⟨powers, detPower, hweights⟩ := exists_minorWeight_eq n (complexPositionWeight ds) hmono
  have hchar (i : Fin n) (z : ℂˣ) :
      complexPositionCharacter ds i z =
        (z : ℂ) ^ ComplexMinorProduct.minorWeight powers detPower i *
          complexPositionCharacter (untwist ds) i z := by
    rw [hweights i]
    exact positionCharacter_untwist ds i (by simpa only [hlen] using i.isLt) z
  obtain ⟨T, hT, hT₁⟩ :=
    ComplexSphericalLieGroup.exists_spherical (n := n) (weight_untwist (ds := ds))
  have hTK (k : Matrix.unitaryGroup (Fin n) ℂ) :
      (T : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) = 1 := by
    have h := congrArg (kFiniteEval (complexStandardModule n (untwist ds)) 1) (hT k)
    simpa only [kFiniteEval_apply, complexStandardRep_apply_apply, one_mul, hT₁] using h
  let f : KF n ds := ComplexMinorProduct.mulV powers detPower hchar T
  have hf (k : Matrix.unitaryGroup (Fin n) ℂ) :
      (f : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) =
        ComplexLowestKType.minorMonomial powers detPower (k : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [f, ComplexMinorProduct.mulV_coe, hTK, mul_one]
    rfl
  refine ⟨f, ?_, complexLowestKTypeMultOne n ds powers detPower f hf⟩
  intro h
  have heval := hf (ComplexMinorProduct.revUnitary n)
  rw [h] at heval
  exact ComplexMinorProduct.minorMonomial_revUnitary_ne_zero powers detPower heval.symm

/-- A complex standard module with `n` characters has a nonzero vector that every
`U(n)`-equivariant linear endomorphism sends to a scalar multiple of itself. -/
theorem complexStandardExistsCompactScalarVector (n : ℕ) (ds : List ComplexCharacterData)
    (hlen : ds.length = n) :
    ∃ f : KF n ds, f ≠ 0 ∧
      ∀ E : Module.End ℂ (KF n ds),
        (∀ k x, E (complexStandardRep n ds k x) = complexStandardRep n ds k (E x)) →
        ∃ c : ℂ, E f = c • f := by
  let dataAt (i : Fin n) := ds.get (Fin.cast hlen.symm i)
  have hds : List.ofFn dataAt = ds := ofFn_get_eq ds hlen
  rw [← hds]
  let sort := Tuple.sort (fun i => (dataAt i).weight)
  let sorted (i : Fin n) := dataAt (sort i)
  have hlenSorted : (List.ofFn sorted).length = n := List.length_ofFn
  have hmono : Monotone (fun i => (sorted i).weight) :=
    Tuple.monotone_sort (fun i => (dataAt i).weight)
  obtain ⟨f, hf₀, hf⟩ := exists_vector_of_sortedWeights n (List.ofFn sorted) hlenSorted
    (fun i hi => by
      rw [positionWeight_eq _ i (by omega), positionWeight_eq _ (i + 1) (by omega)]
      simp only [List.getElem_ofFn]
      exact hmono (show (⟨i, by omega⟩ : Fin n) ≤ ⟨i + 1, hi⟩ from Nat.le_succ i))
  have hrestore : List.ofFn (fun i => sorted (sort.symm i)) = List.ofFn dataAt := by
    simp [sorted]
  obtain ⟨G, hG, hGinj⟩ :
      ∃ G : KF n (List.ofFn sorted) →ₗ[ℂ] KF n (List.ofFn dataAt),
        (∀ k x, G (complexStandardRep n (List.ofFn sorted) k x) =
          complexStandardRep n (List.ofFn dataAt) k (G x)) ∧ Function.Injective G := by
    rw [← hrestore]
    exact ⟨permKMap sorted sort, permKMap_equivariant sorted sort, permKMap_injective sorted sort⟩
  have hGsurj : Function.Surjective G :=
    surjective_of_injective_of_kMap _ _ G hG hGinj
      (permKMap dataAt sort.symm) (permKMap_equivariant dataAt sort.symm)
      (permKMap_injective dataAt sort.symm)
  let e := LinearEquiv.ofBijective G ⟨hGinj, hGsurj⟩
  have he (k : Matrix.unitaryGroup (Fin n) ℂ) (x : KF n (List.ofFn sorted)) :
      e (complexStandardRep n (List.ofFn sorted) k x) =
        complexStandardRep n (List.ofFn dataAt) k (e x) := hG k x
  have heSymm (k : Matrix.unitaryGroup (Fin n) ℂ) (x : KF n (List.ofFn dataAt)) :
      e.symm (complexStandardRep n (List.ofFn dataAt) k x) =
        complexStandardRep n (List.ofFn sorted) k (e.symm x) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  refine ⟨e f, fun h => hf₀ (e.injective (h.trans e.map_zero.symm)), ?_⟩
  intro E hE
  let C := e.symm.toLinearMap ∘ₗ E ∘ₗ e.toLinearMap
  obtain ⟨c, hc⟩ := hf C (fun k x => by
    change e.symm (E (e (complexStandardRep n (List.ofFn sorted) k x))) =
      complexStandardRep n (List.ofFn sorted) k (e.symm (E (e x)))
    rw [he, hE, heSymm])
  refine ⟨c, ?_⟩
  have h := congrArg e hc
  change e (e.symm (E (e f))) = e (c • f) at h
  simpa only [e.apply_symm_apply, map_smul] using h

end Langlands.Archimedean
