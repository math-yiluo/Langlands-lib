import Langlands.GroupScheme.Rational.LaurentAdditiveCoordinates
import Langlands.GroupScheme.Rational.TorusLinearization.Euclid
import Mathlib.Data.Fintype.EquivFin

/-! # Finite Frobenius-orbit coordinates for pointed Laurent functions -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.LaurentAugmentation

open MvPolynomial

variable (k : Type u) [CommRing k] (p : ℕ) [hp : Fact p.Prime] (I : Type v)

/-- Pointed Laurent functions supported on a specified finite set of primitive orbits. -/
def finiteOrbitSpace (s : Finset {m : I → ℤ // IsPrimitive p m}) :
    Submodule k (space k (I → ℤ)) :=
  Submodule.span k {f | ∃ a ∈ s, ∃ r : ℕ, f = frobeniusBasis k p I (a, r)}

/-- Project the polynomial orbit variables to a finite list of variables. -/
def finiteProjection (s : Finset {m : I → ℤ // IsPrimitive p m}) :
    MvPolynomial {m : I → ℤ // IsPrimitive p m} k →ₐ[k] MvPolynomial (Fin s.card) k := by
  classical
  exact aeval fun a => if ha : a ∈ s then X (s.equivFin ⟨a, ha⟩) else 0

/-- Finite polynomial coordinates, with all unlisted primitive orbits discarded. -/
def finiteEncoding (s : Finset {m : I → ℤ // IsPrimitive p m}) :
    space k (I → ℤ) →ₗ[k] MvPolynomial (Fin s.card) k :=
  (finiteProjection k p I s).toLinearMap.comp (additiveEncoding (k := k) (p := p) (I := I))

variable {k p I}

theorem basis_mem_finiteOrbitSpace {s : Finset {m : I → ℤ // IsPrimitive p m}}
    {a : {m : I → ℤ // IsPrimitive p m}} (ha : a ∈ s) (r : ℕ) :
    frobeniusBasis k p I (a, r) ∈ finiteOrbitSpace k p I s :=
  Submodule.subset_span ⟨a, ha, r, rfl⟩

theorem finiteEncoding_basis_mem {s : Finset {m : I → ℤ // IsPrimitive p m}}
    {a : {m : I → ℤ // IsPrimitive p m}} (ha : a ∈ s) (r : ℕ) :
    finiteEncoding k p I s (frobeniusBasis k p I (a, r)) =
      X (s.equivFin ⟨a, ha⟩) ^ p ^ r := by
  classical
  simp [finiteEncoding, finiteProjection, ha]

theorem finiteEncoding_basis_not_mem {s : Finset {m : I → ℤ // IsPrimitive p m}}
    {a : {m : I → ℤ // IsPrimitive p m}} (ha : a ∉ s) (r : ℕ) :
    finiteEncoding k p I s (frobeniusBasis k p I (a, r)) = 0 := by
  classical
  simp only [finiteEncoding, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    additiveEncoding_basis, map_pow]
  simpa [finiteProjection, ha] using
    (zero_pow (pow_ne_zero r hp.out.ne_zero) :
      (0 : MvPolynomial (Fin s.card) k) ^ p ^ r = 0)

/-- Restoring the listed variable names recovers the full encoding on their orbit span. -/
theorem rename_finiteEncoding {s : Finset {m : I → ℤ // IsPrimitive p m}}
    {f : space k (I → ℤ)} (hf : f ∈ finiteOrbitSpace k p I s) :
    rename (fun j : Fin s.card => (s.equivFin.symm j).val) (finiteEncoding k p I s f) =
      additiveEncoding (k := k) (p := p) (I := I) f := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, r, rfl⟩ := hf
    rw [finiteEncoding_basis_mem ha, map_pow, rename_X, Equiv.symm_apply_apply,
      additiveEncoding_basis]
  | zero => simp
  | add f g _ _ hf hg => simp only [map_add, hf, hg]
  | smul c f _ hf => simp only [map_smul, hf]

/-- Finite encoding loses no information on the specified orbit span. -/
theorem finiteEncoding_injOn (s : Finset {m : I → ℤ // IsPrimitive p m}) :
    Set.InjOn (finiteEncoding k p I s) (finiteOrbitSpace k p I s) := by
  intro f hf g hg h
  apply additiveEncoding_injective (k := k) (p := p) (I := I)
  rw [← rename_finiteEncoding hf, ← rename_finiteEncoding hg, h]

/-- Each finite family is contained in a finite primitive-orbit span. -/
theorem exists_finiteOrbitSpace (F : Finset (space k (I → ℤ))) :
    ∃ s : Finset {m : I → ℤ // IsPrimitive p m},
      ∀ f ∈ F, f ∈ finiteOrbitSpace k p I s := by
  classical
  let b := frobeniusBasis k p I
  refine ⟨F.biUnion (fun f => (b.repr f).support.image Prod.fst), ?_⟩
  intro f hf
  rw [← b.linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro ar har
  apply Submodule.smul_mem
  exact basis_mem_finiteOrbitSpace
    (Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image.mpr ⟨ar, har, rfl⟩⟩) ar.2

section Frobenius

variable [CharP k p]

/-- Each finite primitive-orbit span is stable under semilinear Frobenius. -/
theorem frobeniusMap_mem_finiteOrbitSpace
    {s : Finset {m : I → ℤ // IsPrimitive p m}} {f : space k (I → ℤ)}
    (hf : f ∈ finiteOrbitSpace k p I s) :
    frobeniusMap (k := k) (p := p) (I := I) f ∈ finiteOrbitSpace k p I s := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, r, rfl⟩ := hf
    rw [frobeniusMap_basis]
    exact basis_mem_finiteOrbitSpace ha (r + 1)
  | zero => simp
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul c f _ hf => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hf

theorem finiteEncoding_frobenius
    (s : Finset {m : I → ℤ // IsPrimitive p m}) (f : space k (I → ℤ)) :
    finiteEncoding k p I s (frobeniusMap (k := k) (p := p) (I := I) f) =
      finiteEncoding k p I s f ^ p := by
  simp only [finiteEncoding, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    additiveEncoding_frobenius, map_pow]

/-- Every projected orbit coordinate is an additive polynomial. -/
theorem finiteEncoding_isAddPoly
    (s : Finset {m : I → ℤ // IsPrimitive p m}) (f : space k (I → ℤ)) :
    TorusLinearization.IsAddPoly (finiteEncoding k p I s f) := by
  classical
  change finiteEncoding k p I s f ∈ TorusLinearization.addPolys s.card k
  rw [← (frobeniusBasis k p I).linearCombination_repr f,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro ar _
  rw [map_smul]
  apply Submodule.smul_mem
  by_cases ha : ar.1 ∈ s
  · rw [finiteEncoding_basis_mem ha]
    exact (TorusLinearization.isAddPoly_X _).pow_char p (CharP.cast_eq_zero k p) ar.2
  · rw [finiteEncoding_basis_not_mem ha]
    exact zero_mem _

end Frobenius

end Langlands.GroupScheme.LaurentAugmentation
