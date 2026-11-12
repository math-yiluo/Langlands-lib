import Mathlib
import Langlands.CommutativeAlgebra.FiniteTypeIntGRing.RegularQuotient

/-! # A derivation test for quotients of regular local rings -/

namespace Langlands.CommutativeAlgebra.FiniteTypeIntGRing

open IsLocalRing

section

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {V : Type*} [AddCommGroup V] [Module (ResidueField R) V]
  [Module (ResidueField R)ᵐᵒᵖ V]

/-- A ring hom into a trivial square-zero extension of the residue field whose first component
is the residue map has second component vanishing on the square of the maximal ideal. -/
theorem trivSqZeroExt_snd_eq_zero_of_mem_sq (Ψ : R →+* TrivSqZeroExt (ResidueField R) V)
    (hΨ : ∀ x, (Ψ x).fst = residue R x) {z : R} (hz : z ∈ maximalIdeal R ^ 2) :
    (Ψ z).snd = 0 := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro x hx y hy
    rw [map_mul, TrivSqZeroExt.snd_mul, hΨ, hΨ, (residue_eq_zero_iff x).mpr hx,
      (residue_eq_zero_iff y).mpr hy]
    simp
  · intro x y hx hy
    rw [map_add, TrivSqZeroExt.snd_add, hx, hy, add_zero]

/-- The second component of such a ring hom is linear over `R` on the maximal ideal. -/
theorem trivSqZeroExt_snd_mul_of_mem (Ψ : R →+* TrivSqZeroExt (ResidueField R) V)
    (hΨ : ∀ x, (Ψ x).fst = residue R x) (a : R) {x : R} (hx : x ∈ maximalIdeal R) :
    (Ψ (a * x)).snd = residue R a • (Ψ x).snd := by
  rw [map_mul, TrivSqZeroExt.snd_mul, hΨ, hΨ, (residue_eq_zero_iff x).mpr hx]
  simp

end

/-- The class of a linear combination of elements of the maximal ideal in the cotangent space. -/
theorem toCotangent_sum_mul {R : Type*} [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι] (f : ι → R) (hfm : ∀ i, f i ∈ maximalIdeal R) (a : ι → R) :
    (maximalIdeal R).toCotangent
      ⟨∑ i, a i * f i, Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hfm i)⟩ =
      ∑ i, residue R (a i) • (maximalIdeal R).toCotangent ⟨f i, hfm i⟩ := by
  have : (⟨∑ i, a i * f i, Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hfm i)⟩ :
      maximalIdeal R) = ∑ i, a i • (⟨f i, hfm i⟩ : maximalIdeal R) := by
    ext
    simp [smul_eq_mul]
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  exact (algebraMap_smul (ResidueField R) (a i) _).symm

/-- Linear independence in the cotangent space: the classes of `fᵢ ∈ 𝔪` in `𝔪 / 𝔪²` are
linearly independent over the residue field if and only if every relation `∑ aᵢ fᵢ ∈ 𝔪²` has
all coefficients in `𝔪`. -/
theorem linearIndependent_toCotangent_iff {R : Type*} [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι] (f : ι → R) (hfm : ∀ i, f i ∈ maximalIdeal R) :
    LinearIndependent (ResidueField R) (fun i => (maximalIdeal R).toCotangent ⟨f i, hfm i⟩) ↔
      ∀ a : ι → R, ∑ i, a i * f i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R := by
  classical
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h a ha i
    have hz := (Ideal.toCotangent_eq_zero (maximalIdeal R)
      ⟨∑ i, a i * f i, Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hfm i)⟩).mpr ha
    rw [toCotangent_sum_mul f hfm a] at hz
    exact (residue_eq_zero_iff _).mp (h _ hz i)
  · intro h g hg
    choose a ha using fun i => residue_surjective (R := R) (g i)
    have hsum := toCotangent_sum_mul f hfm a
    simp_rw [ha, hg, Ideal.toCotangent_eq_zero] at hsum
    intro i
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (h a hsum i)

/-- **Derivation test.** Let `R` be a regular local ring and let `Ψ` be a ring hom from `R` to
the trivial square-zero extension `κ ⊕ V` of its residue field `κ` whose first component is the
residue map (equivalently, the second component of `Ψ` is a derivation `R → V`). If `f` is a
finite family in the maximal ideal whose derivatives `(Ψ (f i)).snd` are linearly independent,
then `R ⧸ (f)` is a regular local ring. -/
theorem isRegularLocalRing_quotient_of_trivSqZeroExt {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {V : Type*} [AddCommGroup V] [Module (ResidueField R) V]
    [Module (ResidueField R)ᵐᵒᵖ V] [IsCentralScalar (ResidueField R) V]
    (Ψ : R →+* TrivSqZeroExt (ResidueField R) V) (hΨ : ∀ x, (Ψ x).fst = residue R x)
    {ι : Type*} [Fintype ι] (f : ι → R) (hfm : ∀ i, f i ∈ maximalIdeal R)
    (hf : LinearIndependent (ResidueField R) (fun i => (Ψ (f i)).snd)) :
    IsRegularLocalRing (R ⧸ Ideal.span (Set.range f)) := by
  classical
  refine isRegularLocalRing_quotient_span_of_linearIndependent f hfm
    ((linearIndependent_toCotangent_iff f hfm).mpr fun a ha => ?_)
  rw [Fintype.linearIndependent_iff] at hf
  have h0 := trivSqZeroExt_snd_eq_zero_of_mem_sq Ψ hΨ ha
  rw [map_sum, TrivSqZeroExt.snd_sum] at h0
  have h1 : ∑ i, residue R (a i) • (Ψ (f i)).snd = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [trivSqZeroExt_snd_mul_of_mem Ψ hΨ (a i) (hfm i)]
  intro i
  exact (residue_eq_zero_iff _).mp (hf _ h1 i)

end Langlands.CommutativeAlgebra.FiniteTypeIntGRing
