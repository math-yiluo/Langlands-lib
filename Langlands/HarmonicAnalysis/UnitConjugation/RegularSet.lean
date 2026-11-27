import Langlands.HarmonicAnalysis.UnitConjugation.PairingHaar
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Rank
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# The regular set of the Lie algebra of `Aˣ`

Let `A` be a finite-dimensional associative algebra over a field `F`, regarded as the Lie
algebra of its unit group `Aˣ` with the commutator bracket. For `X : A` the adjoint endomorphism
is `ad X : Y ↦ X Y - Y X` (`adjointEndomorphism`; `adjointEndomorphism_eq_ad` identifies it with
Mathlib's `LieAlgebra.ad`). This module defines Harish-Chandra's regular set `g'`:

* `lieAlgebraRank F A`: the rank `ℓ` of the Lie algebra `A`, Mathlib's `LieAlgebra.rank`: the
  least `n` such that the coefficient of `t^n` in the characteristic polynomial of `ad` of the
  generic element is not the zero polynomial;
* `adjointEta F X`: `η(X)`, the coefficient of `t^ℓ` in `det(t - ad X)`;
* `regularSet F A`: `g' = {X | η(X) ≠ 0}`.

`mem_regularSet_iff_isRegular` identifies `g'` with Mathlib's regular elements
`LieAlgebra.IsRegular`; `mem_regularSet_iff` shows that `X ∈ g'` exactly when the multiplicity of
the root `0` of `det(t - ad X)` equals `ℓ`; `lieAlgebraRank_le` shows that this multiplicity is at
least `ℓ` for every `X`; `regularSet_nonempty` that `g'` is nonempty, so that the multiplicity `ℓ`
is attained, over an infinite field; and `conj_mem_regularSet_iff` that `g'` is stable under
conjugation by `Aˣ`, through `adjointEndomorphism_conj`, which conjugates `ad X` by the linear
equivalence `conjugationLinearEquiv` of `Langlands.HarmonicAnalysis.UnitConjugation.PairingHaar`.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), Introduction, printed p. 2: "Let `ℓ` denote the (absolute) rank of
`g`. For `X ∈ g`, let `η_g(X)` denote the coefficient of `t^ℓ` in the polynomial
`det(t - ad X)` … Let `g'` be the set of all points `X ∈ g` such that `η(X) ≠ 0`."
-/

noncomputable section

open Polynomial

namespace Langlands.HarmonicAnalysis.UnitConjugation

universe u v

section Adjoint

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A]

/-- The adjoint endomorphism `ad X : Y ↦ X Y - Y X` of `A`, as an `F`-linear map. -/
def adjointEndomorphism (X : A) : A →ₗ[F] A :=
  LinearMap.mulLeft F X - LinearMap.mulRight F X

@[simp]
theorem adjointEndomorphism_apply (X Y : A) : adjointEndomorphism F X Y = X * Y - Y * X := rfl

/-- `ad (w X w⁻¹)` is the conjugate of `ad X` by conjugation with the unit `w`. -/
theorem adjointEndomorphism_conj (w : Aˣ) (X : A) :
    adjointEndomorphism F ((w : A) * X * ((w⁻¹ : Aˣ) : A)) =
      (conjugationLinearEquiv F w).conj (adjointEndomorphism F X) := by
  ext Y
  obtain ⟨Z, rfl⟩ := (conjugationLinearEquiv F w).surjective Y
  simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.symm_apply_apply]
  simp only [adjointEndomorphism_apply, conjugationLinearEquiv_apply, mul_sub, sub_mul, mul_assoc,
    Units.inv_mul_cancel_left]

/-- The adjoint endomorphism is Mathlib's adjoint action `LieAlgebra.ad` of the commutator Lie
algebra. -/
theorem adjointEndomorphism_eq_ad (X : A) :
    letI : LieRing A := LieRing.ofAssociativeRing
    adjointEndomorphism F X = LieAlgebra.ad F A X := by
  let : LieRing A := LieRing.ofAssociativeRing
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  rfl

end Adjoint

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A]

variable (A) in
/-- The rank `ℓ` of `A` as a Lie algebra with the commutator bracket: Mathlib's
`LieAlgebra.rank`, the least `n` such that the coefficient of `t^n` in the characteristic
polynomial `det(t - ad X)` of the generic element is not the zero polynomial. -/
def lieAlgebraRank : ℕ :=
  letI : LieRing A := LieRing.ofAssociativeRing
  LieAlgebra.rank F A

/-- Harish-Chandra's `η(X)`: the coefficient of `t^ℓ` in `det(t - ad X)`, `ℓ` the rank. -/
def adjointEta (X : A) : F :=
  (LinearMap.charpoly (adjointEndomorphism F X)).coeff (lieAlgebraRank F A)

variable (A) in
/-- Harish-Chandra's regular set `g' = {X ∈ A | η(X) ≠ 0}`. -/
def regularSet : Set A :=
  {X | adjointEta F X ≠ 0}

/-- The regular set consists of Mathlib's regular elements `LieAlgebra.IsRegular` of the
commutator Lie algebra. -/
theorem mem_regularSet_iff_isRegular (X : A) :
    X ∈ regularSet F A ↔
      letI : LieRing A := LieRing.ofAssociativeRing
      LieAlgebra.IsRegular F X := by
  let : LieRing A := LieRing.ofAssociativeRing
  change (LinearMap.charpoly (adjointEndomorphism F X)).coeff (LieAlgebra.rank F A) ≠ 0 ↔ _
  rw [LieAlgebra.isRegular_def, adjointEndomorphism_eq_ad]

/-- The rank is at most the multiplicity of the root `0` of `det(t - ad X)`. -/
theorem lieAlgebraRank_le (X : A) :
    lieAlgebraRank F A ≤ (LinearMap.charpoly (adjointEndomorphism F X)).natTrailingDegree := by
  let : LieRing A := LieRing.ofAssociativeRing
  rw [adjointEndomorphism_eq_ad]
  exact LieAlgebra.rank_le_natTrailingDegree_charpoly_ad F X

/-- `X` is regular exactly when the multiplicity of the eigenvalue `0` of `ad X`, the dimension
of the generalized `0`-eigenspace of `ad X`, is the rank. -/
theorem mem_regularSet_iff (X : A) :
    X ∈ regularSet F A ↔
      (LinearMap.charpoly (adjointEndomorphism F X)).natTrailingDegree = lieAlgebraRank F A := by
  let : LieRing A := LieRing.ofAssociativeRing
  rw [mem_regularSet_iff_isRegular, LieAlgebra.isRegular_iff_natTrailingDegree_charpoly_eq_rank,
    adjointEndomorphism_eq_ad]
  rfl

/-- Over an infinite field the regular set is nonempty. -/
theorem regularSet_nonempty [Infinite F] : (regularSet F A).Nonempty := by
  let : LieRing A := LieRing.ofAssociativeRing
  obtain ⟨X, hX⟩ := LieAlgebra.exists_isRegular F A
  exact ⟨X, (mem_regularSet_iff_isRegular F X).2 hX⟩

/-- `det(t - ad X)` is invariant under conjugation by units. -/
theorem charpoly_adjointEndomorphism_conj (w : Aˣ) (X : A) :
    LinearMap.charpoly (adjointEndomorphism F ((w : A) * X * ((w⁻¹ : Aˣ) : A))) =
      LinearMap.charpoly (adjointEndomorphism F X) := by
  rw [adjointEndomorphism_conj]
  exact LinearEquiv.charpoly_conj _ _

theorem adjointEta_conj (w : Aˣ) (X : A) :
    adjointEta F ((w : A) * X * ((w⁻¹ : Aˣ) : A)) = adjointEta F X := by
  simp only [adjointEta, charpoly_adjointEndomorphism_conj]

/-- The regular set is stable under conjugation by `Aˣ`. -/
theorem conj_mem_regularSet_iff (w : Aˣ) (X : A) :
    (w : A) * X * ((w⁻¹ : Aˣ) : A) ∈ regularSet F A ↔ X ∈ regularSet F A := by
  simp only [regularSet, Set.mem_ofPred_eq, adjointEta_conj]

end Langlands.HarmonicAnalysis.UnitConjugation
