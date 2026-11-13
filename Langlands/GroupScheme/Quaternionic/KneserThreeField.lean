import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The quadratic field `K[X]/(X² - c)` and its embeddings

For `c ∈ K` not a square, `field c = AdjoinRoot (X² - c)` is a quadratic field. It is separable
when `2 ≠ 0`, and the Library's conjugation sends the root to its negative. An element `x` of a
`K`-algebra with `x² = c` defines a `K`-algebra homomorphism `embed : field c →ₐ[K] D` sending the
root to `x`.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.GroupScheme.KneserThree.QuadField

variable {K : Type u} [Field K]

/-- The polynomial `X² - c`. -/
def poly (c : K) : K[X] := X ^ 2 - C c

theorem poly_monic (c : K) : (poly c).Monic := by
  unfold poly
  exact monic_X_pow_sub_C c (by norm_num)

theorem poly_natDegree (c : K) : (poly c).natDegree = 2 := by
  unfold poly
  exact natDegree_X_pow_sub_C

theorem poly_ne_zero (c : K) : poly c ≠ 0 := (poly_monic c).ne_zero

theorem irreducible_poly {c : K} (hc : ∀ r : K, r * r ≠ c) : Irreducible (poly c) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [poly_natDegree]
    decide
  · intro r hr
    apply hc r
    simp only [poly, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
    rw [← hr, sq]

/-- The quadratic field `K[X]/(X² - c)`. -/
abbrev field (c : K) : Type u := AdjoinRoot (poly c)

variable {c : K} [Fact (Irreducible (poly c))]

instance : Algebra.IsQuadraticExtension K (field c) where
  finrank_eq_two' := by
    rw [(AdjoinRoot.powerBasis (poly_ne_zero c)).finrank, AdjoinRoot.powerBasis_dim,
      poly_natDegree]

theorem isSeparable (h2 : (2 : K) ≠ 0) (hc : c ≠ 0) : Algebra.IsSeparable K (field c) := by
  have hsep : IsSeparable K (AdjoinRoot.root (poly c)) := by
    unfold IsSeparable
    rw [AdjoinRoot.minpoly_root (poly_ne_zero c), (poly_monic c).leadingCoeff, inv_one, C_1,
      mul_one]
    exact separable_X_pow_sub_C c (by exact_mod_cast h2) hc
  have h := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (F := K)
    (x := AdjoinRoot.root (poly c))).mpr hsep
  have htop : IntermediateField.adjoin K {AdjoinRoot.root (poly c)} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra K _ (AdjoinRoot.adjoinRoot_eq_top)
  rw [htop] at h
  exact AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv

/-- The root. -/
abbrev root : field c := AdjoinRoot.root (poly c)

theorem root_mul_self : (root : field c) * root = algebraMap K (field c) c := by
  have h : AdjoinRoot.mk (poly c) (poly c) = 0 := AdjoinRoot.mk_self
  have h' : AdjoinRoot.mk (poly c) (X ^ 2 - C c) = 0 := h
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h'
  rw [← sq]
  exact h'

/-- The power basis `1, root`. -/
abbrev powerBasis : PowerBasis K (field c) := AdjoinRoot.powerBasis' (poly_monic c)

theorem powerBasis_dim : (powerBasis (c := c)).dim = 2 := by
  rw [AdjoinRoot.powerBasis'_dim, poly_natDegree]

/-- Every element is `a₀ + a₁ root`. -/
theorem exists_eq (a : field c) : ∃ a₀ a₁ : K, a = a₀ • (1 : field c) + a₁ • root := by
  obtain ⟨f, hf, rfl⟩ := (powerBasis (c := c)).exists_eq_aeval a
  rw [powerBasis_dim] at hf
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)]
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  simp [AdjoinRoot.powerBasis'_gen, Algebra.smul_def, add_comm]

theorem trace_root : Algebra.trace K (field c) root = 0 := by
  have h := (powerBasis (c := c)).trace_gen_eq_nextCoeff_minpoly
  rw [AdjoinRoot.powerBasis'_gen] at h
  rw [h, AdjoinRoot.minpoly_root (poly_ne_zero c), (poly_monic c).leadingCoeff, inv_one, C_1,
    mul_one, neg_eq_zero, nextCoeff, poly_natDegree]
  simp [poly, coeff_X_pow]

section Conjugation

variable [Algebra.IsSeparable K (field c)]

theorem conjugation_root :
    SU3Root.conjugation K (field c) root = -root := by
  have h := SU3Root.algebraMap_trace K (field c) root
  rw [trace_root, map_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

end Conjugation

section Embed

variable {D : Type*} [Ring D] [Algebra K D] (x : D) (hx : x * x = algebraMap K D c)

/-- The embedding sending the root to `x`. -/
def embed : field c →ₐ[K] D :=
  Ideal.Quotient.liftₐ (Ideal.span {poly c}) (Polynomial.aeval x) (by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    have : Polynomial.aeval x (poly c) = 0 := by
      simp [poly, sq, hx]
    rw [this, mul_zero])

theorem embed_root : embed x hx (root : field c) = x := by
  change (Ideal.Quotient.liftₐ _ (Polynomial.aeval x) _)
    (Ideal.Quotient.mkₐ K (Ideal.span {poly c}) X) = x
  rw [← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp, aeval_X]

end Embed

end Langlands.GroupScheme.KneserThree.QuadField
