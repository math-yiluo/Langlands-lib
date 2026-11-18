import Langlands.Algebra.SymmetricDerivation
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Nilpotent.Defs

/-! # The Frobenius subspace has no nilpotent-equivariant projection -/

noncomputable section

universe u v

namespace Langlands.Algebra.SymmetricDerivation

open SymmetricGrading

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The span of the `p`th powers of linear generators in the genuine symmetric
algebra. -/
def frobeniusSpan (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] (p : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  Submodule.span R (Set.range fun x : M => (SymmetricAlgebra.ι R M x) ^ p)

theorem pow_ι_mem_homogeneousSpan (p : ℕ) (x : M) :
    (SymmetricAlgebra.ι R M x) ^ p ∈ homogeneousSpan R M p := by
  simpa using prod_mem_homogeneousSpan R M (List.replicate p x)

theorem frobeniusSpan_le_homogeneousSpan (p : ℕ) :
    frobeniusSpan R M p ≤ homogeneousSpan R M p := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  exact pow_ι_mem_homogeneousSpan p x

/-- The Frobenius subspace as a submodule of its genuine degree-`p` component. -/
def frobeniusSubspace (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] (p : ℕ) : Submodule R (homogeneousSpan R M p) :=
  (frobeniusSpan R M p).comap (homogeneousSpan R M p).subtype

/-- Every derivation in characteristic `p` kills `p`th powers. -/
theorem derivation_pow_eq_zero (p : ℕ) [CharP R p]
    {A : Type*} [CommRing A] [Algebra R A]
    (D : Derivation R A A) (a : A) : D (a ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero R p,
    zero_smul]

/-- Every derivation kills the entire Frobenius span. -/
theorem derivation_eq_zero_of_mem_frobeniusSpan (p : ℕ) [CharP R p]
    (D : Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M))
    {a : SymmetricAlgebra R M} (ha : a ∈ frobeniusSpan R M p) : D a = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨x, rfl⟩ := ha
    exact derivation_pow_eq_zero p D _
  | zero => exact map_zero D
  | add a c ha hc iha ihc => simp only [map_add, iha, ihc, add_zero]
  | smul r a ha iha => simp only [Derivation.map_smul, iha, smul_zero]

section Field

variable {k : Type u} [Field k] [Module k M]

/-- A nonzero linear generator stays nonzero in the genuine symmetric algebra. -/
theorem ι_ne_zero {x : M} (hx : x ≠ 0) : SymmetricAlgebra.ι k M x ≠ 0 := by
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_ne_zero k hx
  intro h
  have heq := congrArg (SymmetricAlgebra.lift ell) h
  exact hell (by simpa using heq)

/-- A length-two nonzero nilpotent chain obstructs a commuting projection from
the degree-`p` component onto the span of `p`th powers. -/
theorem not_isProj_frobeniusSubspace_of_chain (p : ℕ) [CharP k p] (hp : 0 < p)
    (f : Module.End k M) {x y : M} (hfx : f x = y) (hfy : f y = 0) (hy : y ≠ 0)
    (P : Module.End k (homogeneousSpan k M p))
    (hcomm : (homogeneous f p).comp P = P.comp (homogeneous f p)) :
    ¬ LinearMap.IsProj (frobeniusSubspace k M p) P := by
  intro hP
  let w : homogeneousSpan k M p :=
    ⟨(SymmetricAlgebra.ι k M y) ^ p, pow_ι_mem_homogeneousSpan p y⟩
  let z : homogeneousSpan k M p :=
    ⟨(SymmetricAlgebra.ι k M y) ^ (p - 1) * SymmetricAlgebra.ι k M x, by
      simpa only [Nat.sub_add_cancel hp, pow_one] using
        mul_mem_homogeneousSpan k M (pow_ι_mem_homogeneousSpan (p - 1) y)
          (pow_ι_mem_homogeneousSpan 1 x)⟩
  have hw : w ∈ frobeniusSubspace k M p :=
    Submodule.subset_span ⟨y, rfl⟩
  have hdz : homogeneous f p z = w := by
    apply Subtype.ext
    change induced f ((SymmetricAlgebra.ι k M y) ^ (p - 1) *
      SymmetricAlgebra.ι k M x) = (SymmetricAlgebra.ι k M y) ^ p
    simp only [Derivation.leibniz, Derivation.leibniz_pow, induced_ι, hfx, hfy,
      map_zero, smul_eq_mul, mul_zero, smul_zero, add_zero]
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hdP : homogeneous f p (P z) = 0 := by
    apply Subtype.ext
    exact derivation_eq_zero_of_mem_frobeniusSpan p (induced f) (hP.map_mem z)
  have h := LinearMap.congr_fun hcomm z
  change homogeneous f p (P z) = P (homogeneous f p z) at h
  rw [hdP, hdz, hP.map_id w hw] at h
  have hw0 : w ≠ 0 := by
    intro hw0
    have := congrArg Subtype.val hw0
    exact pow_ne_zero p (ι_ne_zero hy) this
  exact hw0 h.symm

/-- A nonzero nilpotent endomorphism has a nonzero chain of length two. -/
theorem exists_chain_of_isNilpotent (f : Module.End k M) (hf : IsNilpotent f)
    (hf0 : f ≠ 0) : ∃ x y : M, f x = y ∧ f y = 0 ∧ y ≠ 0 := by
  have hex : ∃ a : M, f a ≠ 0 := by
    by_contra! h
    exact hf0 (LinearMap.ext h)
  obtain ⟨a, ha⟩ := hex
  let : Nontrivial M := ⟨⟨f a, 0, ha⟩⟩
  have hn : 1 < nilpotencyClass f := by
    have hpos := pos_nilpotencyClass_iff.mpr hf
    have hne := (nilpotencyClass_eq_one (x := f)).not.mpr hf0
    omega
  have hex' : ∃ b : M, (f ^ (nilpotencyClass f - 1)) b ≠ 0 := by
    by_contra! h
    exact pow_pred_nilpotencyClass hf (LinearMap.ext h)
  obtain ⟨b, hb⟩ := hex'
  refine ⟨(f ^ (nilpotencyClass f - 2)) b,
    (f ^ (nilpotencyClass f - 1)) b, ?_, ?_, hb⟩
  · have he : nilpotencyClass f - 2 + 1 = nilpotencyClass f - 1 := by omega
    rw [← Module.End.mul_apply, ← pow_succ', he]
  · rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (by omega),
      pow_nilpotencyClass hf, LinearMap.zero_apply]

/-- No nonzero nilpotent endomorphism admits a commuting projection onto the
Frobenius subspace of its genuine degree-`p` symmetric component. -/
theorem not_isProj_frobeniusSubspace_of_isNilpotent (p : ℕ) [CharP k p] (hp : 0 < p)
    (f : Module.End k M) (hf : IsNilpotent f) (hf0 : f ≠ 0)
    (P : Module.End k (homogeneousSpan k M p))
    (hcomm : (homogeneous f p).comp P = P.comp (homogeneous f p)) :
    ¬ LinearMap.IsProj (frobeniusSubspace k M p) P := by
  obtain ⟨x, y, hfx, hfy, hy⟩ := exists_chain_of_isNilpotent f hf hf0
  exact not_isProj_frobeniusSubspace_of_chain p hp f hfx hfy hy P hcomm

end Field

end Langlands.Algebra.SymmetricDerivation
