import Langlands.Weil.Representation.UnitaryRestriction
import Langlands.Weil.Representation.CharacterLine
import Langlands.WeilDeligne.InductionAlong

/-!
# Unitarity of finite-index induction

For a finite-index subgroup `S` of a group `G` and a unitary finite-dimensional complex
representation `A` of `S`, the induced representation `induce S A` is unitary. The invariant
inner product sums the inner products of the values at chosen right-coset representatives.
Character lines of characters with values of absolute value one are unitary.
-/

noncomputable section

universe uG uH uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] (S : Subgroup G) [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace Induction

omit [S.FiniteIndex] in
/-- Right translation of right cosets, `Sx ↦ Sxg`, read on chosen representatives, is
injective. -/
theorem coset_out_mul_injective (g : G) :
    Function.Injective fun q : Cosets S => coset S (q.out * g) := by
  intro q q' hqq
  have h' : QuotientGroup.rightRel S (q.out * g) (q'.out * g) := Quotient.exact hqq
  rw [QuotientGroup.rightRel_apply] at h'
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  apply Quotient.sound
  have hrw : q'.out * g * (q.out * g)⁻¹ = q'.out * q.out⁻¹ := by group
  exact QuotientGroup.rightRel_apply.mpr (by rwa [hrw] at h')

/-- Right translation of right cosets is a bijection. -/
theorem coset_out_mul_bijective (g : G) :
    Function.Bijective fun q : Cosets S => coset S (q.out * g) :=
  Finite.injective_iff_bijective.mp (coset_out_mul_injective S g)

/-- An equivariant function is determined by its values on the chosen representatives. -/
theorem val_eq_factor (A : FiniteRepresentation.{0, uG, uV} ℂ S) (f : induce S A) (x : G) :
    f.val x = A.representation (factor S x) (f.val (coset S x).out) := by
  conv_lhs => rw [← factor_mul_out S x]
  exact f.property (factor S x) (coset S x).out

end Induction

open Induction

/-- The inner product on `induce S A` obtained from an inner product on `A`: the sum over right
cosets of the inner products of the values at the chosen representatives. -/
@[instance_reducible]
def inducedInnerCore (A : FiniteRepresentation.{0, uG, uV} ℂ S)
    (h : InnerProductSpace.Core ℂ A) : InnerProductSpace.Core ℂ (induce S A) where
  inner f f' := ∑ q : Cosets S, h.inner (f.val q.out) (f'.val q.out)
  conj_inner_symm f f' := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => h.conj_inner_symm _ _
  re_inner_nonneg f := by
    rw [map_sum]
    exact Finset.sum_nonneg fun q _ => h.re_inner_nonneg _
  add_left f f' f'' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => h.add_left _ _ _
  smul_left f f' r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => h.smul_left _ _ _
  definite f hf := by
    have hsum : ∑ q : Cosets S, RCLike.re (h.inner (f.val q.out) (f.val q.out)) = 0 := by
      rw [← map_sum]
      change RCLike.re (∑ q : Cosets S, h.inner (f.val q.out) (f.val q.out)) = 0 at *
      rw [hf, map_zero]
    have hre := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => h.re_inner_nonneg _).mp hsum
    have hval : ∀ q : Cosets S, f.val q.out = 0 := fun q => h.definite _ (by
      apply Complex.ext
      · simpa using hre q (Finset.mem_univ q)
      · exact Complex.conj_eq_iff_im.mp (h.conj_inner_symm _ _))
    have hzero : ∀ x, f.val x = 0 := fun x => by
      rw [val_eq_factor S A f x, hval, map_zero]
    exact Subtype.ext (funext hzero)

theorem inducedInnerCore_inner (A : FiniteRepresentation.{0, uG, uV} ℂ S)
    (h : InnerProductSpace.Core ℂ A) (f f' : induce S A) :
    (inducedInnerCore S A h).inner f f' =
      ∑ q : Cosets S, h.inner (f.val q.out) (f'.val q.out) := rfl

/-- The induced inner product is invariant when the original one is. -/
theorem inducedInnerCore_invariant (A : FiniteRepresentation.{0, uG, uV} ℂ S)
    (h : InnerProductSpace.Core ℂ A)
    (hinv : ∀ (s : S) (v w : A),
      h.inner (A.representation s v) (A.representation s w) = h.inner v w)
    (g : G) (f f' : induce S A) :
    (inducedInnerCore S A h).inner ((induce S A).representation g f)
        ((induce S A).representation g f') =
      (inducedInnerCore S A h).inner f f' := by
  rw [inducedInnerCore_inner, inducedInnerCore_inner]
  change ∑ q : Cosets S, h.inner (f.val (q.out * g)) (f'.val (q.out * g)) = _
  calc ∑ q : Cosets S, h.inner (f.val (q.out * g)) (f'.val (q.out * g))
      = ∑ q : Cosets S, h.inner (f.val (coset S (q.out * g)).out)
          (f'.val (coset S (q.out * g)).out) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [val_eq_factor S A f (q.out * g), val_eq_factor S A f' (q.out * g), hinv]
    _ = ∑ q : Cosets S, h.inner (f.val q.out) (f'.val q.out) :=
        (coset_out_mul_bijective S g).sum_comp
          (fun q : Cosets S => h.inner (f.val q.out) (f'.val q.out))

/-- Finite-index induction preserves unitarity. -/
theorem isUnitary_induce (A : FiniteRepresentation.{0, uG, uV} ℂ S) (hA : A.IsUnitary) :
    (induce S A).IsUnitary := by
  obtain ⟨h, hinv⟩ := hA
  exact ⟨inducedInnerCore S A h, inducedInnerCore_invariant S A h hinv⟩

/-- Induction along an injective map with finite-index image preserves unitarity. -/
theorem isUnitary_induceAlong {H : Type uH} [Group H] (ι : H →* G)
    (hι : Function.Injective ι) [ι.range.FiniteIndex]
    (A : FiniteRepresentation.{0, uH, uV} ℂ H) (hA : A.IsUnitary) :
    (induceAlong ι hι A).IsUnitary :=
  isUnitary_induce ι.range _ (isUnitary_restrict _ hA)

omit [S.FiniteIndex] in
/-- The line of a character whose values have absolute value one is unitary. -/
theorem characterLine_isUnitary (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1) :
    (characterLine.{uG, uV} χ).IsUnitary := by
  apply isUnitary_of_equiv (characterLineEquiv χ)
  refine ⟨InnerProductSpace.toCore, ?_⟩
  intro g x y
  change inner ℂ ((χ g : ℂ) * x) ((χ g : ℂ) * y) = inner ℂ x y
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul]
  calc (χ g : ℂ) * y * ((starRingEnd ℂ) (χ g : ℂ) * (starRingEnd ℂ) x)
      = ((starRingEnd ℂ) (χ g : ℂ) * (χ g : ℂ)) * (y * (starRingEnd ℂ) x) := by ring
    _ = y * (starRingEnd ℂ) x := by
        rw [Complex.conj_mul', hχ g]
        simp

end Langlands.FiniteRepresentation
