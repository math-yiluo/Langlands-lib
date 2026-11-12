import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel

/-! # Proof of the intrinsic rational and real character/root complements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.LinearAlgebra

/-- A vector fixed by a finite group of `ℚ`-linear automorphisms is zero when it
lies in the span of vectors each of which is negated by some group element. -/
theorem eq_zero_of_fixed_of_mem_span_negated
    {W V : Type*} [Group W] [Fintype W] [AddCommGroup V] [Module ℚ V]
    (ρ : W →* (V ≃ₗ[ℚ] V)) {R : Set V}
    (hR : ∀ r ∈ R, ∃ w, ρ w r = -r)
    {x : V} (hx : x ∈ Submodule.span ℚ R) (hfix : ∀ w, ρ w x = x) : x = 0 := by
  classical
  let S : V →ₗ[ℚ] V := ∑ w : W, (ρ w : V →ₗ[ℚ] V)
  have hS (v : V) : S v = ∑ w : W, ρ w v := by
    simp only [S, LinearMap.sum_apply, LinearEquiv.coe_coe]
  have hSinv (s : W) (v : V) : S (ρ s v) = S v := by
    rw [hS, hS]
    simp_rw [← LinearEquiv.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun _ => rfl)
  have hker : Submodule.span ℚ R ≤ LinearMap.ker S := by
    rw [Submodule.span_le]
    intro r hr
    obtain ⟨s, hs⟩ := hR r hr
    have h := hSinv s r
    rw [hs, map_neg] at h
    change S r = 0
    have h2 : (2 : ℚ) • S r = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hSx : S x = (Fintype.card W : ℚ) • x := by
    rw [hS, Nat.cast_smul_eq_nsmul]
    simp only [hfix, Finset.sum_const, Finset.card_univ]
  have h0 : (Fintype.card W : ℚ) • x = 0 := by
    rw [← hSx]
    exact hker hx
  exact (smul_eq_zero.mp h0).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every actual relative root of a maximal split torus in a connected reductive
group is negated by the Weyl action of some actual normalizing rational point. -/
theorem IsConnectedReductive.exists_weylAction_eq_neg
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ α ∈ relativeRoots i, ∃ n : normalizerPoints i, weylAction i n α = -α := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hi.isSplitSubtorus.mono
  intro α hα
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hi.1.1 i hα
  obtain ⟨p, hp⟩ := (rootRankOneFactorization k G hG T i hi α hα x hx hx1).1.exists
  exact ⟨_, hp.weylAction_eq_neg i hi.1.1 hα.1 hx hx1⟩

/-- The actual relative-root span meets the rationalized restrictions of the
rational characters of the group only in zero. -/
theorem IsConnectedReductive.relativeRootSpan_disjoint_restrictionRange
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    Disjoint (relativeRootSpan i) (rationalCharacterRestrictRat i).range := by
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : Finite (relativeWeylGroup i) := hG.finite_relativeWeylGroup i hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  rw [Submodule.disjoint_def]
  intro x hx hxr
  refine Langlands.LinearAlgebra.eq_zero_of_fixed_of_mem_span_negated
    (relativeWeylFullRatAction i) (R := toRat '' relativeRoots i) ?_ hx ?_
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨n, hn⟩ := hG.exists_weylAction_eq_neg i hi α hα
    refine ⟨QuotientGroup.mk n, ?_⟩
    rw [relativeWeylFullRatAction_mk, ratAut_toRat, hn, map_neg]
  · obtain ⟨y, rfl⟩ := hxr
    intro w
    exact relativeWeylFullRatAction_restrictionRange i w y

/-- The actual relative-root span and the rationalized restrictions of rational
characters are complementary in the full rational character space. -/
theorem IsConnectedReductive.relativeRootSpan_isCompl_restrictionRange
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    IsCompl (relativeRootSpan i) (rationalCharacterRestrictRat i).range := by
  let := hG.isAffineHom
  exact ⟨hG.relativeRootSpan_disjoint_restrictionRange i hi,
    codisjoint_iff.mpr (hG.relativeRootSpan_sup_restrictionRange_eq_top i hi)⟩

/-- **Intrinsic character/root complements.** Over every field, for every
actual maximal split torus of a connected reductive group, the actual root span
complements the restricted rational characters over `ℚ` and over `ℝ`. -/
theorem relativeCharacterRootComplement : RelativeCharacterRootComplementStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  have h := hG.relativeRootSpan_isCompl_restrictionRange i hi
  exact ⟨h, relativeCharacterRootComplementReal_of_rat i h⟩

end Langlands.GroupScheme
