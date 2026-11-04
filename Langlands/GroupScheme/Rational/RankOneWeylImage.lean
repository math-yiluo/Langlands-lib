import Langlands.GroupScheme.Rational.RelativeWeylRootPermutation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! # The actual Weyl-action image in semisimple rank at most one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

private theorem toRat_mem_span_singleton_of_dependent
    (hT : IsSplitTorus T.toGrp) {α β : characterLattice T} (hα : α ≠ 0)
    (hdep : ¬ LinearIndependent ℤ ![α, β]) :
    toRat β ∈ Submodule.span ℚ {toRat α} := by
  have hαrat : toRat α ≠ 0 := by
    intro h
    apply hα
    exact hT.character_toRat_injective (by simpa using h)
  rw [LinearIndependent.pair_iff] at hdep
  push Not at hdep
  obtain ⟨m, n, hmn, hne⟩ := hdep
  have hrat : (m : ℚ) • toRat α + (n : ℚ) • toRat β = 0 := by
    simpa only [map_add, map_zsmul, map_zero, Int.cast_smul_eq_zsmul] using
      congrArg toRat hmn
  have hn : (n : ℚ) ≠ 0 := by
    intro hn
    have hn' : n = 0 := by exact_mod_cast hn
    rw [hn, zero_smul, add_zero] at hrat
    have hm : (m : ℚ) = 0 := (smul_eq_zero.mp hrat).resolve_right hαrat
    have hm' : m = 0 := by exact_mod_cast hm
    exact hne hm' hn'
  apply Submodule.mem_span_singleton.mpr
  refine ⟨-(m : ℚ) / (n : ℚ), ?_⟩
  have hrel : (n : ℚ) • toRat β = -(m : ℚ) • toRat α := by
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_right hrat
  calc
    (-(m : ℚ) / (n : ℚ)) • toRat α =
        (n : ℚ)⁻¹ • (-(m : ℚ) • toRat α) := by
      rw [smul_smul, div_eq_mul_inv, mul_comm]
    _ = (n : ℚ)⁻¹ • ((n : ℚ) • toRat β) := by rw [hrel]
    _ = toRat β := by rw [smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Under pairwise integral dependence of the actual roots, any actual root
spans their entire rational span. -/
theorem IsSplitTorus.relativeRootSpan_eq_span_singleton_of_rankOne
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hdep : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} (hα : α ∈ roots i) :
    relativeRootSpan i = Submodule.span ℚ {toRat α} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    exact toRat_mem_span_singleton_of_dependent hT hα.1 (hdep α hα β hβ)
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (toRat_mem_ratSpan hα))

/-- Pairwise integral dependence of actual roots bounds their rational
span by one, allowing the empty root set. -/
theorem IsSplitTorus.finrank_relativeRootSpan_le_one_of_rankOne
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hdep : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) :
    Module.finrank ℚ (relativeRootSpan i) ≤ 1 := by
  classical
  rcases (roots i).eq_empty_or_nonempty with hempty | ⟨α, hα⟩
  · change Module.finrank ℚ ↥(Submodule.span ℚ (toRat '' roots i)) ≤ 1
    rw [hempty, Set.image_empty, Submodule.span_empty, finrank_bot]
    exact Nat.zero_le _
  · have hneq : toRat α ≠ 0 := by
      intro h
      exact hα.1 (hT.character_toRat_injective (by simpa using h))
    rw [hT.relativeRootSpan_eq_span_singleton_of_rankOne i hdep hα,
      finrank_span_singleton hneq]

private theorem finOrder_linearEquiv_eq_one_or_neg
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (hdim : Module.finrank ℚ V ≤ 1) (e : V ≃ₗ[ℚ] V) (he : IsOfFinOrder e) :
    e = 1 ∨ e = LinearEquiv.neg ℚ := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℚ V) with hzero | hpos
  · have : Subsingleton V := Module.finrank_zero_iff.mp hzero
    exact Or.inl (Subsingleton.elim _ _)
  have hone : Module.finrank ℚ V = 1 := by omega
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hone e.toLinearMap
  have heval (v : V) : e v = c • v := by
    exact congrArg (fun f : V →ₗ[ℚ] V => f v) hc
  have hpow (n : ℕ) (v : V) : (e ^ n) v = c ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, heval, smul_smul, pow_succ]
  obtain ⟨n, hn, hpowone⟩ := he.exists_pow_eq_one
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hcpow : c ^ n = 1 := by
    apply smul_left_injective ℚ hv
    change c ^ n • v = (1 : ℚ) • v
    rw [← hpow, hpowone]
    simp
  have hcfin : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hcpow⟩
  rcases le_total 0 c with hnonneg | hnonpos
  · left
    apply LinearEquiv.ext
    intro v
    simpa [hcfin.eq_one hnonneg] using heval v
  · right
    apply LinearEquiv.ext
    intro v
    simpa [hcfin.eq_neg_one hnonpos] using heval v

variable [LocallyOfFiniteType G.X.hom]

/-- The actual root-span Weyl action in rank at most one acts by a single
global sign. The acting quotient is not assumed to act faithfully. -/
theorem IsSplitTorus.relativeWeylAction_eq_one_or_neg_of_rankOne
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hdep : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (w : relativeWeylGroup i) :
    relativeWeylAction i w = 1 ∨ relativeWeylAction i w = LinearEquiv.neg ℚ := by
  have : FiniteDimensional ℚ (relativeRootSpan i) :=
    FiniteDimensional.span_of_finite ℚ ((hT.finite_relativeRoots i).image toRat)
  have := hT.finite_range_relativeWeylAction i
  let e : (relativeWeylAction i).range := ⟨relativeWeylAction i w, ⟨w, rfl⟩⟩
  have hfin : IsOfFinOrder (relativeWeylAction i w) := by
    obtain ⟨n, hn, hp⟩ := (isOfFinOrder_of_finite e).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val hp⟩
  exact finOrder_linearEquiv_eq_one_or_neg
    (hT.finrank_relativeRootSpan_le_one_of_rankOne i hdep) _ hfin

/-- An encoding of the actual rank-one root-action image by its sign:
`true` denotes the identity, and `false` denotes negation. If the root span
is zero, only `true` occurs. -/
def IsSplitTorus.rankOneRelativeWeylSignEmbedding
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hdep : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) :
    (relativeWeylAction i).range ↪ Bool := by
  classical
  refine ⟨fun e => decide ((e : relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i) = 1), ?_⟩
  intro a b hab
  apply Subtype.ext
  by_cases ha : (a : relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i) = 1
  · have hb : (b : relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i) = 1 := by
      simpa [ha] using hab.symm
    exact ha.trans hb.symm
  · have hb : (b : relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i) ≠ 1 := by
      simpa [ha] using hab.symm
    obtain ⟨w, hw⟩ := a.property
    obtain ⟨z, hz⟩ := b.property
    have ha' := (hT.relativeWeylAction_eq_one_or_neg_of_rankOne i hdep w).resolve_left
      (by simpa [hw] using ha)
    have hb' := (hT.relativeWeylAction_eq_one_or_neg_of_rankOne i hdep z).resolve_left
      (by simpa [hz] using hb)
    exact (hw.symm.trans ha').trans (hz.symm.trans hb').symm

/-- The image of the actual Weyl action on the root span has at most two
elements. Faithfulness is a separate geometric input. -/
theorem IsSplitTorus.card_range_relativeWeylAction_le_two_of_rankOne
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hdep : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) :
    Nat.card (relativeWeylAction i).range ≤ 2 := by
  simpa using Nat.card_le_card_of_injective
    (hT.rankOneRelativeWeylSignEmbedding i hdep)
    (hT.rankOneRelativeWeylSignEmbedding i hdep).injective

end Langlands.GroupScheme
