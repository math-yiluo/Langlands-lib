import Langlands.Global.LeftCosetSpace
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Group

/-! # Regrouping finitely supported sums over nested subgroups -/

noncomputable section

open scoped Classical

namespace Langlands.Global.ArthurTruncation

universe u

variable {A : Type u} [Group A]

/-- The cosets of `L ∩ M` in `M`, written using subgroups of the same ambient group. -/
abbrev NestedCosets (L M : Subgroup A) := LeftCosetSpace (L.subgroupOf M)

private theorem out_mul_inv_mem (L M : Subgroup A) (x : M) :
    ((LeftCosetSpace.mk (L.subgroupOf M) x).out : A) * (x : A)⁻¹ ∈ L :=
  (LeftCosetSpace.mk_eq_mk_iff (L.subgroupOf M) _ _).mp (Quotient.out_eq _).symm

private theorem out_mul_inv_mem' (L : Subgroup A) (x : A) :
    (LeftCosetSpace.mk L x).out * x⁻¹ ∈ L :=
  (LeftCosetSpace.mk_eq_mk_iff L _ _).mp (Quotient.out_eq _).symm

/-- The inclusion of the relative cosets in the full coset space. -/
def nestedCosetsEmbedding (L M : Subgroup A) : NestedCosets L M ↪ LeftCosetSpace L where
  toFun := Quotient.map' (fun x : M => (x : A)) fun _ _ h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    exact h
  inj' := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      intro h
      apply Quotient.sound
      change QuotientGroup.rightRel (L.subgroupOf M) x y
      have hxy : QuotientGroup.rightRel L (x : A) (y : A) := Quotient.exact h
      rw [QuotientGroup.rightRel_apply] at hxy ⊢
      exact hxy

theorem nestedCosetsEmbedding_apply (L M : Subgroup A) (c : NestedCosets L M) :
    nestedCosetsEmbedding L M c = LeftCosetSpace.mk L (c.out : A) := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- At the full upper subgroup the inclusion of coset spaces is an equivalence. -/
def nestedCosetsEquivOfTop (L M : Subgroup A) (hM : M = ⊤) :
    NestedCosets L M ≃ LeftCosetSpace L :=
  Equiv.ofBijective (nestedCosetsEmbedding L M) ⟨(nestedCosetsEmbedding L M).injective, by
    intro c
    refine ⟨LeftCosetSpace.mk _ ⟨c.out, hM.symm ▸ Subgroup.mem_top _⟩, ?_⟩
    exact Quotient.out_eq c⟩

/-- Evaluation of an invariant function can use a representative of the relative coset. -/
theorem nestedCosetsEmbedding_out (L M : Subgroup A) {E : Type*} {f : A → E}
    (hf : ∀ g ∈ L, ∀ z, f (g * z) = f z) (c : NestedCosets L M) :
    f (nestedCosetsEmbedding L M c).out = f (c.out : A) := by
  rw [nestedCosetsEmbedding_apply]
  simpa only [inv_mul_cancel_right] using hf _ (out_mul_inv_mem' L (c.out : A)) (c.out : A)

/-- Right multiplication permutes a relative coset space and its invariant summands. -/
theorem tsum_nestedCosets_mul_right (L M : Subgroup A) (a : M)
    (f : A → ℂ) (hf : ∀ b ∈ L, ∀ z, f (b * z) = f z) :
    (∑' c : NestedCosets L M, f ((c.out : A) * (a : A))) =
      ∑' c : NestedCosets L M, f (c.out : A) := by
  let Γ := L.subgroupOf M
  let E : NestedCosets L M ≃ NestedCosets L M :=
    ⟨LeftCosetSpace.rightTranslate Γ a, LeftCosetSpace.rightTranslate Γ a⁻¹,
      fun c => by rw [LeftCosetSpace.rightTranslate_mul, mul_inv_cancel, LeftCosetSpace.rightTranslate_one],
      fun c => by rw [LeftCosetSpace.rightTranslate_mul, inv_mul_cancel, LeftCosetSpace.rightTranslate_one]⟩
  rw [← E.tsum_eq (fun c : NestedCosets L M => f (c.out : A))]
  refine tsum_congr fun c => ?_
  have he : E c = LeftCosetSpace.mk Γ (c.out * a) := by
    change LeftCosetSpace.rightTranslate Γ a c = _
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [he]
  simpa only [inv_mul_cancel_right, Subgroup.coe_mul] using
    (hf _ (out_mul_inv_mem L M (c.out * a)) ((c.out : A) * (a : A))).symm

private def cosetProduct (L M N : Subgroup A) (hMN : M ≤ N)
    (x : Σ _ : NestedCosets M N, NestedCosets L M) : NestedCosets L N :=
  LeftCosetSpace.mk _ (Subgroup.inclusion hMN x.2.out * x.1.out)

private theorem cosetProduct_bijective (L M N : Subgroup A) (hLM : L ≤ M) (hMN : M ≤ N) :
    Function.Bijective (cosetProduct L M N hMN) := by
  constructor
  · rintro ⟨c, d⟩ ⟨c', d'⟩ h
    have hL : (((d'.out : M) : A) * (c'.out : N)) *
        ((((d.out : M) : A) * (c.out : N)))⁻¹ ∈ L :=
      (LeftCosetSpace.mk_eq_mk_iff (L.subgroupOf N) _ _).mp h
    have hM : (c'.out : A) * (c.out : A)⁻¹ ∈ M := by
      have hh := M.mul_mem (M.mul_mem (M.inv_mem d'.out.2) (hLM hL)) d.out.2
      convert hh using 1
      group
    have hc₀ := (LeftCosetSpace.mk_eq_mk_iff (M.subgroupOf N) c.out c'.out).mpr hM
    have hc : c = c' := (Quotient.out_eq c).symm.trans (hc₀.trans (Quotient.out_eq c'))
    subst c'
    have hd : (d'.out : A) * (d.out : A)⁻¹ ∈ L := by
      convert hL using 1
      group
    have hd' := (LeftCosetSpace.mk_eq_mk_iff (L.subgroupOf M) d.out d'.out).mpr hd
    exact congrArg (Sigma.mk c) ((Quotient.out_eq d).symm.trans (hd'.trans (Quotient.out_eq d')))
  · intro e
    let c : NestedCosets M N := LeftCosetSpace.mk _ e.out
    let x : M := ⟨(e.out : A) * (c.out : A)⁻¹, by
      have h : (c.out : A) * (e.out : A)⁻¹ ∈ M := out_mul_inv_mem M N e.out
      simpa only [mul_inv_rev, inv_inv] using M.inv_mem h⟩
    let d : NestedCosets L M := LeftCosetSpace.mk _ x
    refine ⟨⟨c, d⟩, ?_⟩
    conv_rhs => rw [← Quotient.out_eq e]
    symm
    apply (LeftCosetSpace.mk_eq_mk_iff (L.subgroupOf N) _ _).mpr
    change ((d.out : A) * (c.out : A)) * (e.out : A)⁻¹ ∈ L
    have h : (d.out : A) * (x : A)⁻¹ ∈ L := out_mul_inv_mem L M x
    change (d.out : A) * ((e.out : A) * (c.out : A)⁻¹)⁻¹ ∈ L at h
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h

set_option maxHeartbeats 550000 in
/-- Multiplication of representatives bijects the two stages of nested cosets with the
single quotient. A finitely supported double sum therefore equals the regrouped sum. -/
theorem tsum_nestedCosets (L M N : Subgroup A) (hLM : L ≤ M) (hMN : M ≤ N)
    (f g : A → ℂ) (hf : ∀ a ∈ L, ∀ z, f (a * z) = f z)
    (hg : ∀ a ∈ M, ∀ z, g (a * z) = g z)
    (hgfin : (Function.support fun c : NestedCosets M N => g (c.out : A)).Finite)
    (hffin : ∀ c : NestedCosets M N,
      (Function.support fun d : NestedCosets L M => f ((d.out : A) * (c.out : A))).Finite) :
    (Function.support fun e : NestedCosets L N => f (e.out : A) * g (e.out : A)).Finite ∧
    (∑' c : NestedCosets M N, (∑' d : NestedCosets L M, f ((d.out : A) * (c.out : A))) *
      g (c.out : A)) = ∑' e : NestedCosets L N, f (e.out : A) * g (e.out : A) := by
  let E := Equiv.ofBijective (cosetProduct L M N hMN) (cosetProduct_bijective L M N hLM hMN)
  let w (z : Σ _ : NestedCosets M N, NestedCosets L M) :=
    f ((z.2.out : A) * (z.1.out : A)) * g (z.1.out : A)
  let v (e : NestedCosets L N) := f (e.out : A) * g (e.out : A)
  have hfin : w.support.Finite := by
    apply (hgfin.toFinset.sigma fun c => (hffin c).toFinset).finite_toSet.subset
    intro ⟨c, d⟩ hz
    change f ((d.out : A) * (c.out : A)) * g (c.out : A) ≠ 0 at hz
    exact Finset.mem_sigma.mpr ⟨hgfin.mem_toFinset.mpr (right_ne_zero_of_mul hz),
      (hffin _).mem_toFinset.mpr (left_ne_zero_of_mul hz)⟩
  have he : v ∘ E = w := by
    funext ⟨c, d⟩
    let x := Subgroup.inclusion hMN d.out * c.out
    have h := out_mul_inv_mem L N x
    have hfe := hf _ h (x : A)
    have hge := hg _ (hLM h) (x : A)
    simp only [inv_mul_cancel_right] at hfe hge
    change f ((LeftCosetSpace.mk (L.subgroupOf N) x).out : A) *
      g ((LeftCosetSpace.mk (L.subgroupOf N) x).out : A) = _
    rw [hfe, hge]
    exact congrArg (f (x : A) * ·) (hg _ d.out.2 (c.out : A))
  refine ⟨?_, ?_⟩
  · apply (hfin.image E).subset
    intro e he'
    exact ⟨E.symm e, by
      change w (E.symm e) ≠ 0
      rw [← he, Function.comp_apply, E.apply_symm_apply]
      exact he', E.apply_symm_apply e⟩
  · change _ = ∑' e, v e
    rw [← E.tsum_eq v, show (fun z => v (E z)) = w from he]
    have hs (c : NestedCosets M N) : Summable (fun d : NestedCosets L M => w ⟨c, d⟩) :=
      (summable_of_hasFiniteSupport (hffin c)).mul_right (g (c.out : A))
    rw [(summable_of_hasFiniteSupport hfin).tsum_sigma' hs]
    refine tsum_congr fun c => ?_
    change (∑' d : NestedCosets L M, f ((d.out : A) * (c.out : A))) * g (c.out : A) =
      ∑' d : NestedCosets L M, f ((d.out : A) * (c.out : A)) * g (c.out : A)
    exact tsum_mul_right.symm

end Langlands.Global.ArthurTruncation
