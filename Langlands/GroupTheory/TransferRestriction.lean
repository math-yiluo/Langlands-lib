import Mathlib.GroupTheory.Transfer
import Mathlib.Tactic.Group

/-! # Restriction of the transfer along a homomorphism

Let `A` be a normal subgroup of finite index of `G` and let `ι : G' → G` be a homomorphism
whose range contains `A`; put `A' = ι⁻¹(A)`. The transfer of `ϕ : A → M` at `ι h` is the
product, over the cosets `q` of the range of `ι`, of the transfers to `A'` of `ϕ` composed
with conjugation by a representative of `q`. -/

noncomputable section

namespace Langlands.GroupTheory.Transfer

open Subgroup Subgroup.leftTransversals MulAction
open scoped Pointwise

variable {G G' : Type*} [Group G] [Group G'] {M : Type*} [CommGroup M]
  {A : Subgroup G} {A' : Subgroup G'}

/-- For a homomorphism `ι : G' → G` mapping `A'` into the normal subgroup `A`, the
homomorphism `A' → A`, `a ↦ w * ι a * w⁻¹`. -/
def conjComap [hA : A.Normal] (ι : G' →* G) (hι : ∀ x ∈ A', ι x ∈ A) (w : G) : A' →* A where
  toFun a := ⟨w * ι a * w⁻¹, hA.conj_mem _ (hι a a.2) w⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

@[simp] theorem coe_conjComap [A.Normal] (ι : G' →* G) (hι : ∀ x ∈ A', ι x ∈ A) (w : G)
    (a : A') : (conjComap ι hι w a : G) = w * ι a * w⁻¹ := rfl

/-- Restriction of the transfer along a homomorphism. Let `A` be a normal subgroup of finite
index of `G`, let `ι : G' → G` be a homomorphism whose range contains `A`, and let `A'` be the
inverse image of `A`. Then the transfer of `ϕ : A → M` at `ι h` is the product, over the
cosets `q` of the range of `ι`, of the transfers to `A'` of `ϕ` composed with the conjugation
`a ↦ q.out * ι a * q.out⁻¹`. -/
theorem transfer_apply_eq_prod [hA : A.Normal] [A.FiniteIndex] [A'.FiniteIndex]
    (ι : G' →* G) (hι : ∀ x, x ∈ A' ↔ ι x ∈ A) (hAι : A ≤ ι.range)
    [Fintype (G ⧸ ι.range)] (ϕ : A →* M) (h : G') :
    MonoidHom.transfer ϕ (ι h) =
      ∏ q : G ⧸ ι.range,
        MonoidHom.transfer (ϕ.comp (conjComap ι (fun x => (hι x).mp) q.out)) h := by
  classical
  let _ := A.fintypeQuotientOfFiniteIndex
  let _ := A'.fintypeQuotientOfFiniteIndex
  let T' : A'.LeftTransversal := default
  let t' : G' ⧸ A' → G' := fun r => (T'.2.leftQuotientEquiv r : G')
  have ht' : ∀ r, (QuotientGroup.mk (t' r) : G' ⧸ A') = r :=
    T'.2.quotientGroupMk_leftQuotientEquiv
  let e : (G ⧸ ι.range) × (G' ⧸ A') → G ⧸ A :=
    fun x => QuotientGroup.mk (ι (t' x.2) * x.1.out⁻¹)
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨q₁, r₁⟩ ⟨q₂, r₂⟩ heq
      have hx := QuotientGroup.eq.mp heq
      have hx' := hA.conj_mem _ hx q₁.out⁻¹
      obtain ⟨y, hy⟩ := hAι hx'
      have hq : q₁ = q₂ := by
        rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
        refine QuotientGroup.eq.mpr (MonoidHom.mem_range.mpr ⟨(t' r₁ * y)⁻¹ * t' r₂, ?_⟩)
        rw [map_mul, map_inv, map_mul, hy]
        group
      subst hq
      have hz : ι ((t' r₁)⁻¹ * t' r₂) ∈ A := by
        convert hx' using 1
        simp only [map_mul, map_inv]
        group
      have hr := QuotientGroup.eq.mpr ((hι _).mpr hz)
      rw [ht', ht'] at hr
      rw [hr]
    · intro p
      induction p using QuotientGroup.induction_on with
      | H g =>
        let q : G ⧸ ι.range := QuotientGroup.mk g⁻¹
        have hq : g * q.out ∈ ι.range := by
          have := ι.range.inv_mem (QuotientGroup.eq.mp (QuotientGroup.out_eq' q))
          simpa using this
        obtain ⟨y, hy⟩ := hq
        refine ⟨(q, QuotientGroup.mk y), QuotientGroup.eq.mpr ?_⟩
        have hm : ι ((t' (QuotientGroup.mk y))⁻¹ * y) ∈ A :=
          (hι _).mp (QuotientGroup.eq.mp (ht' _))
        convert hA.conj_mem _ hm q.out using 1
        rw [eq_mul_inv_of_mul_eq hy.symm]
        simp only [map_mul, map_inv]
        group
  let eq := Equiv.ofBijective e he
  let f : G ⧸ A → G := fun p => ι (t' (eq.symm p).2) * (eq.symm p).1.out⁻¹
  have hf : ∀ p, (QuotientGroup.mk (f p) : G ⧸ A) = p := fun p => eq.apply_symm_apply p
  let S : A.LeftTransversal := ⟨Set.range f, isComplement_range_left hf⟩
  have hS : ∀ p, (S.2.leftQuotientEquiv p : G) = f p :=
    IsComplement.leftQuotientEquiv_apply hf
  have hfe : ∀ x, f (e x) = ι (t' x.2) * x.1.out⁻¹ := fun x => by
    simp only [f, show eq.symm (e x) = x from eq.symm_apply_apply x]
  have hsmul : ∀ x : (G ⧸ ι.range) × (G' ⧸ A'),
      (ι h)⁻¹ • e x = e (x.1, h⁻¹ • x.2) := by
    rintro ⟨q, r⟩
    refine QuotientGroup.eq.mpr ?_
    have hm : ι ((h⁻¹ * t' r)⁻¹ * t' (h⁻¹ • r)) ∈ A := by
      refine (hι _).mp (QuotientGroup.eq.mp ?_)
      rw [ht']
      conv_rhs => rw [← ht' r]
      rfl
    convert hA.conj_mem _ hm q.out using 1
    simp only [smul_eq_mul, map_mul, map_inv]
    group
  rw [MonoidHom.transfer_def ϕ S]
  simp only [diff]
  rw [Finset.prod_congr rfl fun q _ => MonoidHom.transfer_def _ T' h]
  simp only [diff]
  rw [← Fintype.prod_prod_type']
  refine (Fintype.prod_bijective e he _ _ fun x => ?_).symm
  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  dsimp only [coe_conjComap]
  rw [hS, smul_apply_eq_smul_apply_inv_smul, smul_apply_eq_smul_apply_inv_smul,
    hS, hsmul, hfe, hfe]
  simp only [smul_eq_mul, map_mul, map_inv, t']
  group

end Langlands.GroupTheory.Transfer
