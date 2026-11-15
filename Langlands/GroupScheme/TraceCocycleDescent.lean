import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.Push

/-! # Trace and cocycle descent for semilinear group actions

Let a group `Δ` act on a group `P`, and let `res : Δ →* Γ` be a homomorphism onto a finite
group `Γ` with a set-theoretic section `s`. Elements fixed by the kernel of `res` behave as if
they were acted on by `Γ`. This module proves two descent statements used for Galois descent at
a finite level:

* `exists_fixed_mul_of_trace_eq_one`: if `e` identifies a `Δ`-stable subgroup `B` of `P`
  semilinearly with an additive subgroup of a module over a ring `L` with a `Δ`-action, and the
  conjugates of an element `θ` of trace one preserve `e(B)`, then every coset `w₀ B`
  that is stable under `Δ` (in the sense `w₀⁻¹ σ(w₀) ∈ B`) and whose base point is fixed by the
  kernel of `res` contains a `Δ`-fixed element. This is the additive Hilbert 90 argument
  `b = ∑_γ γ(θ) z_γ`.
* `sectionNorm`: the norm `∏_γ act (s γ) y` over the chosen lifts.
* `exists_fixed_not_mem_of_dual`: given a semilinear quotient map `q : P →* V` with kernel
  carrying semilinear coordinates `e`, a `Δ`-stable subgroup `A`, a subgroup `Ap`, and a dual
  family `a_j, c_j` with `∑_j a_j γ(c_j) = δ_{γ,1}` whose members preserve `q(A)` and
  `q(Ap)`, an element `u ∈ A` fixed by the kernel of `res` with `q(u) ∉ q(Ap)` yields a
  `Δ`-fixed element `h ∈ A` with `q(h) ∉ q(Ap)`.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.GroupScheme.TraceCocycleDescent

variable {Δ Γ P L : Type*} [Group Δ] [Group Γ] [Group P] [CommRing L] [MulSemiringAction Δ L]

section KernelFixed

variable {X : Type*} [MulAction Δ X] (res : Δ →* Γ) (s : Γ → Δ)

/-- An element fixed by the kernel of `res` is moved by `τ` as by the chosen lift of `res τ`. -/
theorem smul_eq_section_smul (hs : ∀ γ, res (s γ) = γ) {x : X}
    (hx : ∀ k, res k = 1 → k • x = x) (τ : Δ) : τ • x = s (res τ) • x := by
  have hk : res ((s (res τ))⁻¹ * τ) = 1 := by
    rw [map_mul, map_inv, hs, inv_mul_cancel]
  calc τ • x = (s (res τ) * ((s (res τ))⁻¹ * τ)) • x := by rw [mul_inv_cancel_left]
    _ = s (res τ) • x := by rw [mul_smul, hx _ hk]

variable [Fintype Γ] {M : Type*} [AddCommMonoid M] [DistribMulAction Δ M]

/-- The trace over the chosen lifts of an element fixed by the kernel of `res` is fixed. -/
theorem smul_sum_section (hs : ∀ γ, res (s γ) = γ) {m : M}
    (hm : ∀ k, res k = 1 → k • m = m) (σ : Δ) :
    σ • ∑ γ, s γ • m = ∑ γ, s γ • m := by
  rw [Finset.smul_sum]
  have h : ∀ γ, σ • s γ • m = s (res σ * γ) • m := by
    intro γ
    rw [← mul_smul, smul_eq_section_smul res s hs hm, map_mul, hs]
  simp_rw [h]
  exact Fintype.sum_bijective (res σ * ·) (Group.mulLeft_bijective _) _ _ fun _ => rfl

end KernelFixed

section Coboundary

variable [Fintype Γ] {W : Type*} [AddCommGroup W] [Module L W] [DistribMulAction Δ W]

omit [MulSemiringAction Δ L] in
/-- Additive coordinates on a subgroup are injective. -/
theorem eq_of_coord_eq (B : Subgroup P) (e : P → W)
    (he_mul : ∀ x ∈ B, ∀ y ∈ B, e (x * y) = e x + e y)
    (he_inj : ∀ x ∈ B, e x = 0 → x = 1) {x y : P} (hx : x ∈ B) (hy : y ∈ B)
    (h : e x = e y) : x = y := by
  have h1 : e 1 = 0 := by
    have := he_mul 1 B.one_mem 1 B.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : e y⁻¹ = -e y := by
    have := he_mul y hy y⁻¹ (B.inv_mem hy)
    rw [mul_inv_cancel, h1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hxy : e (x * y⁻¹) = 0 := by
    rw [he_mul x hx _ (B.inv_mem hy), hinv, h, add_neg_cancel]
  exact mul_inv_eq_one.mp (he_inj _ (B.mul_mem hx (B.inv_mem hy)) hxy)

/-- **Vanishing of cocycles with a trace-one element.** Let `e` identify a `Δ`-stable subgroup
`B` of `P` semilinearly with an additive subgroup of an `L`-module `W`. If `θ ∈ L` is fixed by
the kernel of `res`, has trace `∑_γ s(γ) θ = 1`, and all its conjugates preserve `e(B)`, then
every `B`-valued cocycle on `Δ` that is trivial on the kernel of `res` is a coboundary. -/
theorem exists_coboundary_of_trace_eq_one
    (hW : ∀ (σ : Δ) (c : L) (w : W), σ • (c • w) = (σ • c) • (σ • w))
    (act : Δ →* MulAut P) (res : Δ →* Γ) (s : Γ → Δ) (hs : ∀ γ, res (s γ) = γ)
    (B : Subgroup P) (hB : ∀ σ, ∀ x ∈ B, act σ x ∈ B)
    (e : P → W) (he_mul : ∀ x ∈ B, ∀ y ∈ B, e (x * y) = e x + e y)
    (he_inj : ∀ x ∈ B, e x = 0 → x = 1)
    (he_act : ∀ σ, ∀ x ∈ B, e (act σ x) = σ • e x)
    (θ : L) (hθfix : ∀ k, res k = 1 → k • θ = θ) (hθ : ∑ γ, s γ • θ = 1)
    (hθB : ∀ σ : Δ, ∀ x ∈ B, ∃ y ∈ B, e y = (σ • θ) • e x)
    (z : Δ → P) (hzB : ∀ σ, z σ ∈ B) (hcoc : ∀ σ τ, z (σ * τ) = z σ * act σ (z τ))
    (hker : ∀ k, res k = 1 → z k = 1) :
    ∃ b ∈ B, ∀ σ, z σ = b * (act σ b)⁻¹ := by
  -- the image `e(B)` is an additive subgroup
  have h1 : e 1 = 0 := by
    have := he_mul 1 B.one_mem 1 B.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hsum : ∀ (t : Finset Γ) (f : Γ → W), (∀ γ ∈ t, ∃ y ∈ B, e y = f γ) →
      ∃ y ∈ B, e y = ∑ γ ∈ t, f γ := by
    intro t f hf
    induction t using Finset.cons_induction with
    | empty => exact ⟨1, B.one_mem, by rw [h1, Finset.sum_empty]⟩
    | cons γ t hγ ih =>
      obtain ⟨y, hy, hye⟩ := hf γ (Finset.mem_cons_self γ t)
      obtain ⟨y', hy', hye'⟩ := ih fun δ hδ => hf δ (Finset.mem_cons_of_mem hδ)
      exact ⟨y * y', B.mul_mem hy hy', by
        rw [he_mul y hy y' hy', hye, hye', Finset.sum_cons]⟩
  -- the cocycle and the conjugates of `θ` only depend on the image in `Γ`
  have hzsec : ∀ τ, z τ = z (s (res τ)) := by
    intro τ
    have hk : res ((s (res τ))⁻¹ * τ) = 1 := by
      rw [map_mul, map_inv, hs, inv_mul_cancel]
    calc z τ = z (s (res τ) * ((s (res τ))⁻¹ * τ)) := by rw [mul_inv_cancel_left]
      _ = z (s (res τ)) := by rw [hcoc, hker _ hk, map_one, mul_one]
  have hθsec : ∀ τ : Δ, τ • θ = s (res τ) • θ := smul_eq_section_smul res s hs hθfix
  obtain ⟨b, hb, hbe⟩ := hsum Finset.univ (fun γ => (s γ • θ) • e (z (s γ)))
    fun γ _ => hθB (s γ) (z (s γ)) (hzB _)
  refine ⟨b, hb, fun σ => ?_⟩
  have hσb : act σ b ∈ B := hB σ b hb
  apply eq_of_coord_eq B e he_mul he_inj (hzB σ) (B.mul_mem hb (B.inv_mem hσb))
  -- coordinates of `σ(b)`
  have hinv : ∀ x ∈ B, e x⁻¹ = -e x := by
    intro x hx
    have := he_mul x hx x⁻¹ (B.inv_mem hx)
    rw [mul_inv_cancel, h1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hcocσ : ∀ τ, σ • e (z τ) = e (z (σ * τ)) - e (z σ) := by
    intro τ
    rw [← he_act σ _ (hzB τ), hcoc, he_mul _ (hzB σ) _ (hB σ _ (hzB τ)), add_sub_cancel_left]
  have hσe : σ • e b = e b - e (z σ) := by
    rw [hbe, Finset.smul_sum]
    have hterm : ∀ γ, σ • ((s γ • θ) • e (z (s γ))) =
        (s (res σ * γ) • θ) • e (z (s (res σ * γ))) - (s (res σ * γ) • θ) • e (z σ) := by
      intro γ
      rw [hW, hcocσ, smul_sub, ← mul_smul, hθsec (σ * s γ), hzsec (σ * s γ), map_mul, hs]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    have hre1 : ∑ γ, (s (res σ * γ) • θ) • e (z (s (res σ * γ))) =
        ∑ γ, (s γ • θ) • e (z (s γ)) :=
      Fintype.sum_bijective (res σ * ·) (Group.mulLeft_bijective _) _ _ fun _ => rfl
    have hre2 : ∑ γ, s (res σ * γ) • θ = ∑ γ, s γ • θ :=
      Fintype.sum_bijective (res σ * ·) (Group.mulLeft_bijective _) _ _ fun _ => rfl
    rw [hre1, hre2, hθ, one_smul]
  rw [he_mul b hb _ (B.inv_mem hσb), hinv _ hσb, he_act σ b hb, hσe]
  abel

/-- **Fixed points in stable cosets.** Under the hypotheses of
`exists_coboundary_of_trace_eq_one`, if `w₀` is fixed by the kernel of `res` and
`w₀⁻¹ σ(w₀) ∈ B` for every `σ`, then some `w₀ b` with `b ∈ B` is fixed by `Δ`. -/
theorem exists_fixed_mul_of_trace_eq_one
    (hW : ∀ (σ : Δ) (c : L) (w : W), σ • (c • w) = (σ • c) • (σ • w))
    (act : Δ →* MulAut P) (res : Δ →* Γ) (s : Γ → Δ) (hs : ∀ γ, res (s γ) = γ)
    (B : Subgroup P) (hB : ∀ σ, ∀ x ∈ B, act σ x ∈ B)
    (e : P → W) (he_mul : ∀ x ∈ B, ∀ y ∈ B, e (x * y) = e x + e y)
    (he_inj : ∀ x ∈ B, e x = 0 → x = 1)
    (he_act : ∀ σ, ∀ x ∈ B, e (act σ x) = σ • e x)
    (θ : L) (hθfix : ∀ k, res k = 1 → k • θ = θ) (hθ : ∑ γ, s γ • θ = 1)
    (hθB : ∀ σ : Δ, ∀ x ∈ B, ∃ y ∈ B, e y = (σ • θ) • e x)
    (w₀ : P) (hw₀ : ∀ k, res k = 1 → act k w₀ = w₀) (hw₀B : ∀ σ, w₀⁻¹ * act σ w₀ ∈ B) :
    ∃ b ∈ B, ∀ σ, act σ (w₀ * b) = w₀ * b := by
  obtain ⟨b, hb, hz⟩ := exists_coboundary_of_trace_eq_one hW act res s hs B hB e he_mul he_inj
    he_act θ hθfix hθ hθB (fun σ => w₀⁻¹ * act σ w₀) hw₀B
    (fun σ τ => by
      simp only [map_mul, MulAut.mul_apply, map_inv, mul_assoc, mul_inv_cancel_left])
    (fun k hk => by rw [hw₀ k hk, inv_mul_cancel])
  refine ⟨b, hb, fun σ => ?_⟩
  have h := hz σ
  rw [map_mul]
  calc act σ w₀ * act σ b = w₀ * (w₀⁻¹ * act σ w₀) * act σ b := by rw [mul_inv_cancel_left]
    _ = w₀ * (b * (act σ b)⁻¹) * act σ b := by rw [h]
    _ = w₀ * b := by rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

end Coboundary

section SectionNorm

variable [Fintype Γ]

/-- The norm of `y` over the chosen lifts `s γ`: the product of the elements `act (s γ) y` for
`γ : Γ`, taken in the order of `Finset.univ.toList`. -/
def sectionNorm (act : Δ →* MulAut P) (s : Γ → Δ) (y : P) : P :=
  ((Finset.univ : Finset Γ).toList.map fun γ => act (s γ) y).prod

omit [Group Γ] in
/-- The norm of an element of a `Δ`-stable subgroup lies in the subgroup. -/
theorem sectionNorm_mem (act : Δ →* MulAut P) (s : Γ → Δ) (A : Subgroup P)
    (hA : ∀ σ, ∀ x ∈ A, act σ x ∈ A) {y : P} (hy : y ∈ A) : sectionNorm act s y ∈ A := by
  apply Subgroup.list_prod_mem
  intro w hw
  obtain ⟨γ, -, rfl⟩ := List.mem_map.mp hw
  exact hA _ y hy

omit [Group Γ] in
/-- Under a homomorphism to an additive group, the norm becomes the sum of the conjugates. -/
theorem toAdd_sectionNorm {V : Type*} [AddCommGroup V] (act : Δ →* MulAut P) (s : Γ → Δ)
    (q : P →* Multiplicative V) (y : P) :
    (q (sectionNorm act s y)).toAdd = ∑ γ, (q (act (s γ) y)).toAdd := by
  simp only [sectionNorm, map_list_prod, List.map_map]
  rw [Finset.prod_map_toList, toAdd_prod]
  rfl

/-- The norm of an element fixed by the kernel of `res` is fixed by the kernel of `res`. -/
theorem sectionNorm_fixed (act : Δ →* MulAut P) (res : Δ →* Γ) (s : Γ → Δ) {y : P}
    (hy : ∀ k, res k = 1 → act k y = y) (k : Δ) (hk : res k = 1) :
    act k (sectionNorm act s y) = sectionNorm act s y := by
  simp only [sectionNorm, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun γ _ => ?_
  simp only [Function.comp_apply, ← MulAut.mul_apply, ← map_mul]
  have hk' : res ((s γ)⁻¹ * k * s γ) = 1 := by
    rw [map_mul, map_mul, map_inv, hk, mul_one, inv_mul_cancel]
  calc act (k * s γ) y = act (s γ * ((s γ)⁻¹ * k * s γ)) y := by group
    _ = act (s γ) y := by rw [map_mul, MulAut.mul_apply, hy _ hk']

end SectionNorm

section Norm

variable [Fintype Γ] {V W : Type*} [AddCommGroup V] [Module L V] [DistribMulAction Δ V]
  [AddCommGroup W] [Module L W] [DistribMulAction Δ W]

/-- **Norm descent with a dual family.** Let `q : P →* V` be a semilinear quotient map whose
kernel carries semilinear coordinates `e`, `A` a `Δ`-stable subgroup and `Ap` a subgroup of
`P`. Suppose `a_j, c_j ∈ L` satisfy `∑_j a_j s(γ)(c_j) = δ_{γ,1}`, every `a_j` preserves
`q(Ap)`, every `c_j` preserves the image under `q` of the elements of `A` fixed by the kernel
of `res`, and a trace-one `θ` as in `exists_fixed_mul_of_trace_eq_one` preserves
`e(A ∩ ker q)`. Then an element `u ∈ A` fixed by the kernel of `res` with `q(u) ∉ q(Ap)`
yields a `Δ`-fixed `h ∈ A` with `q(h) ∉ q(Ap)`. -/
theorem exists_fixed_not_mem_of_dual [DecidableEq Γ]
    (hV : ∀ (σ : Δ) (c : L) (v : V), σ • (c • v) = (σ • c) • (σ • v))
    (hW : ∀ (σ : Δ) (c : L) (w : W), σ • (c • w) = (σ • c) • (σ • w))
    (act : Δ →* MulAut P) (res : Δ →* Γ) (s : Γ → Δ) (hs : ∀ γ, res (s γ) = γ)
    (q : P →* Multiplicative V)
    (hq : ∀ σ x, (q (act σ x)).toAdd = σ • (q x).toAdd)
    (e : P → W) (he_mul : ∀ x y, q x = 1 → q y = 1 → e (x * y) = e x + e y)
    (he_inj : ∀ x, q x = 1 → e x = 0 → x = 1)
    (he_act : ∀ σ x, q x = 1 → e (act σ x) = σ • e x)
    (A Ap : Subgroup P) (hA : ∀ σ, ∀ x ∈ A, act σ x ∈ A)
    (n : ℕ) (a c : Fin n → L)
    (hac : ∀ γ : Γ, ∑ j, a j * s γ • c j = if γ = 1 then 1 else 0)
    (ha : ∀ j, ∀ x ∈ Ap, ∃ y ∈ Ap, (q y).toAdd = a j • (q x).toAdd)
    (hc : ∀ j, ∀ x ∈ A, (∀ k, res k = 1 → act k x = x) →
      ∃ y ∈ A, (∀ k, res k = 1 → act k y = y) ∧ (q y).toAdd = c j • (q x).toAdd)
    (θ : L) (hθfix : ∀ k, res k = 1 → k • θ = θ) (hθ : ∑ γ, s γ • θ = 1)
    (hθA : ∀ σ : Δ, ∀ x ∈ A, q x = 1 → ∃ y ∈ A, q y = 1 ∧ e y = (σ • θ) • e x)
    (u : P) (huA : u ∈ A) (hufix : ∀ k, res k = 1 → act k u = u)
    (hu : ∀ y ∈ Ap, q y ≠ q u) :
    ∃ h ∈ A, (∀ σ, act σ h = h) ∧ ∀ y ∈ Ap, q y ≠ q h := by
  classical
  set x := (q u).toAdd with hx
  -- the image of a fixed point of the kernel is fixed by the kernel
  have hfixq : ∀ y, (∀ k, res k = 1 → act k y = y) → ∀ k, res k = 1 → k • (q y).toAdd = (q y).toAdd :=
    fun y hy k hk => by rw [← hq, hy k hk]
  -- sums of images of `Ap`
  have hsumAp : ∀ (t : Finset (Fin n)) (f : Fin n → V), (∀ j ∈ t, ∃ y ∈ Ap, (q y).toAdd = f j) →
      ∃ y ∈ Ap, (q y).toAdd = ∑ j ∈ t, f j := by
    intro t f hf
    induction t using Finset.cons_induction with
    | empty => exact ⟨1, Ap.one_mem, by simp⟩
    | cons j t hj ih =>
      obtain ⟨y, hy, hye⟩ := hf j (Finset.mem_cons_self j t)
      obtain ⟨y', hy', hye'⟩ := ih fun i hi => hf i (Finset.mem_cons_of_mem hi)
      exact ⟨y * y', Ap.mul_mem hy hy', by
        rw [map_mul, toAdd_mul, hye, hye', Finset.sum_cons]⟩
  -- `x = ∑_j a_j • Tr(c_j • x)`
  have hdecomp : x = ∑ j, a j • ∑ γ, s γ • (c j • x) := by
    have hx1 : s 1 • x = x := hfixq u hufix _ (hs 1)
    simp_rw [Finset.smul_sum, hV, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hac]
    simp [hx1]
  -- some trace `Tr(c_j • x)` is not in `q(Ap)`
  obtain ⟨j, hj⟩ : ∃ j, ∀ y ∈ Ap, (q y).toAdd ≠ ∑ γ, s γ • (c j • x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hye⟩ := hsumAp Finset.univ (fun j => a j • ∑ γ, s γ • (c j • x))
      fun j _ => by
        obtain ⟨y, hy, hye⟩ := hcon j
        obtain ⟨y', hy', hye'⟩ := ha j y hy
        exact ⟨y', hy', by rw [hye', hye]⟩
    apply hu y hy
    apply Multiplicative.toAdd.injective
    rw [hye, ← hdecomp]
  -- the norm of a lift of `c_j • x`
  obtain ⟨y, hyA, hyfix, hye⟩ := hc j u huA hufix
  set N : P := sectionNorm act s y with hN
  have hNA : N ∈ A := sectionNorm_mem act s A hA hyA
  have hqN : (q N).toAdd = ∑ γ, s γ • (c j • x) := by
    rw [hN, toAdd_sectionNorm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [hq, hye]
  have hNfix : ∀ k, res k = 1 → act k N = N := sectionNorm_fixed act res s hyfix
  -- the defect of `N` lies in `A ∩ ker q`
  let B : Subgroup P := A ⊓ q.ker
  have hNB : ∀ σ, N⁻¹ * act σ N ∈ B := by
    intro σ
    refine ⟨A.mul_mem (A.inv_mem hNA) (hA σ N hNA), ?_⟩
    change q (N⁻¹ * act σ N) = 1
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hq, hqN,
      smul_sum_section res s hs (fun k hk => by rw [← hye, hfixq y hyfix k hk]) σ,
      neg_add_cancel, toAdd_one]
  obtain ⟨b, hb, hfix⟩ := exists_fixed_mul_of_trace_eq_one hW act res s hs B
    (fun σ w hw => ⟨hA σ w hw.1, by
      change q (act σ w) = 1
      apply Multiplicative.toAdd.injective
      rw [hq, show q w = 1 from hw.2, toAdd_one, smul_zero]⟩)
    e (fun w hw w' hw' => he_mul w w' hw.2 hw'.2) (fun w hw => he_inj w hw.2)
    (fun σ w hw => he_act σ w hw.2) θ hθfix hθ
    (fun σ w hw => by
      obtain ⟨w', hw'A, hw'q, hw'e⟩ := hθA σ w hw.1 hw.2
      exact ⟨w', ⟨hw'A, hw'q⟩, hw'e⟩)
    N hNfix hNB
  refine ⟨N * b, A.mul_mem hNA hb.1, hfix, fun y' hy' => ?_⟩
  have hqb : q b = 1 := hb.2
  rw [map_mul, hqb, mul_one]
  intro heq
  exact hj y' hy' (by rw [heq, hqN])

end Norm

end Langlands.GroupScheme.TraceCocycleDescent
