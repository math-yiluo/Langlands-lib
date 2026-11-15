import Langlands.GroupScheme.TraceCocycleDescent
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Algebra.Equiv

/-! # Descent of filtration jumps through semilinear coordinates

Let a group `Δ` act on a group `H`, preserving a subgroup `U`, and let `ψ : H → Λ` be a function
to a linear order. Assume `ψ` is ultrametric on `U` and `Δ`-invariant. Fix a threshold `r`. Write
`A = {x ∈ U | r ≤ ψ x}`, `A₊ = {x ∈ U | r < ψ x}`, and let `U₂` be a subgroup. This module proves
that a jump `u ∈ A ∖ A₊ U₂` that is fixed by the kernel of a homomorphism `res : Δ →* Γ` onto a
finite group can be replaced by a `Δ`-fixed jump. The data needed are:

* semilinear coordinates `q` on `U` with kernel `U₂` and `e` on `U₂`
  (`exists_fixed_not_mem_mul`), together with a dual family and a trace-one element whose
  members preserve the relevant coordinate images; or
* (`exists_fixed_not_mem_mul_of_subring`) a ring `R` with a map `ι : R →+* L`, a `Γ`-action on
  `R` compatible with `res`, and the guarantee that every `Γ`-stable subring of `R` containing
  all squares of units contains a dual family and a trace-one element. Squares of units must act
  on the coordinate images through elements `τ ∈ H` that are fixed by the kernel of `res`,
  normalize `U`, and preserve `ψ`.

The proofs reduce to `TraceCocycleDescent.exists_fixed_not_mem_of_dual`, applied to the
subgroup `U` with the restricted action.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Langlands.GroupScheme.FilteredTraceDescent

open TraceCocycleDescent

section Restrict

variable {Δ H : Type*} [Group Δ] [Group H]

/-- The action of `Δ` on a stable subgroup `U`. -/
def restrictAct (act : Δ →* MulAut H) (U : Subgroup H) (hU : ∀ σ, ∀ x ∈ U, act σ x ∈ U) :
    Δ →* MulAut U where
  toFun σ :=
    { toFun := fun x => ⟨act σ (x : H), hU σ x x.2⟩
      invFun := fun x => ⟨act σ⁻¹ (x : H), hU σ⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext (by
        change act σ⁻¹ (act σ (x : H)) = x
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun x => Subtype.ext (by
        change act σ (act σ⁻¹ (x : H)) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun x y => Subtype.ext (map_mul (act σ) (x : H) y) }
  map_one' := by
    ext x
    change act 1 (x : H) = x
    rw [map_one, MulAut.one_apply]
  map_mul' σ τ := by
    ext x
    change act (σ * τ) (x : H) = act σ (act τ (x : H))
    rw [map_mul, MulAut.mul_apply]

@[simp] theorem coe_restrictAct (act : Δ →* MulAut H) (U : Subgroup H)
    (hU : ∀ σ, ∀ x ∈ U, act σ x ∈ U) (σ : Δ) (x : U) :
    ((restrictAct act U hU σ x : U) : H) = act σ x :=
  rfl

end Restrict

section Additive

variable {H V : Type*} [Group H] [AddCommGroup V]

/-- A map that is additive on a subgroup sends `1` to `0`. -/
theorem map_one_eq_zero (U : Subgroup H) (q : H → V)
    (hq : ∀ x ∈ U, ∀ y ∈ U, q (x * y) = q x + q y) : q 1 = 0 := by
  have h := hq 1 U.one_mem 1 U.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

/-- A map that is additive on a subgroup sends inverses to negatives. -/
theorem map_inv_eq_neg (U : Subgroup H) (q : H → V)
    (hq : ∀ x ∈ U, ∀ y ∈ U, q (x * y) = q x + q y) {x : H} (hx : x ∈ U) :
    q x⁻¹ = -q x := by
  have h := hq x hx x⁻¹ (U.inv_mem hx)
  rw [mul_inv_cancel, map_one_eq_zero U q hq] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- The image of a subgroup `B ≤ U` under a map that is additive on `U`, as an additive
subgroup. -/
def imageAddSubgroup (U B : Subgroup H) (hB : B ≤ U) (q : H → V)
    (hq : ∀ x ∈ U, ∀ y ∈ U, q (x * y) = q x + q y) : AddSubgroup V where
  carrier := q '' B
  zero_mem' := ⟨1, B.one_mem, map_one_eq_zero U q hq⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, B.mul_mem hx hy, hq x (hB hx) y (hB hy)⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, B.inv_mem hx, map_inv_eq_neg U q hq (hB hx)⟩

theorem mem_imageAddSubgroup (U B : Subgroup H) (hB : B ≤ U) (q : H → V)
    (hq : ∀ x ∈ U, ∀ y ∈ U, q (x * y) = q x + q y) (v : V) :
    v ∈ imageAddSubgroup U B hB q hq ↔ ∃ x ∈ B, q x = v :=
  Iff.rfl

end Additive

section Stabilizer

variable {R L V : Type*} [CommRing R] [CommRing L] [AddCommGroup V] [Module L V]

/-- The elements `r` of `R` such that `ι r` preserves an additive subgroup `X` of an
`L`-module. -/
def stabilizer (ι : R →+* L) (X : AddSubgroup V) : Subring R where
  carrier := {r | ∀ x ∈ X, ι r • x ∈ X}
  mul_mem' := by
    intro r t hr ht x hx
    rw [map_mul, mul_smul]
    exact hr _ (ht x hx)
  one_mem' := by
    intro x hx
    rwa [map_one, one_smul]
  add_mem' := by
    intro r t hr ht x hx
    rw [map_add, add_smul]
    exact X.add_mem (hr x hx) (ht x hx)
  zero_mem' := by
    intro x _
    rw [map_zero, zero_smul]
    exact X.zero_mem
  neg_mem' := by
    intro r hr x hx
    rw [map_neg, neg_smul]
    exact X.neg_mem (hr x hx)

theorem mem_stabilizer (ι : R →+* L) (X : AddSubgroup V) (r : R) :
    r ∈ stabilizer ι X ↔ ∀ x ∈ X, ι r • x ∈ X :=
  Iff.rfl

/-- If `X` is stable under a semilinear `σ` and its inverse, and `ι r' = σ (ι r)`, then `r'`
stabilizes `X` whenever `r` does. -/
theorem mem_stabilizer_of_smul {Δ : Type*} [Group Δ] [MulSemiringAction Δ L]
    [DistribMulAction Δ V] (hV : ∀ (σ : Δ) (c : L) (v : V), σ • (c • v) = (σ • c) • (σ • v))
    (ι : R →+* L) (X : AddSubgroup V) (hX : ∀ σ : Δ, ∀ x ∈ X, σ • x ∈ X) (σ : Δ) {r r' : R}
    (h : ι r' = σ • ι r) (hr : r ∈ stabilizer ι X) : r' ∈ stabilizer ι X := by
  intro x hx
  have hmem : σ • (ι r • (σ⁻¹ • x)) ∈ X := hX σ _ (hr _ (hX σ⁻¹ x hx))
  rwa [hV, smul_inv_smul, ← h] at hmem

end Stabilizer

section Descent

variable {Δ Γ H L Λ : Type*} [Group Δ] [Group Γ] [Fintype Γ] [DecidableEq Γ] [Group H]
  [CommRing L] [MulSemiringAction Δ L] [LinearOrder Λ]

omit [Fintype Γ] [DecidableEq Γ] in
/-- Coordinatewise semilinearity of the `Δ`-action on `L^n`. -/
theorem pi_smul_smul (n : ℕ) (σ : Δ) (c : L) (v : Fin n → L) :
    σ • (c • v) = (σ • c) • (σ • v) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, smul_mul']

/-- **Fixed jumps from semilinear coordinates.** Let `Δ` act on `H` preserving `U`, let
`q : H → L^n` be additive on `U` with kernel `U₂` there, and `e : H → L^m` additive and
injective on `U₂`, both `Δ`-equivariant. Let `ψ : H → Λ` be ultrametric and `Δ`-invariant on
`U`, with `r < ψ 1`. Suppose a dual family `a_j, c_j` and a trace-one `θ` preserve the relevant
images. Then an element `u ∈ U` with `r ≤ ψ u`, fixed by the kernel of `res`, and outside
`{x ∈ U | r < ψ x} · U₂`, yields a `Δ`-fixed element `h` with the same three properties. -/
theorem exists_fixed_not_mem_mul
    (act : Δ →* MulAut H) (res : Δ →* Γ) (s : Γ → Δ) (hs : ∀ γ, res (s γ) = γ)
    (U U₂ : Subgroup H) (hU : ∀ σ, ∀ x ∈ U, act σ x ∈ U)
    {n m : ℕ} (q : H → Fin n → L) (e : H → Fin m → L)
    (hq_mul : ∀ x ∈ U, ∀ y ∈ U, q (x * y) = q x + q y)
    (hq_ker : ∀ x ∈ U, q x = 0 ↔ x ∈ U₂)
    (he_mul : ∀ x ∈ U₂, ∀ y ∈ U₂, e (x * y) = e x + e y)
    (he_inj : ∀ x ∈ U₂, e x = 0 → x = 1)
    (hq_act : ∀ σ, ∀ x ∈ U, q (act σ x) = σ • q x)
    (he_act : ∀ σ, ∀ x ∈ U₂, e (act σ x) = σ • e x)
    (ψ : H → Λ) (r : Λ)
    (hψ_min : ∀ g ∈ U, ∀ h ∈ U, min (ψ g) (ψ h) ≤ ψ (g * h⁻¹))
    (hψ_act : ∀ σ, ∀ g ∈ U, ψ (act σ g) = ψ g)
    (hψ1 : r < ψ 1)
    (N : ℕ) (a c : Fin N → L)
    (hac : ∀ γ : Γ, ∑ j, a j * s γ • c j = if γ = 1 then 1 else 0)
    (ha : ∀ j, ∀ x ∈ U, r < ψ x → ∃ y ∈ U, r < ψ y ∧ q y = a j • q x)
    (hc : ∀ j, ∀ x ∈ U, r ≤ ψ x → (∀ k, res k = 1 → act k x = x) →
      ∃ y ∈ U, r ≤ ψ y ∧ (∀ k, res k = 1 → act k y = y) ∧ q y = c j • q x)
    (θ : L) (hθfix : ∀ k, res k = 1 → k • θ = θ) (hθ : ∑ γ, s γ • θ = 1)
    (hθA : ∀ σ : Δ, ∀ x ∈ U, x ∈ U₂ → r ≤ ψ x →
      ∃ y ∈ U, y ∈ U₂ ∧ r ≤ ψ y ∧ e y = (σ • θ) • e x)
    (u : H) (huU : u ∈ U) (hur : r ≤ ψ u) (hufix : ∀ k, res k = 1 → act k u = u)
    (hu : u ∉ {g | g ∈ U ∧ r < ψ g} * (U₂ : Set H)) :
    ∃ h ∈ U, r ≤ ψ h ∧ (∀ σ, act σ h = h) ∧
      h ∉ {g | g ∈ U ∧ r < ψ g} * (U₂ : Set H) := by
  classical
  -- ultrametric consequences
  have hψ_le : ∀ g ∈ U, ψ g ≤ ψ 1 := by
    intro g hg
    have h := hψ_min g hg g hg
    rwa [min_self, mul_inv_cancel] at h
  have hψ_inv_le : ∀ g ∈ U, ψ g ≤ ψ g⁻¹ := by
    intro g hg
    have h := hψ_min 1 U.one_mem g hg
    rwa [one_mul, min_eq_right (hψ_le g hg)] at h
  have hψ_inv : ∀ g ∈ U, ψ g⁻¹ = ψ g := fun g hg =>
    le_antisymm (by simpa using hψ_inv_le g⁻¹ (U.inv_mem hg)) (hψ_inv_le g hg)
  have hψ_mul : ∀ g ∈ U, ∀ h ∈ U, min (ψ g) (ψ h) ≤ ψ (g * h) := by
    intro g hg h hh
    have h' := hψ_min g hg h⁻¹ (U.inv_mem hh)
    rwa [inv_inv, hψ_inv h hh] at h'
  -- the subgroups `A` and `A₊` of `U`
  let A : Subgroup U :=
    { carrier := {x | r ≤ ψ (x : H)}
      one_mem' := hψ1.le
      mul_mem' := fun {x y} hx hy => le_trans (le_min hx hy) (hψ_mul x x.2 y y.2)
      inv_mem' := fun {x} hx => by
        change r ≤ ψ (x : H)⁻¹
        rw [hψ_inv x x.2]
        exact hx }
  let Ap : Subgroup U :=
    { carrier := {x | r < ψ (x : H)}
      one_mem' := hψ1
      mul_mem' := fun {x y} hx hy => lt_of_lt_of_le (lt_min hx hy) (hψ_mul x x.2 y y.2)
      inv_mem' := fun {x} hx => by
        change r < ψ (x : H)⁻¹
        rw [hψ_inv x x.2]
        exact hx }
  have hq1 : q 1 = 0 := map_one_eq_zero U q hq_mul
  let qP : U →* Multiplicative (Fin n → L) :=
    { toFun := fun x => Multiplicative.ofAdd (q x)
      map_one' := by
        change Multiplicative.ofAdd (q 1) = 1
        rw [hq1, ofAdd_zero]
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (q ((x : H) * y)) = _
        rw [hq_mul x x.2 y y.2, ofAdd_add] }
  have hqP : ∀ x : U, (qP x).toAdd = q x := fun _ => rfl
  have hqP1 : ∀ x : U, qP x = 1 ↔ (x : H) ∈ U₂ := by
    intro x
    rw [← hq_ker x x.2]
    change Multiplicative.ofAdd (q x) = 1 ↔ _
    rw [ofAdd_eq_one]
  let actP := restrictAct act U hU
  obtain ⟨h, hA, hfix, hne⟩ := exists_fixed_not_mem_of_dual (Δ := Δ) (Γ := Γ) (P := U) (L := L)
    (pi_smul_smul n) (pi_smul_smul m) actP res s hs qP
    (fun σ x => by rw [hqP, hqP]; exact hq_act σ x x.2)
    (fun x => e x)
    (fun x y hx hy => he_mul x ((hqP1 x).mp hx) y ((hqP1 y).mp hy))
    (fun x hx he => Subtype.ext (he_inj x ((hqP1 x).mp hx) he))
    (fun σ x hx => he_act σ x ((hqP1 x).mp hx))
    A Ap
    (fun σ x hx => by
      change r ≤ ψ (act σ x)
      rw [hψ_act σ x x.2]
      exact hx)
    N a c hac
    (fun j x hx => by
      obtain ⟨y, hyU, hy, hyq⟩ := ha j x x.2 hx
      exact ⟨⟨y, hyU⟩, hy, by rw [hqP, hqP]; exact hyq⟩)
    (fun j x hx hxfix => by
      obtain ⟨y, hyU, hy, hyfix, hyq⟩ := hc j x x.2 hx
        (fun k hk => congrArg Subtype.val (hxfix k hk))
      exact ⟨⟨y, hyU⟩, hy, fun k hk => Subtype.ext (hyfix k hk), by
        rw [hqP, hqP]; exact hyq⟩)
    θ hθfix hθ
    (fun σ x hx hxq => by
      obtain ⟨y, hyU, hy₂, hy, hye⟩ := hθA σ x x.2 ((hqP1 x).mp hxq) hx
      exact ⟨⟨y, hyU⟩, hy, (hqP1 ⟨y, hyU⟩).mpr hy₂, hye⟩)
    ⟨u, huU⟩ hur (fun k hk => Subtype.ext (hufix k hk))
    (by
      intro y hy heq
      apply hu
      have hyu : q y = q u := by
        have h' := congrArg Multiplicative.toAdd heq
        rwa [hqP, hqP] at h'
      have hmem : (y : H)⁻¹ * u ∈ U := U.mul_mem (U.inv_mem y.2) huU
      have hq0 : q ((y : H)⁻¹ * u) = 0 := by
        rw [hq_mul _ (U.inv_mem y.2) u huU, map_inv_eq_neg U q hq_mul y.2, hyu, neg_add_cancel]
      exact ⟨y, ⟨y.2, hy⟩, (y : H)⁻¹ * u, (hq_ker _ hmem).mp hq0, mul_inv_cancel_left _ _⟩)
  refine ⟨h, h.2, hA, fun σ => congrArg Subtype.val (hfix σ), ?_⟩
  rintro ⟨y, ⟨hyU, hy⟩, w, hw, hyw⟩
  have hwU : w ∈ U := by
    have : w = y⁻¹ * h := by rw [← hyw, inv_mul_cancel_left]
    rw [this]
    exact U.mul_mem (U.inv_mem hyU) h.2
  have hqw : q w = 0 := (hq_ker w hwU).mpr hw
  apply hne ⟨y, hyU⟩ hy
  apply Multiplicative.toAdd.injective
  rw [hqP, hqP, ← hyw, hq_mul y hyU w hwU, hqw, add_zero]

/-- **Fixed jumps from stable subrings.** The version of `exists_fixed_not_mem_mul` in which the
dual family and the trace-one element come from a ring `R`. Here `Γ` acts on `R` through `ρ`,
compatibly with `res` along `ι : R →+* L`. Every `Γ`-stable subring of `R` containing all squares
of units is assumed to contain a dual family (`hdual`) and a trace-one element (`htrace`). The
squares of units must act on the images of `q` and `e` through conjugation by elements of `H`
(`hsq_q`, `hsq_e`). -/
theorem exists_fixed_not_mem_mul_of_subring
    {R R₀ : Type*} [CommRing R] [CommRing R₀] [Algebra R₀ R]
    (act : Δ →* MulAut H) (res : Δ →* Γ) (s : Γ → Δ) (hs : ∀ γ, res (s γ) = γ)
    (ρ : Γ →* (R ≃ₐ[R₀] R)) (ι : R →+* L) (hι : ∀ σ x, ι (ρ (res σ) x) = σ • ι x)
    (hdual : ∀ P : Subring R, (∀ γ, ∀ x ∈ P, ρ γ x ∈ P) → (∀ x : R, IsUnit x → x ^ 2 ∈ P) →
      ∃ (N : ℕ) (a c : Fin N → R), (∀ j, a j ∈ P) ∧ (∀ j, c j ∈ P) ∧
        ∀ γ : Γ, ∑ j, a j * ρ γ (c j) = if γ = 1 then 1 else 0)
    (htrace : ∀ P : Subring R, (∀ γ, ∀ x ∈ P, ρ γ x ∈ P) → (∀ x : R, IsUnit x → x ^ 2 ∈ P) →
      ∃ θ ∈ P, ∑ γ : Γ, ρ γ θ = 1)
    (U U₂ : Subgroup H) (hU : ∀ σ, ∀ x ∈ U, act σ x ∈ U)
    {n m : ℕ} (q : H → Fin n → L) (e : H → Fin m → L)
    (hq_mul : ∀ x ∈ U, ∀ y ∈ U, q (x * y) = q x + q y)
    (hq_ker : ∀ x ∈ U, q x = 0 ↔ x ∈ U₂)
    (he_mul : ∀ x ∈ U₂, ∀ y ∈ U₂, e (x * y) = e x + e y)
    (he_inj : ∀ x ∈ U₂, e x = 0 → x = 1)
    (hq_act : ∀ σ, ∀ x ∈ U, q (act σ x) = σ • q x)
    (he_act : ∀ σ, ∀ x ∈ U₂, e (act σ x) = σ • e x)
    (ψ : H → Λ) (r : Λ)
    (hψ_min : ∀ g ∈ U, ∀ h ∈ U, min (ψ g) (ψ h) ≤ ψ (g * h⁻¹))
    (hψ_act : ∀ σ, ∀ g ∈ U, ψ (act σ g) = ψ g)
    (hψ1 : r < ψ 1)
    (hsq_q : ∀ x : R, IsUnit x → ∃ τ : H, (∀ k, res k = 1 → act k τ = τ) ∧
      ∀ g ∈ U, τ * g * τ⁻¹ ∈ U ∧ ψ (τ * g * τ⁻¹) = ψ g ∧ q (τ * g * τ⁻¹) = ι (x ^ 2) • q g)
    (hsq_e : ∀ x : R, IsUnit x → ∃ τ : H, (∀ k, res k = 1 → act k τ = τ) ∧
      ∀ g ∈ U, g ∈ U₂ → τ * g * τ⁻¹ ∈ U ∧ τ * g * τ⁻¹ ∈ U₂ ∧ ψ (τ * g * τ⁻¹) = ψ g ∧
        e (τ * g * τ⁻¹) = ι (x ^ 2) • e g)
    (u : H) (huU : u ∈ U) (hur : r ≤ ψ u) (hufix : ∀ k, res k = 1 → act k u = u)
    (hu : u ∉ {g | g ∈ U ∧ r < ψ g} * (U₂ : Set H)) :
    ∃ h ∈ U, r ≤ ψ h ∧ (∀ σ, act σ h = h) ∧
      h ∉ {g | g ∈ U ∧ r < ψ g} * (U₂ : Set H) := by
  classical
  -- ultrametric consequences
  have hψ_le : ∀ g ∈ U, ψ g ≤ ψ 1 := by
    intro g hg
    have h := hψ_min g hg g hg
    rwa [min_self, mul_inv_cancel] at h
  have hψ_inv_le : ∀ g ∈ U, ψ g ≤ ψ g⁻¹ := by
    intro g hg
    have h := hψ_min 1 U.one_mem g hg
    rwa [one_mul, min_eq_right (hψ_le g hg)] at h
  have hψ_inv : ∀ g ∈ U, ψ g⁻¹ = ψ g := fun g hg =>
    le_antisymm (by simpa using hψ_inv_le g⁻¹ (U.inv_mem hg)) (hψ_inv_le g hg)
  have hψ_mul : ∀ g ∈ U, ∀ h ∈ U, min (ψ g) (ψ h) ≤ ψ (g * h) := by
    intro g hg h hh
    have h' := hψ_min g hg h⁻¹ (U.inv_mem hh)
    rwa [inv_inv, hψ_inv h hh] at h'
  -- kernel elements and conjugation
  have hker_conj : ∀ σ k, res k = 1 → res (σ⁻¹ * k * σ) = 1 := by
    intro σ k hk
    rw [map_mul, map_mul, map_inv, hk, mul_one, inv_mul_cancel]
  have hact_fix : ∀ σ (x : H), (∀ k, res k = 1 → act k x = x) →
      ∀ k, res k = 1 → act k (act σ x) = act σ x := by
    intro σ x hx k hk
    have h1 : act k (act σ x) = act σ (act (σ⁻¹ * k * σ) x) := by
      simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    rw [h1, hx _ (hker_conj σ k hk)]
  have hU₂act : ∀ σ, ∀ x ∈ U, x ∈ U₂ → act σ x ∈ U₂ := by
    intro σ x hxU hx
    rw [← hq_ker _ (hU σ x hxU), hq_act σ x hxU, (hq_ker x hxU).mpr hx, smul_zero]
  -- the three subgroups and their coordinate images
  let Bp : Subgroup H :=
    { carrier := {x | x ∈ U ∧ r < ψ x}
      one_mem' := ⟨U.one_mem, hψ1⟩
      mul_mem' := fun {x y} hx hy =>
        ⟨U.mul_mem hx.1 hy.1, lt_of_lt_of_le (lt_min hx.2 hy.2) (hψ_mul x hx.1 y hy.1)⟩
      inv_mem' := fun {x} hx => ⟨U.inv_mem hx.1, by rw [hψ_inv x hx.1]; exact hx.2⟩ }
  let Bf : Subgroup H :=
    { carrier := {x | x ∈ U ∧ r ≤ ψ x ∧ ∀ k, res k = 1 → act k x = x}
      one_mem' := ⟨U.one_mem, hψ1.le, fun k _ => map_one (act k)⟩
      mul_mem' := fun {x y} hx hy =>
        ⟨U.mul_mem hx.1 hy.1, le_trans (le_min hx.2.1 hy.2.1) (hψ_mul x hx.1 y hy.1),
          fun k hk => by rw [map_mul, hx.2.2 k hk, hy.2.2 k hk]⟩
      inv_mem' := fun {x} hx => ⟨U.inv_mem hx.1, by rw [hψ_inv x hx.1]; exact hx.2.1,
        fun k hk => by rw [map_inv, hx.2.2 k hk]⟩ }
  let B₂ : Subgroup H :=
    { carrier := {x | x ∈ U ∧ x ∈ U₂ ∧ r ≤ ψ x}
      one_mem' := ⟨U.one_mem, U₂.one_mem, hψ1.le⟩
      mul_mem' := fun {x y} hx hy =>
        ⟨U.mul_mem hx.1 hy.1, U₂.mul_mem hx.2.1 hy.2.1,
          le_trans (le_min hx.2.2 hy.2.2) (hψ_mul x hx.1 y hy.1)⟩
      inv_mem' := fun {x} hx => ⟨U.inv_mem hx.1, U₂.inv_mem hx.2.1, by
        rw [hψ_inv x hx.1]; exact hx.2.2⟩ }
  have hBp : Bp ≤ U := fun x hx => hx.1
  have hBf : Bf ≤ U := fun x hx => hx.1
  have hB₂ : B₂ ≤ U₂ := fun x hx => hx.2.1
  let Xp := imageAddSubgroup U Bp hBp q hq_mul
  let Xf := imageAddSubgroup U Bf hBf q hq_mul
  let X₂ := imageAddSubgroup U₂ B₂ hB₂ e he_mul
  -- the images are `Δ`-stable
  have hXp : ∀ σ : Δ, ∀ v ∈ Xp, σ • v ∈ Xp := by
    rintro σ _ ⟨x, hx, rfl⟩
    exact ⟨act σ x, ⟨hU σ x hx.1, by rw [hψ_act σ x hx.1]; exact hx.2⟩, hq_act σ x hx.1⟩
  have hXf : ∀ σ : Δ, ∀ v ∈ Xf, σ • v ∈ Xf := by
    rintro σ _ ⟨x, hx, rfl⟩
    exact ⟨act σ x, ⟨hU σ x hx.1, by rw [hψ_act σ x hx.1]; exact hx.2.1,
      hact_fix σ x hx.2.2⟩, hq_act σ x hx.1⟩
  have hX₂ : ∀ σ : Δ, ∀ v ∈ X₂, σ • v ∈ X₂ := by
    rintro σ _ ⟨x, hx, rfl⟩
    exact ⟨act σ x, ⟨hU σ x hx.1, hU₂act σ x hx.1 hx.2.1, by
      rw [hψ_act σ x hx.1]; exact hx.2.2⟩, he_act σ x hx.2.1⟩
  -- the stabilizer subrings
  let Pq : Subring R := stabilizer ι Xp ⊓ stabilizer ι Xf
  let Pe : Subring R := stabilizer ι X₂
  have hιs : ∀ γ x, ι (ρ γ x) = s γ • ι x := fun γ x => by rw [← hι, hs]
  have hPq : ∀ γ, ∀ x ∈ Pq, ρ γ x ∈ Pq := fun γ x hx =>
    ⟨mem_stabilizer_of_smul (pi_smul_smul n) ι Xp hXp (s γ) (hιs γ x) hx.1,
      mem_stabilizer_of_smul (pi_smul_smul n) ι Xf hXf (s γ) (hιs γ x) hx.2⟩
  have hPe : ∀ γ, ∀ x ∈ Pe, ρ γ x ∈ Pe := fun γ x hx =>
    mem_stabilizer_of_smul (pi_smul_smul m) ι X₂ hX₂ (s γ) (hιs γ x) hx
  have hsqPq : ∀ x : R, IsUnit x → x ^ 2 ∈ Pq := by
    intro x hx
    obtain ⟨τ, hτ, hτU⟩ := hsq_q x hx
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨hgU, hgψ, hgq⟩ := hτU g hg.1
      exact ⟨τ * g * τ⁻¹, ⟨hgU, by rw [hgψ]; exact hg.2⟩, hgq⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨hgU, hgψ, hgq⟩ := hτU g hg.1
      refine ⟨τ * g * τ⁻¹, ⟨hgU, by rw [hgψ]; exact hg.2.1, fun k hk => ?_⟩, hgq⟩
      rw [map_mul, map_mul, map_inv, hτ k hk, hg.2.2 k hk]
  have hsqPe : ∀ x : R, IsUnit x → x ^ 2 ∈ Pe := by
    intro x hx
    obtain ⟨τ, -, hτU⟩ := hsq_e x hx
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hgU, hg₂, hgψ, hge⟩ := hτU g hg.1 hg.2.1
    exact ⟨τ * g * τ⁻¹, ⟨hgU, hg₂, by rw [hgψ]; exact hg.2.2⟩, hge⟩
  obtain ⟨N, a, c, haP, hcP, hac⟩ := hdual Pq hPq hsqPq
  obtain ⟨θ, hθP, hθ⟩ := htrace Pe hPe hsqPe
  refine exists_fixed_not_mem_mul act res s hs U U₂ hU q e hq_mul hq_ker he_mul he_inj
    hq_act he_act ψ r hψ_min hψ_act hψ1 N (fun j => ι (a j)) (fun j => ι (c j)) ?_ ?_ ?_
    (ι θ) ?_ ?_ ?_ u huU hur hufix hu
  · intro γ
    simp_rw [← hιs, ← map_mul, ← map_sum, hac γ]
    split_ifs <;> simp
  · intro j x hxU hx
    obtain ⟨y, hy, hyq⟩ := (haP j).1 (q x) ⟨x, ⟨hxU, hx⟩, rfl⟩
    exact ⟨y, hy.1, hy.2, hyq⟩
  · intro j x hxU hx hxfix
    obtain ⟨y, hy, hyq⟩ := (hcP j).2 (q x) ⟨x, ⟨hxU, hx, hxfix⟩, rfl⟩
    exact ⟨y, hy.1, hy.2.1, hy.2.2, hyq⟩
  · intro k hk
    rw [← hι, hk, map_one, AlgEquiv.one_apply]
  · simp_rw [← hιs, ← map_sum, hθ, map_one]
  · intro σ x hxU hx₂ hx
    have hmem : ρ (res σ) θ ∈ Pe := hPe _ θ hθP
    obtain ⟨y, hy, hye⟩ := hmem (e x) ⟨x, ⟨hxU, hx₂, hx⟩, rfl⟩
    refine ⟨y, hy.1, hy.2.1, hy.2.2, ?_⟩
    rw [hye, hι]

end Descent

end Langlands.GroupScheme.FilteredTraceDescent
