import Langlands.LinearAlgebra.EpsilonHermitian.FiveTerm

/-!
# The Siegel parabolic subgroup and the Weyl elements

GKT §4.4.1: the Siegel parabolic `P(X)`, its Levi factor `M(X) ≅ GL(X)` and unipotent radical
`N(X) = {n(b) | b ∈ Herm^ε(Y, X)}`, `P(X) = M(X) ⋉ N(X)`; the Weyl elements `w_S` of a standard
basis and Lemma 4.27.

Let `h` be a non-degenerate `ε'`-Hermitian form on a finite-dimensional left `D`-module `V` (the
book's `W` is `-ε`-Hermitian: `ε' = -ε`), `X` a Lagrangian and `V = X ⊕ Y` a polarization.

* `siegelParabolic h X = {g | g X = X}`;
* `siegelUnipotent h X = {g | ∀ v, g v - v ∈ X}`, the book's `N(X)`; its elements are the identity
  on `X`, and they are the `n(b)`, `v ↦ v + b (v_Y)`, for `b : Y → X` with
  `h(b y, y') + h(y, b y') = 0` (the book's `Herm^ε(Y, X)`, (4.5));
* `siegelLeviOf a` (`a ∈ GL(X)`) is the book's `m(a)`: the isometry extending `a` with `m(a) Y = Y`
  (Lemma 4.9); every `p ∈ P(X)` is `m(p|_X) n(b)`;
* for a standard basis `e` and `S ⊆ ι`, `weylElement e S` is the book's `w_S` (4.8):
  `eᵢ ↦ ε' eᵢ*`, `eᵢ* ↦ eᵢ` for `i ∈ S`, fixing the other basis vectors.
-/

noncomputable section

namespace Langlands

namespace EpsilonHermitianForm

open Module
open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε' : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V] {h : EpsilonHermitianForm τ ε' V}

/-! ### The Siegel parabolic subgroup -/

section Parabolic

theorem map_isometryGroup_mul (g g' : h.isometryGroup) (X : Submodule D V) :
    X.map ((g * g' : h.isometryGroup) : V ≃ₗ[D] V).toLinearMap =
      (X.map (g' : V ≃ₗ[D] V).toLinearMap).map (g : V ≃ₗ[D] V).toLinearMap := by
  rw [← Submodule.map_comp]; rfl

variable (h) in
/-- The Siegel parabolic subgroup `P(X) = {g ∈ G(W) | g X = X}` (GKT §4.1.5, §4.4.1). -/
def siegelParabolic (X : Submodule D V) : Subgroup h.isometryGroup where
  carrier := {g | X.map (g : V ≃ₗ[D] V).toLinearMap = X}
  mul_mem' {g g'} hg hg' := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_isometryGroup_mul, hg', hg]
  one_mem' := by simp only [Set.mem_ofPred_eq]; exact Submodule.map_id X
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hg]
    rw [← map_isometryGroup_mul, inv_mul_cancel]
    exact Submodule.map_id X

theorem mem_siegelParabolic_iff {X : Submodule D V} {g : h.isometryGroup} :
    g ∈ h.siegelParabolic X ↔ X.map (g : V ≃ₗ[D] V).toLinearMap = X := Iff.rfl

theorem apply_mem_of_mem_siegelParabolic {X : Submodule D V} {g : h.isometryGroup}
    (hg : g ∈ h.siegelParabolic X) {x : V} (hx : x ∈ X) : (g : V ≃ₗ[D] V) x ∈ X :=
  hg ▸ ⟨x, hx, rfl⟩

theorem mem_siegelParabolic_of_le [FiniteDimensional D V] {X : Submodule D V} {g : h.isometryGroup}
    (hg : ∀ x ∈ X, (g : V ≃ₗ[D] V) x ∈ X) : g ∈ h.siegelParabolic X := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩; exact hg x hx
  · exact LinearEquiv.finrank_map_eq _ _

/-! ### The Siegel unipotent radical -/

variable (h) in
/-- The unipotent radical `N(X) = {g ∈ G | (g - 1) W ⊆ X}` of the Siegel parabolic (GKT §4.4.1). -/
def siegelUnipotent (X : Submodule D V) : Subgroup h.isometryGroup where
  carrier := {g | ∀ v, (g : V ≃ₗ[D] V) v - v ∈ X}
  mul_mem' {g g'} hg hg' v := by
    simp only [Set.mem_ofPred_eq] at *
    rw [isometryGroup_coe_mul_apply,
      show (g : V ≃ₗ[D] V) ((g' : V ≃ₗ[D] V) v) - v =
        ((g : V ≃ₗ[D] V) ((g' : V ≃ₗ[D] V) v) - (g' : V ≃ₗ[D] V) v) +
          ((g' : V ≃ₗ[D] V) v - v) by abel]
    exact X.add_mem (hg _) (hg' v)
  one_mem' v := by simp
  inv_mem' {g} hg v := by
    simp only [Set.mem_ofPred_eq] at *
    have := hg (((g⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) v)
    rw [isometryGroup_coe_inv_apply] at this
    rw [← neg_sub]; exact X.neg_mem this

theorem mem_siegelUnipotent_iff {X : Submodule D V} {g : h.isometryGroup} :
    g ∈ h.siegelUnipotent X ↔ ∀ v, (g : V ≃ₗ[D] V) v - v ∈ X := Iff.rfl

/-- An element of `N(X)` is the identity on `X`. -/
theorem apply_eq_of_mem_siegelUnipotent (hh : h.Nondegenerate) {X : Submodule D V}
    (hX : h.IsLagrangian X) {g : h.isometryGroup} (hg : g ∈ h.siegelUnipotent X) {x : V}
    (hx : x ∈ X) : (g : V ≃ₗ[D] V) x = x := by
  refine sub_eq_zero.1 (hh _ fun v => ?_)
  have e := isometryGroup_apply g x v
  have hv : (g : V ≃ₗ[D] V) v = v + ((g : V ≃ₗ[D] V) v - v) := by abel
  have hx' : (g : V ≃ₗ[D] V) x = x + ((g : V ≃ₗ[D] V) x - x) := by abel
  rw [hv, hx', h.map_add_left, h.map_add_right, h.map_add_right,
    hX.apply_eq_zero hx (hg v), hX.apply_eq_zero (hg x) (hg v), add_zero, add_zero] at e
  rw [h.map_sub_left]
  calc h ((g : V ≃ₗ[D] V) x) v - h x v
      = (h x v + h ((g : V ≃ₗ[D] V) x - x) v) - h x v := by
        rw [← h.map_add_left, add_sub_cancel]
    _ = 0 := by rw [e]; abel

theorem siegelUnipotent_le_siegelParabolic [FiniteDimensional D V] (hh : h.Nondegenerate)
    {X : Submodule D V} (hX : h.IsLagrangian X) : h.siegelUnipotent X ≤ h.siegelParabolic X :=
  fun g hg => mem_siegelParabolic_of_le fun x hx => by
    rw [apply_eq_of_mem_siegelUnipotent hh hX hg hx]; exact hx

/-- `N(X)` is abelian. -/
theorem siegelUnipotent_mul_comm (hh : h.Nondegenerate) {X : Submodule D V}
    (hX : h.IsLagrangian X) {g g' : h.isometryGroup} (hg : g ∈ h.siegelUnipotent X)
    (hg' : g' ∈ h.siegelUnipotent X) : g * g' = g' * g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [isometryGroup_coe_mul_apply]
  have e₁ : (g : V ≃ₗ[D] V) ((g' : V ≃ₗ[D] V) v) =
      ((g' : V ≃ₗ[D] V) v - v) + (g : V ≃ₗ[D] V) v := by
    have ha := apply_eq_of_mem_siegelUnipotent hh hX hg (hg' v)
    calc (g : V ≃ₗ[D] V) ((g' : V ≃ₗ[D] V) v)
        = (g : V ≃ₗ[D] V) (((g' : V ≃ₗ[D] V) v - v) + v) := by rw [sub_add_cancel]
      _ = _ := by rw [map_add, ha]
  have e₂ : (g' : V ≃ₗ[D] V) ((g : V ≃ₗ[D] V) v) =
      ((g : V ≃ₗ[D] V) v - v) + (g' : V ≃ₗ[D] V) v := by
    have ha := apply_eq_of_mem_siegelUnipotent hh hX hg' (hg v)
    calc (g' : V ≃ₗ[D] V) ((g : V ≃ₗ[D] V) v)
        = (g' : V ≃ₗ[D] V) (((g : V ≃ₗ[D] V) v - v) + v) := by rw [sub_add_cancel]
      _ = _ := by rw [map_add, ha]
  rw [e₁, e₂]; abel

/-- `N(X)` is normal in `P(X)`. -/
theorem conj_mem_siegelUnipotent {X : Submodule D V} {p g : h.isometryGroup}
    (hp : p ∈ h.siegelParabolic X) (hg : g ∈ h.siegelUnipotent X) :
    p * g * p⁻¹ ∈ h.siegelUnipotent X := by
  intro v
  simp only [isometryGroup_coe_mul_apply]
  have := apply_mem_of_mem_siegelParabolic hp (hg (((p⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) v))
  rwa [map_sub, isometryGroup_coe_inv_apply] at this

end Parabolic

/-! ### The elements `n(b)` -/

section Unipotent

variable {X Y : Submodule D V}

variable (h) in
/-- The book's `Herm^ε(Y, X)` (4.5), (4.6): the linear maps `b : Y → X` with
`h(b y, y') + h(y, b y') = 0`, i.e. `(y, y') ↦ h(b y, y')` is `-ε'`-Hermitian. -/
def siegelHerm (X Y : Submodule D V) : Set (Y →ₗ[D] X) :=
  {b | ∀ y y' : Y, h (b y) y' + h y (b y') = 0}

variable [FiniteDimensional D V]

/-- The linear map `n(b) : v ↦ v + b (v_Y)` for the polarization `V = X ⊕ Y`. -/
def siegelUnipotentMap (hXY : IsCompl X Y) (b : Y →ₗ[D] X) : V →ₗ[D] V :=
  LinearMap.id + X.subtype ∘ₗ b ∘ₗ Y.projectionOnto X hXY.symm

omit [FiniteDimensional D V] in
theorem siegelUnipotentMap_apply (hXY : IsCompl X Y) (b : Y →ₗ[D] X) (v : V) :
    siegelUnipotentMap hXY b v = v + b (Y.projectionOnto X hXY.symm v) := rfl

omit [FiniteDimensional D V] in
theorem siegelUnipotentMap_map_apply (hX : h.IsLagrangian X) (hXY : IsCompl X Y)
    {b : Y →ₗ[D] X} (hb : b ∈ h.siegelHerm X Y) (v w : V) :
    h (siegelUnipotentMap hXY b v) (siegelUnipotentMap hXY b w) = h v w := by
  set pv := Y.projectionOnto X hXY.symm v
  set pw := Y.projectionOnto X hXY.symm w
  have hv : v = (v - pv) + pv := by abel
  have hw : w = (w - pw) + pw := by abel
  have hvX : v - pv ∈ X := Submodule.sub_projection_mem hXY.symm v
  have hwX : w - pw ∈ X := Submodule.sub_projection_mem hXY.symm w
  rw [siegelUnipotentMap_apply, siegelUnipotentMap_apply, h.map_add_left, h.map_add_right,
    h.map_add_right, hX.apply_eq_zero (b pv).2 (b pw).2, add_zero]
  have e₁ : h v (b pw) = h (pv : V) (b pw) := by
    conv_lhs => rw [hv]
    rw [h.map_add_left, hX.apply_eq_zero hvX (b pw).2, zero_add]
  have e₂ : h (b pv : V) w = h (b pv : V) (pw : V) := by
    conv_lhs => rw [hw]
    rw [h.map_add_right, hX.apply_eq_zero (b pv).2 hwX, zero_add]
  rw [e₁, e₂, add_assoc, add_comm (h (pv : V) _), hb pv pw, add_zero]

variable (h) in
/-- The element `n(b)` of the Siegel unipotent radical (GKT §4.4.1). -/
def siegelUnipotentOf (hh : h.Nondegenerate) (hX : h.IsLagrangian X) (hXY : IsCompl X Y)
    (b : Y →ₗ[D] X) (hb : b ∈ h.siegelHerm X Y) : h.isometryGroup :=
  ofLinearMap hh (siegelUnipotentMap hXY b) (siegelUnipotentMap_map_apply hX hXY hb)

theorem siegelUnipotentOf_apply (hh : h.Nondegenerate) (hX : h.IsLagrangian X)
    (hXY : IsCompl X Y) {b : Y →ₗ[D] X} (hb : b ∈ h.siegelHerm X Y) (v : V) :
    ((h.siegelUnipotentOf hh hX hXY b hb : h.isometryGroup) : V ≃ₗ[D] V) v =
      v + b (Y.projectionOnto X hXY.symm v) := rfl

theorem siegelUnipotentOf_apply_right (hh : h.Nondegenerate) (hX : h.IsLagrangian X)
    (hXY : IsCompl X Y) {b : Y →ₗ[D] X} (hb : b ∈ h.siegelHerm X Y) (y : Y) :
    ((h.siegelUnipotentOf hh hX hXY b hb : h.isometryGroup) : V ≃ₗ[D] V) y = y + b y := by
  rw [siegelUnipotentOf_apply, Submodule.projectionOnto_apply_left]

theorem siegelUnipotentOf_mem (hh : h.Nondegenerate) (hX : h.IsLagrangian X)
    (hXY : IsCompl X Y) {b : Y →ₗ[D] X} (hb : b ∈ h.siegelHerm X Y) :
    h.siegelUnipotentOf hh hX hXY b hb ∈ h.siegelUnipotent X := fun v => by
  rw [siegelUnipotentOf_apply, add_sub_cancel_left]; exact Submodule.coe_mem _

/-- Every element of `N(X)` is an `n(b)` (GKT §4.4.1). -/
theorem exists_eq_siegelUnipotentOf (hh : h.Nondegenerate) (hX : h.IsLagrangian X)
    (hXY : IsCompl X Y) {g : h.isometryGroup} (hg : g ∈ h.siegelUnipotent X) :
    ∃ b hb, g = h.siegelUnipotentOf hh hX hXY b hb := by
  set b : Y →ₗ[D] X := ((((g : V ≃ₗ[D] V).toLinearMap - LinearMap.id).comp Y.subtype).codRestrict X
    (fun y => hg y))
  have hb' : ∀ y : Y, (b y : V) = (g : V ≃ₗ[D] V) y - y := fun _ => rfl
  have hb : b ∈ h.siegelHerm X Y := by
    intro y y'
    have e := isometryGroup_apply g (y : V) y'
    have hy : (g : V ≃ₗ[D] V) y = y + b y := by rw [hb']; abel
    have hy' : (g : V ≃ₗ[D] V) y' = y' + b y' := by rw [hb']; abel
    rw [hy, hy', h.map_add_left, h.map_add_right, h.map_add_right,
      hX.apply_eq_zero (b y).2 (b y').2, add_zero, add_assoc] at e
    have : h (y : V) (b y') + h (b y : V) y' = 0 :=
      add_left_cancel (e.trans (add_zero _).symm)
    rw [add_comm]; exact this
  refine ⟨b, hb, Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
  rw [siegelUnipotentOf_apply]
  set pv := Y.projectionOnto X hXY.symm v
  have hv : v = (v - pv) + pv := by abel
  have hvX : v - pv ∈ X := Submodule.sub_projection_mem hXY.symm v
  conv_lhs => rw [hv]
  rw [map_add, apply_eq_of_mem_siegelUnipotent hh hX hg hvX, hb']
  abel

end Unipotent

/-! ### The Levi factor and `P = M ⋉ N` -/

section Levi

variable [FiniteDimensional D V] {X Y : Submodule D V}

variable (h) in
/-- The Siegel Levi subgroup `M(X) = P(X) ∩ P(Y)` of a polarization (GKT §4.4.1). -/
def siegelLevi (X Y : Submodule D V) : Subgroup h.isometryGroup :=
  h.siegelParabolic X ⊓ h.siegelParabolic Y

variable (h) in
/-- The element `m(a)` of the Siegel Levi subgroup: the isometry extending `a ∈ GL(X)` with
`m(a) Y = Y` (GKT §4.4.1, Lemma 4.9). -/
def siegelLeviOf (hh : h.Nondegenerate) (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y)
    (hXY : IsCompl X Y) (a : X ≃ₗ[D] X) : h.isometryGroup :=
  (exists_isometry_extend hh hX hY hXY hX hY hXY a).choose

theorem siegelLeviOf_apply (hh : h.Nondegenerate) (hX : h.IsLagrangian X)
    (hY : h.IsLagrangian Y) (hXY : IsCompl X Y) (a : X ≃ₗ[D] X) (x : X) :
    ((h.siegelLeviOf hh hX hY hXY a : h.isometryGroup) : V ≃ₗ[D] V) x = a x :=
  (exists_isometry_extend hh hX hY hXY hX hY hXY a).choose_spec.1 x

theorem map_siegelLeviOf_right (hh : h.Nondegenerate) (hX : h.IsLagrangian X)
    (hY : h.IsLagrangian Y) (hXY : IsCompl X Y) (a : X ≃ₗ[D] X) :
    Y.map ((h.siegelLeviOf hh hX hY hXY a : h.isometryGroup) : V ≃ₗ[D] V).toLinearMap = Y :=
  (exists_isometry_extend hh hX hY hXY hX hY hXY a).choose_spec.2

theorem map_siegelLeviOf_left (hh : h.Nondegenerate) (hX : h.IsLagrangian X)
    (hY : h.IsLagrangian Y) (hXY : IsCompl X Y) (a : X ≃ₗ[D] X) :
    X.map ((h.siegelLeviOf hh hX hY hXY a : h.isometryGroup) : V ≃ₗ[D] V).toLinearMap = X :=
  mem_siegelParabolic_of_le fun x hx => by
    rw [siegelLeviOf_apply hh hX hY hXY a ⟨x, hx⟩]; exact Submodule.coe_mem _

theorem siegelLeviOf_mem (hh : h.Nondegenerate) (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y)
    (hXY : IsCompl X Y) (a : X ≃ₗ[D] X) :
    h.siegelLeviOf hh hX hY hXY a ∈ h.siegelLevi X Y :=
  ⟨map_siegelLeviOf_left hh hX hY hXY a, map_siegelLeviOf_right hh hX hY hXY a⟩

/-- `m(a)` is determined by `a` among the elements of `M(X)`. -/
theorem eq_siegelLeviOf (hh : h.Nondegenerate) (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y)
    (hXY : IsCompl X Y) (a : X ≃ₗ[D] X) {m : h.isometryGroup} (hm : m ∈ h.siegelLevi X Y)
    (hma : ∀ x : X, (m : V ≃ₗ[D] V) x = a x) : m = h.siegelLeviOf hh hX hY hXY a := by
  apply eq_of_isometry_extend hX hXY hX hXY
  · intro x hx; rw [hma ⟨x, hx⟩, siegelLeviOf_apply hh hX hY hXY a ⟨x, hx⟩]
  · intro y hy; exact apply_mem_of_mem_siegelParabolic hm.2 hy
  · intro y hy
    exact apply_mem_of_mem_siegelParabolic (siegelLeviOf_mem hh hX hY hXY a).2 hy
  · intro x hx; exact apply_mem_of_mem_siegelParabolic hm.1 hx

/-- The restriction `p ↦ p|_X` of an element of `P(X)` to `X`. -/
def restrictOfMemSiegelParabolic {g : h.isometryGroup} (hg : g ∈ h.siegelParabolic X) :
    X ≃ₗ[D] X :=
  ((g : V ≃ₗ[D] V).submoduleMap X).trans (LinearEquiv.ofEq _ _ hg)

omit [FiniteDimensional D V] in
theorem restrictOfMemSiegelParabolic_apply {g : h.isometryGroup} (hg : g ∈ h.siegelParabolic X)
    (x : X) : (restrictOfMemSiegelParabolic hg x : V) = (g : V ≃ₗ[D] V) x := rfl

/-- GKT §4.4.1, `P(X) = M(X) ⋉ N(X)`: every `p ∈ P(X)` is `m(p|_X) n(b)` with `b ∈ Herm^ε(Y, X)`. -/
theorem exists_eq_siegelLeviOf_mul_siegelUnipotentOf (hh : h.Nondegenerate)
    (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y) (hXY : IsCompl X Y) {p : h.isometryGroup}
    (hp : p ∈ h.siegelParabolic X) :
    ∃ b hb, p = h.siegelLeviOf hh hX hY hXY (restrictOfMemSiegelParabolic hp) *
      h.siegelUnipotentOf hh hX hXY b hb := by
  set m := h.siegelLeviOf hh hX hY hXY (restrictOfMemSiegelParabolic hp)
  have hq : m⁻¹ * p ∈ h.siegelUnipotent X := by
    intro v
    -- `m⁻¹ p` is the identity on `X` and preserves the form, so it moves vectors by `X`
    have hqX : ∀ x ∈ X, ((m⁻¹ * p : h.isometryGroup) : V ≃ₗ[D] V) x = x := by
      intro x hx
      rw [isometryGroup_coe_mul_apply]
      have : (p : V ≃ₗ[D] V) x = (m : V ≃ₗ[D] V) x := by
        rw [siegelLeviOf_apply hh hX hY hXY _ ⟨x, hx⟩]; rfl
      rw [this, isometryGroup_coe_inv_apply']
    rw [← hX]
    intro x hx
    rw [h.apply_eq_zero_comm, h.map_sub_right]
    have := isometryGroup_apply (m⁻¹ * p) x v
    rw [hqX x hx] at this
    rw [this, sub_self]
  obtain ⟨b, hb, hbq⟩ := exists_eq_siegelUnipotentOf hh hX hXY hq
  exact ⟨b, hb, by rw [← hbq, mul_inv_cancel_left]⟩

end Levi

/-! ### Weyl elements of a standard basis (GKT (4.8), Lemma 4.27) -/

section Weyl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : h.StandardBasis ι)

namespace StandardBasis

/-- The images of the basis vectors under `w_S`: `eᵢ ↦ ε' eᵢ*`, `eᵢ* ↦ eᵢ` for `i ∈ S`. -/
def weylImage (S : Finset ι) : ι ⊕ ι → V
  | .inl i => if i ∈ S then ((ε' : ℤ) : D) • e.snd i else e.fst i
  | .inr i => if i ∈ S then e.fst i else e.snd i

/-- The linear map `w_S`. -/
def weylMap (S : Finset ι) : V →ₗ[D] V := e.basis.constr ℕ (e.weylImage S)

omit [Fintype ι] in
theorem weylMap_basis (S : Finset ι) (k : ι ⊕ ι) : e.weylMap S (e.basis k) = e.weylImage S k :=
  e.basis.constr_basis ℕ _ k

omit [Fintype ι] in
theorem weylMap_map_apply (S : Finset ι) (v w : V) :
    h (e.weylMap S v) (e.weylMap S w) = h v w := by
  have key : h.comp (e.weylMap S) = h := by
    apply ext_basis e.basis
    intro k l
    simp only [comp_apply, weylMap_basis]
    rcases k with i | i <;> rcases l with j | j <;>
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp only [weylImage, hi, hj, ite_true, ite_false, h.map_smul_left, h.map_smul_right,
        fst, snd, e.apply_inl_inl, e.apply_inr_inr, e.apply_inl_inr, apply_inr_inl,
        RingInvo.conj_intCast, mul_zero, zero_mul, mul_ite, ite_mul, one_mul] <;>
      by_cases hij : i = j
    all_goals first
      | (subst hij; simp_all [units_int_cast_mul_self'])
      | simp [hij, Ne.symm hij]
  exact congrArg (fun k : EpsilonHermitianForm τ ε' V => k v w) key

variable [FiniteDimensional D V]

/-- The Weyl element `w_S` of a standard basis (GKT (4.8), (4.10)): `eᵢ ↦ ε' eᵢ*`, `eᵢ* ↦ eᵢ` for
`i ∈ S`, the other basis vectors fixed; for the book's `-ε`-Hermitian `W`, `ε' = -ε`. -/
def weylElement (S : Finset ι) : h.isometryGroup :=
  ofLinearMap e.nondegenerate (e.weylMap S) (e.weylMap_map_apply S)

theorem weylElement_basis (S : Finset ι) (k : ι ⊕ ι) :
    ((e.weylElement S : h.isometryGroup) : V ≃ₗ[D] V) (e.basis k) = e.weylImage S k :=
  e.weylMap_basis S k

theorem weylElement_fst_of_mem {S : Finset ι} {i : ι} (hi : i ∈ S) :
    ((e.weylElement S : h.isometryGroup) : V ≃ₗ[D] V) (e.fst i) = ((ε' : ℤ) : D) • e.snd i := by
  rw [fst, weylElement_basis]; simp [weylImage, hi]

theorem weylElement_fst_of_not_mem {S : Finset ι} {i : ι} (hi : i ∉ S) :
    ((e.weylElement S : h.isometryGroup) : V ≃ₗ[D] V) (e.fst i) = e.fst i := by
  rw [fst, weylElement_basis]; simp [weylImage, hi, fst]

theorem weylElement_snd_of_mem {S : Finset ι} {i : ι} (hi : i ∈ S) :
    ((e.weylElement S : h.isometryGroup) : V ≃ₗ[D] V) (e.snd i) = e.fst i := by
  rw [snd, weylElement_basis]; simp [weylImage, hi]

theorem weylElement_snd_of_not_mem {S : Finset ι} {i : ι} (hi : i ∉ S) :
    ((e.weylElement S : h.isometryGroup) : V ≃ₗ[D] V) (e.snd i) = e.snd i := by
  rw [snd, weylElement_basis]; simp [weylImage, hi, snd]

omit [Fintype ι] [FiniteDimensional D V] in
/-- Two isometries agreeing on a standard basis are equal. -/
theorem isometryGroup_ext {g g' : h.isometryGroup}
    (H : ∀ k, (g : V ≃ₗ[D] V) (e.basis k) = (g' : V ≃ₗ[D] V) (e.basis k)) : g = g' :=
  Subtype.ext (LinearEquiv.toLinearMap_injective (e.basis.ext H))

/-- GKT Lemma 4.27: `w_{S₁} w_{S₂} = w_{S₁ ∪ S₂}` for disjoint `S₁`, `S₂`. -/
theorem weylElement_mul_weylElement {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂) :
    e.weylElement S₁ * e.weylElement S₂ = e.weylElement (S₁ ∪ S₂) := by
  apply e.isometryGroup_ext
  rintro (i | i)
  · change _ = ((e.weylElement (S₁ ∪ S₂) : h.isometryGroup) : V ≃ₗ[D] V) (e.fst i)
    rw [isometryGroup_coe_mul_apply]
    change ((e.weylElement S₁ : h.isometryGroup) : V ≃ₗ[D] V)
      (((e.weylElement S₂ : h.isometryGroup) : V ≃ₗ[D] V) (e.fst i)) = _
    by_cases h₂ : i ∈ S₂
    · have h₁ : i ∉ S₁ := Finset.disjoint_right.1 hS h₂
      rw [e.weylElement_fst_of_mem h₂, map_smul, e.weylElement_snd_of_not_mem h₁,
        e.weylElement_fst_of_mem (Finset.mem_union_right _ h₂)]
    · by_cases h₁ : i ∈ S₁
      · rw [e.weylElement_fst_of_not_mem h₂, e.weylElement_fst_of_mem h₁,
          e.weylElement_fst_of_mem (Finset.mem_union_left _ h₁)]
      · rw [e.weylElement_fst_of_not_mem h₂, e.weylElement_fst_of_not_mem h₁,
          e.weylElement_fst_of_not_mem (by simp [h₁, h₂])]
  · change _ = ((e.weylElement (S₁ ∪ S₂) : h.isometryGroup) : V ≃ₗ[D] V) (e.snd i)
    rw [isometryGroup_coe_mul_apply]
    change ((e.weylElement S₁ : h.isometryGroup) : V ≃ₗ[D] V)
      (((e.weylElement S₂ : h.isometryGroup) : V ≃ₗ[D] V) (e.snd i)) = _
    by_cases h₂ : i ∈ S₂
    · have h₁ : i ∉ S₁ := Finset.disjoint_right.1 hS h₂
      rw [e.weylElement_snd_of_mem h₂, e.weylElement_fst_of_not_mem h₁,
        e.weylElement_snd_of_mem (Finset.mem_union_right _ h₂)]
    · by_cases h₁ : i ∈ S₁
      · rw [e.weylElement_snd_of_not_mem h₂, e.weylElement_snd_of_mem h₁,
          e.weylElement_snd_of_mem (Finset.mem_union_left _ h₁)]
      · rw [e.weylElement_snd_of_not_mem h₂, e.weylElement_snd_of_not_mem h₁,
          e.weylElement_snd_of_not_mem (by simp [h₁, h₂])]

theorem weylElement_comm {S₁ S₂ : Finset ι} (hS : Disjoint S₁ S₂) :
    e.weylElement S₁ * e.weylElement S₂ = e.weylElement S₂ * e.weylElement S₁ := by
  rw [e.weylElement_mul_weylElement hS, e.weylElement_mul_weylElement hS.symm, Finset.union_comm]

theorem weylElement_empty : e.weylElement ∅ = 1 :=
  e.isometryGroup_ext fun k => by
    rcases k with i | i
    · exact e.weylElement_fst_of_not_mem (Finset.notMem_empty i)
    · exact e.weylElement_snd_of_not_mem (Finset.notMem_empty i)

end StandardBasis

end Weyl

end EpsilonHermitianForm

end Langlands

end
