import Langlands.LinearAlgebra.EpsilonHermitian.Isotropic
import Mathlib.LinearAlgebra.Projection

/-!
# Lagrangians, polarizations and standard bases

GKT §4.1.3 (Definitions 4.7, 4.8), §4.2.1 (Lemmas 4.9, 4.10, 4.11 (d)), Lemma 4.14 (the
Lagrangian part), and Appendix B.2.1 (Proposition B.13).

For a non-degenerate `ε`-Hermitian form `h` on a finite-dimensional left `D`-module `V`:

* a Lagrangian is a subspace `X` with `X^⊥ = X` (`IsLagrangian`; GKT Lemma 4.10 (b)); for a
  split space this is the book's Definition 4.7 (a maximal totally isotropic subspace,
  `isLagrangian_iff_maximal`); `2 dim X = dim V`;
* `V` is split if it is the direct sum of two Lagrangians (a complete polarization, Definition 4.7);
* GKT Lemma 4.9: for two polarizations `V = X ⊕ Y = X' ⊕ Y'` every linear isomorphism `X ≅ X'`
  extends to a unique isometry `g` with `g Y = Y'` (`exists_isometry_extend`,
  `eq_of_isometry_extend`); hence the isometry group acts transitively on Lagrangians;
* GKT Lemma 4.14: for a totally isotropic `M` and a Lagrangian `X`, the image `X_M` of `X ∩ M^⊥`
  in `M^⊥/M` is a Lagrangian (`IsLagrangian.reduction`);
* a standard basis `e₁, …, eₙ, e₁*, …, eₙ*` (Definition 4.8, `StandardBasis`) exists for every
  polarization and every basis of its first Lagrangian.
-/

noncomputable section

namespace Langlands

namespace EpsilonHermitianForm

open Module
open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V] {h : EpsilonHermitianForm τ ε V}

variable (h) in
/-- A Lagrangian subspace: `X^⊥ = X` (GKT Definition 4.7 with Lemma 4.10 (b); see
`isLagrangian_iff_maximal` for the book's definition as a maximal totally isotropic subspace). -/
def IsLagrangian (X : Submodule D V) : Prop := h.orthogonal X = X

variable (h) in
/-- The space is split: it is the direct sum of two Lagrangians, a complete polarization
(GKT Definition 4.7). -/
def IsSplit : Prop := ∃ X Y : Submodule D V, h.IsLagrangian X ∧ h.IsLagrangian Y ∧ IsCompl X Y

theorem IsLagrangian.isTotallyIsotropic {X : Submodule D V} (hX : h.IsLagrangian X) :
    h.IsTotallyIsotropic X :=
  isTotallyIsotropic_iff_le_orthogonal.2 hX.symm.le

theorem IsLagrangian.mem_orthogonal_iff {X : Submodule D V} (hX : h.IsLagrangian X) {v : V} :
    v ∈ h.orthogonal X ↔ v ∈ X := by rw [hX]

theorem IsLagrangian.apply_eq_zero {X : Submodule D V} (hX : h.IsLagrangian X) {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) : h x y = 0 := hX.isTotallyIsotropic x hx y hy

/-- A Lagrangian has half the dimension: `2 dim X = dim V`. -/
theorem IsLagrangian.two_mul_finrank [FiniteDimensional D V] (hh : h.Nondegenerate)
    {X : Submodule D V} (hX : h.IsLagrangian X) : 2 * finrank D X = finrank D V := by
  have := finrank_add_finrank_orthogonal hh X
  rw [hX] at this
  omega

/-- A totally isotropic subspace of half the dimension is a Lagrangian. -/
theorem isLagrangian_of_two_mul_finrank [FiniteDimensional D V] (hh : h.Nondegenerate)
    {X : Submodule D V} (hX : h.IsTotallyIsotropic X) (hd : 2 * finrank D X = finrank D V) :
    h.IsLagrangian X := by
  have hle := isTotallyIsotropic_iff_le_orthogonal.1 hX
  have := finrank_add_finrank_orthogonal hh X
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

/-- The image of a Lagrangian under an isometry is a Lagrangian. -/
theorem IsLagrangian.map {X : Submodule D V} (hX : h.IsLagrangian X) (g : h.isometryGroup) :
    h.IsLagrangian (X.map (g : V ≃ₗ[D] V).toLinearMap) := by
  rw [IsLagrangian, ← map_orthogonal, hX]

/-- Two Lagrangians are transverse (`X ∩ Y = 0`) if and only if `V = X ⊕ Y`. -/
theorem IsLagrangian.isCompl_iff_disjoint [FiniteDimensional D V] (hh : h.Nondegenerate)
    {X Y : Submodule D V} (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y) :
    IsCompl X Y ↔ Disjoint X Y := by
  apply Submodule.isCompl_iff_disjoint
  have := hX.two_mul_finrank hh
  have := hY.two_mul_finrank hh
  omega

/-- GKT Lemma 4.11 (d): for a Lagrangian `X` and any `Y`, `X + Y = (X ∩ Y^⊥)^⊥`. -/
theorem IsLagrangian.sup_eq_orthogonal_inf [FiniteDimensional D V] (hh : h.Nondegenerate)
    {X : Submodule D V} (hX : h.IsLagrangian X) (Y : Submodule D V) :
    X ⊔ Y = h.orthogonal (X ⊓ h.orthogonal Y) := by
  rw [orthogonal_inf hh, hX, orthogonal_orthogonal hh]

/-- GKT Proposition B.13: a split space is the direct sum of two totally isotropic subspaces of
the same dimension. -/
theorem IsSplit.exists_isCompl [FiniteDimensional D V] (hh : h.Nondegenerate) (hs : h.IsSplit) :
    ∃ X Y : Submodule D V, h.IsTotallyIsotropic X ∧ h.IsTotallyIsotropic Y ∧ IsCompl X Y ∧
      finrank D X = finrank D Y := by
  obtain ⟨X, Y, hX, hY, hXY⟩ := hs
  refine ⟨X, Y, hX.isTotallyIsotropic, hY.isTotallyIsotropic, hXY, ?_⟩
  have := hX.two_mul_finrank hh
  have := hY.two_mul_finrank hh
  omega

/-! ### Lagrangian complements -/

/-- Every Lagrangian has a Lagrangian complement; in particular a non-degenerate space with a
Lagrangian is split. -/
theorem IsLagrangian.exists_isLagrangian_isCompl [FiniteDimensional D V] [NeZero (2 : D)]
    (hh : h.Nondegenerate) {X : Submodule D V} (hX : h.IsLagrangian X) :
    ∃ Y, h.IsLagrangian Y ∧ IsCompl X Y := by
  obtain ⟨Y, hYi, hYd, hc⟩ := exists_isTotallyIsotropic_isCompl hh hX.isTotallyIsotropic
  rw [hX] at hc
  refine ⟨Y, isLagrangian_of_two_mul_finrank hh hYi ?_, hc⟩
  rw [hYd]; exact hX.two_mul_finrank hh

/-! ### GKT Lemma 4.14: the reduction of a Lagrangian -/

variable (h) in
/-- The image `X_M` of `X ∩ M^⊥` in `M^⊥/M` (GKT Lemma 4.14). -/
def reductionSubmodule (M X : Submodule D V) : Submodule D (h.ReductionSpace M) :=
  (X.comap (h.orthogonal M).subtype).map (h.reductionMap M)

theorem mem_reductionSubmodule {M X : Submodule D V} {a : h.ReductionSpace M} :
    a ∈ h.reductionSubmodule M X ↔ ∃ x : h.orthogonal M, (x : V) ∈ X ∧ h.reductionMap M x = a := by
  simp [reductionSubmodule]

/-- GKT Lemma 4.14: for a totally isotropic `M` and a Lagrangian `X`, the image `X_M` of
`X ∩ M^⊥` in `M^⊥/M` is a Lagrangian. -/
theorem IsLagrangian.reduction [FiniteDimensional D V] (hh : h.Nondegenerate)
    {M X : Submodule D V} (hM : h.IsTotallyIsotropic M) (hX : h.IsLagrangian X) :
    (h.reduction M).IsLagrangian (h.reductionSubmodule M X) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨w, rfl⟩ := h.reductionMap_surjective M a
    -- `w ⊥ X ∩ M^⊥`, so `w ∈ X + M`
    have hw : (w : V) ∈ h.orthogonal (X ⊓ h.orthogonal M) := by
      intro u ⟨huX, huM⟩
      exact ha (h.reductionMap M ⟨u, huM⟩) (mem_reductionSubmodule.2 ⟨⟨u, huM⟩, huX, rfl⟩)
    rw [orthogonal_inf hh, hX, orthogonal_orthogonal hh] at hw
    obtain ⟨x, hx, m, hm, hxm⟩ := Submodule.mem_sup.1 hw
    have hxM : x ∈ h.orthogonal M := by
      have : x = (w : V) - m := by rw [← hxm, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ w.2 (isTotallyIsotropic_iff_le_orthogonal.1 hM hm)
    refine mem_reductionSubmodule.2 ⟨⟨x, hxM⟩, hx, ?_⟩
    rw [← sub_eq_zero, ← map_sub, reductionMap_eq_zero_iff]
    simp only [Submodule.coe_sub]
    rw [← hxm, sub_add_cancel_left]
    exact M.neg_mem hm
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := mem_reductionSubmodule.1 ha
    obtain ⟨y, hy, rfl⟩ := mem_reductionSubmodule.1 hb
    rw [reduction_apply_mk]
    exact hX.apply_eq_zero hx hy

/-! ### Definition 4.7: Lagrangians are the maximal totally isotropic subspaces -/

/-- In a split space, the Lagrangians are exactly the maximal totally isotropic subspaces
(GKT Definition 4.7 and Lemma 4.10 (b)). -/
theorem isLagrangian_iff_maximal [FiniteDimensional D V] (hh : h.Nondegenerate)
    (hs : h.IsSplit) {X : Submodule D V} :
    h.IsLagrangian X ↔
      h.IsTotallyIsotropic X ∧ ∀ X', h.IsTotallyIsotropic X' → X ≤ X' → X' = X := by
  constructor
  · intro hX
    refine ⟨hX.isTotallyIsotropic, fun X' hX' hle => le_antisymm ?_ hle⟩
    calc X' ≤ h.orthogonal X' := isTotallyIsotropic_iff_le_orthogonal.1 hX'
      _ ≤ h.orthogonal X := orthogonal_le_orthogonal hle
      _ = X := hX
  · rintro ⟨hXi, hmax⟩
    obtain ⟨L, -, hL, -, -⟩ := hs
    by_contra hne
    have hlt : X < h.orthogonal X :=
      lt_of_le_of_ne (isTotallyIsotropic_iff_le_orthogonal.1 hXi) (Ne.symm hne)
    -- the reduction `W_X = X^⊥/X` is non-zero, and `L_X` is a Lagrangian of it
    have hLX := hL.reduction hh hXi
    obtain ⟨w, hw, hwX⟩ := IsConcreteLE.exists_of_lt hlt
    have hne0 : h.reductionMap X ⟨w, hw⟩ ≠ 0 := by
      rw [Ne, reductionMap_eq_zero_iff]; exact hwX
    have hLne : h.reductionSubmodule X L ≠ ⊥ := by
      intro e
      rw [IsLagrangian, e, orthogonal_bot] at hLX
      exact hne0 (by
        have : h.reductionMap X ⟨w, hw⟩ ∈ (⊤ : Submodule D (h.ReductionSpace X)) := trivial
        rw [hLX] at this
        exact (Submodule.mem_bot D).1 this)
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
    obtain ⟨v, hvL, rfl⟩ := mem_reductionSubmodule.1 ha
    have hvX : (v : V) ∉ X := fun H => ha0 (reductionMap_eq_zero_iff.2 H)
    have hiso : h.IsTotallyIsotropic (X ⊔ D ∙ (v : V)) := by
      intro x hx y hy
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx₂
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
      have hvv : h v v = 0 := hL.apply_eq_zero hvL hvL
      have h1 : h x₁ v = 0 := (h.apply_eq_zero_comm).1 (v.2 x₁ hx₁)
      have h2 : h v y₁ = 0 := v.2 y₁ hy₁
      simp only [h.map_add_left, h.map_add_right, h.map_smul_left, h.map_smul_right,
        hXi x₁ hx₁ y₁ hy₁, h1, h2, hvv, mul_zero, zero_mul, add_zero]
    have heq := hmax _ hiso le_sup_left
    have hv' : (v : V) ∈ X ⊔ D ∙ (v : V) :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    rw [heq] at hv'
    exact hvX hv'

/-! ### GKT Lemma 4.9 -/

section Extend

variable [FiniteDimensional D V]

/-- A vector `y ∈ Y'` represents the form `x' ↦ h (f⁻¹ x') y` on `X'` (the construction of
GKT Lemma 4.9). -/
private theorem exists_rep (hh : h.Nondegenerate) {X X' Y' : Submodule D V}
    (hX' : h.IsLagrangian X') (hY' : h.IsLagrangian Y') (hX'Y' : IsCompl X' Y')
    (f : X ≃ₗ[D] X') (y : V) : ∃ y' ∈ Y', ∀ x : X', h x y' = h (f.symm x) y := by
  have hd : Disjoint Y' (h.orthogonal X') := by rw [hX']; exact hX'Y'.disjoint.symm
  have hdim : finrank D Y' = finrank D X' := by
    have := hX'.two_mul_finrank hh
    have := hY'.two_mul_finrank hh
    omega
  exact exists_mem_forall_apply_eq hd hdim
    ((h.flipApply y).comp (X.subtype.comp f.symm.toLinearMap))

/-- GKT Lemma 4.9 (existence): for two polarizations `V = X ⊕ Y = X' ⊕ Y'`, every linear
isomorphism `f : X ≅ X'` extends to an isometry `g` of `V` with `g Y = Y'`. -/
theorem exists_isometry_extend (hh : h.Nondegenerate) {X Y X' Y' : Submodule D V}
    (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y) (hXY : IsCompl X Y)
    (hX' : h.IsLagrangian X') (hY' : h.IsLagrangian Y') (hX'Y' : IsCompl X' Y')
    (f : X ≃ₗ[D] X') :
    ∃ g : h.isometryGroup, (∀ x : X, (g : V ≃ₗ[D] V) x = f x) ∧
      Y.map (g : V ≃ₗ[D] V).toLinearMap = Y' := by
  choose r hrY hr using fun y : V => exists_rep hh hX' hY' hX'Y' f y
  have hdisj : Disjoint Y' (h.orthogonal X') := by rw [hX']; exact hX'Y'.disjoint.symm
  have runiq : ∀ (y : V) (v : V), v ∈ Y' → (∀ x : X', h x v = h (f.symm x) y) → v = r y :=
    fun y v hv H => eq_of_forall_apply_eq hdisj hv (hrY y) fun x hx => by
      rw [H ⟨x, hx⟩, hr y ⟨x, hx⟩]
  set gY : Y →ₗ[D] V :=
    { toFun := fun y => r y
      map_add' := fun a b => (runiq _ _ (Y'.add_mem (hrY a) (hrY b)) fun x => by
        rw [h.map_add_right, hr, hr, Submodule.coe_add, h.map_add_right]).symm
      map_smul' := fun c a => (runiq _ _ (Y'.smul_mem c (hrY a)) fun x => by
        rw [h.map_smul_right, hr, Submodule.coe_smul, h.map_smul_right]).symm }
  set gX : X →ₗ[D] V := X'.subtype.comp f.toLinearMap
  set g₀ : V →ₗ[D] V := LinearMap.ofIsCompl hXY gX gY
  have hg₀X : ∀ x : X, g₀ x = f x := fun x => LinearMap.ofIsCompl_apply_left hXY x
  have hg₀Y : ∀ y : Y, g₀ y = r y := fun y => LinearMap.ofIsCompl_apply_right hXY y
  have hdecomp : ∀ v : V, ∃ x : X, ∃ y : Y, (x : V) + y = v := fun v => by
    have : v ∈ X ⊔ Y := by rw [hXY.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, rfl⟩
  have hinj : Function.Injective g₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    obtain ⟨x, y, rfl⟩ := hdecomp v
    rw [LinearMap.mem_ker, map_add, hg₀X, hg₀Y] at hv
    have h1 : ((f x : X') : V) = 0 := by
      have := Submodule.disjoint_def.1 hX'Y'.disjoint ((f x : X') : V) (f x).2
        (by rw [eq_neg_of_add_eq_zero_left hv]; exact Y'.neg_mem (hrY y))
      exact this
    have hx : x = 0 := by
      have : f x = 0 := Subtype.ext h1
      simpa using this
    have hy0 : r y = 0 := by rw [h1, zero_add] at hv; exact hv
    have hyX : (y : V) ∈ h.orthogonal X := mem_orthogonal'.2 fun u hu => by
      have := hr y (f ⟨u, hu⟩)
      rw [hy0, map_zero_right, LinearEquiv.symm_apply_apply] at this
      exact this.symm
    rw [hX] at hyX
    have hy : (y : V) = 0 := Submodule.disjoint_def.1 hXY.disjoint _ hyX y.2
    rw [hx, Submodule.coe_zero, zero_add, hy]
    exact (Submodule.mem_bot D).2 rfl
  have hbij : Function.Bijective g₀ := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  set g : V ≃ₗ[D] V := LinearEquiv.ofBijective g₀ hbij
  have hgapp : ∀ v, g v = g₀ v := fun _ => rfl
  have hiso : g ∈ h.isometryGroup := by
    intro v w
    obtain ⟨x₁, y₁, rfl⟩ := hdecomp v
    obtain ⟨x₂, y₂, rfl⟩ := hdecomp w
    simp only [hgapp, map_add, hg₀X, hg₀Y, h.map_add_left, h.map_add_right]
    have e1 : h ((f x₁ : X') : V) ((f x₂ : X') : V) = 0 := hX'.apply_eq_zero (f x₁).2 (f x₂).2
    have e2 : h (r y₁) (r y₂) = 0 := hY'.apply_eq_zero (hrY y₁) (hrY y₂)
    have e3 : h (x₁ : V) (x₂ : V) = 0 := hX.apply_eq_zero x₁.2 x₂.2
    have e4 : h (y₁ : V) (y₂ : V) = 0 := hY.apply_eq_zero y₁.2 y₂.2
    have e5 : h ((f x₁ : X') : V) (r y₂) = h (x₁ : V) y₂ := by
      rw [hr y₂ (f x₁), LinearEquiv.symm_apply_apply]
    have e6 : h (r y₁) ((f x₂ : X') : V) = h (y₁ : V) x₂ := by
      rw [h.conj_swap ((f x₂ : X') : V) (r y₁), hr y₁ (f x₂), LinearEquiv.symm_apply_apply,
        ← h.conj_swap]
    rw [e1, e2, e3, e4, e5, e6]
  refine ⟨⟨g, hiso⟩, fun x => hg₀X x, le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (show g y = r y from hg₀Y ⟨y, hy⟩) ▸ hrY y
  · intro y' hy'
    obtain ⟨v, hv⟩ := hbij.2 y'
    obtain ⟨x, y, rfl⟩ := hdecomp v
    rw [map_add, hg₀X, hg₀Y] at hv
    have hfx : ((f x : X') : V) = 0 := Submodule.disjoint_def.1 hX'Y'.disjoint _ (f x).2 (by
      have : ((f x : X') : V) = y' - r y := by rw [← hv, add_sub_cancel_right]
      rw [this]; exact Y'.sub_mem hy' (hrY y))
    rw [hfx, zero_add] at hv
    exact ⟨y, y.2, (show g y = r y from hg₀Y y).trans hv⟩

omit [FiniteDimensional D V] in
/-- GKT Lemma 4.9 (uniqueness): an isometry is determined by its restriction to `X` and the
condition `g Y ≤ Y'`. -/
theorem eq_of_isometry_extend {X Y X' Y' : Submodule D V} (hX : h.IsLagrangian X)
    (hXY : IsCompl X Y) (hX' : h.IsLagrangian X') (hX'Y' : IsCompl X' Y')
    {g g' : h.isometryGroup} (hgX : ∀ x ∈ X, (g : V ≃ₗ[D] V) x = (g' : V ≃ₗ[D] V) x)
    (hgY : ∀ y ∈ Y, (g : V ≃ₗ[D] V) y ∈ Y') (hg'Y : ∀ y ∈ Y, (g' : V ≃ₗ[D] V) y ∈ Y')
    (hgX' : ∀ x ∈ X, (g : V ≃ₗ[D] V) x ∈ X') : g = g' := by
  have hdisj : Disjoint Y' (h.orthogonal X') := by rw [hX']; exact hX'Y'.disjoint.symm
  have hY : ∀ y ∈ Y, (g : V ≃ₗ[D] V) y = (g' : V ≃ₗ[D] V) y := by
    intro y hy
    apply eq_of_forall_apply_eq hdisj (hgY y hy) (hg'Y y hy)
    intro x' hx'
    -- `x' = g x` for some `x ∈ X`
    have : x' ∈ X.map (g : V ≃ₗ[D] V).toLinearMap := by
      have hle : X.map (g : V ≃ₗ[D] V).toLinearMap ≤ X' := by
        rintro _ ⟨x, hx, rfl⟩; exact hgX' x hx
      have hL := hX.map g
      have heq : X.map (g : V ≃ₗ[D] V).toLinearMap = X' := by
        apply le_antisymm hle
        calc X' = h.orthogonal X' := hX'.symm
          _ ≤ h.orthogonal (X.map (g : V ≃ₗ[D] V).toLinearMap) := orthogonal_le_orthogonal hle
          _ = _ := hL
      rw [heq]; exact hx'
    obtain ⟨x, hx, rfl⟩ := this
    simp only [LinearEquiv.coe_coe]
    rw [isometryGroup_apply, hgX x hx, isometryGroup_apply]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have : v ∈ X ⊔ Y := by rw [hXY.sup_eq_top]; trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 this
  rw [map_add, map_add, hgX x hx, hY y hy]

/-- The isometry group acts transitively on Lagrangians (GKT §4.1.3, after Definition 4.7). -/
theorem exists_isometry_map_eq [NeZero (2 : D)] (hh : h.Nondegenerate) {X X' : Submodule D V}
    (hX : h.IsLagrangian X) (hX' : h.IsLagrangian X') :
    ∃ g : h.isometryGroup, X.map (g : V ≃ₗ[D] V).toLinearMap = X' := by
  obtain ⟨Y, hY, hXY⟩ := hX.exists_isLagrangian_isCompl hh
  obtain ⟨Y', hY', hX'Y'⟩ := hX'.exists_isLagrangian_isCompl hh
  have hd : finrank D X = finrank D X' := by
    have := hX.two_mul_finrank hh; have := hX'.two_mul_finrank hh; omega
  obtain ⟨f⟩ : Nonempty (X ≃ₗ[D] X') := ⟨LinearEquiv.ofFinrankEq _ _ hd⟩
  obtain ⟨g, hgX, -⟩ := exists_isometry_extend hh hX hY hXY hX' hY' hX'Y' f
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, hgX ⟨x, hx⟩]; exact (f ⟨x, hx⟩).2
  · intro x' hx'
    refine ⟨(f.symm ⟨x', hx'⟩ : X), (f.symm ⟨x', hx'⟩).2, ?_⟩
    rw [LinearEquiv.coe_coe, hgX, LinearEquiv.apply_symm_apply]

end Extend

/-! ### Standard bases (GKT Definition 4.8) -/

variable (h) in
/-- A standard basis `e₁, …, eₙ, e₁*, …, eₙ*` (GKT Definition 4.8), indexed by `ι ⊕ ι`:
`h(eᵢ, eⱼ) = h(eᵢ*, eⱼ*) = 0` and `h(eᵢ, eⱼ*) = δᵢⱼ`. -/
structure StandardBasis (ι : Type*) [DecidableEq ι] where
  /-- The underlying basis: `basis (inl i) = eᵢ`, `basis (inr i) = eᵢ*`. -/
  basis : Module.Basis (ι ⊕ ι) D V
  apply_inl_inl : ∀ i j, h (basis (.inl i)) (basis (.inl j)) = 0
  apply_inr_inr : ∀ i j, h (basis (.inr i)) (basis (.inr j)) = 0
  apply_inl_inr : ∀ i j, h (basis (.inl i)) (basis (.inr j)) = if i = j then 1 else 0

namespace StandardBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : h.StandardBasis ι)

/-- The vectors `eᵢ`. -/
def fst (i : ι) : V := e.basis (.inl i)

/-- The vectors `eᵢ*`. -/
def snd (i : ι) : V := e.basis (.inr i)

omit [Fintype ι] in
/-- `h(eⱼ*, eᵢ) = ε δᵢⱼ`. -/
theorem apply_inr_inl (i j : ι) :
    h (e.basis (.inr j)) (e.basis (.inl i)) = if i = j then ((ε : ℤ) : D) else 0 := by
  rw [h.conj_swap, e.apply_inl_inr]
  split_ifs <;> simp

/-- The Lagrangian `X = span {eᵢ}` determined by the standard basis. -/
def lagrangianFst : Submodule D V := Submodule.span D (Set.range e.fst)

/-- The Lagrangian `Y = span {eᵢ*}` determined by the standard basis. -/
def lagrangianSnd : Submodule D V := Submodule.span D (Set.range e.snd)

include e in
/-- A standard basis makes the form non-degenerate. -/
theorem nondegenerate : h.Nondegenerate := by
  intro v hv
  have hc : ∀ k, e.basis.repr v k = 0 := by
    have hv' := e.basis.sum_repr v
    rintro (j | j)
    · -- pair with `eⱼ*`
      have := hv (e.basis (.inr j))
      rw [← hv', h.map_sum_left, Fintype.sum_sum_type] at this
      simpa [h.map_smul_left, e.apply_inl_inr, e.apply_inr_inr] using this
    · have := hv (e.basis (.inl j))
      rw [← hv', h.map_sum_left, Fintype.sum_sum_type] at this
      simp only [h.map_smul_left, e.apply_inl_inl, apply_inr_inl, mul_zero, mul_ite,
        Finset.sum_const_zero, zero_add, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
      have hε : ((ε : ℤ) : D) ≠ 0 := by
        intro e0; have := units_int_cast_mul_self' (D := D) ε; rw [e0, zero_mul] at this
        exact zero_ne_one this
      exact (mul_eq_zero.1 this).resolve_right hε
  rw [← e.basis.sum_repr v]
  simp [hc]

omit [Fintype ι] in
theorem fst_mem_lagrangianFst (i : ι) : e.fst i ∈ e.lagrangianFst :=
  Submodule.subset_span ⟨i, rfl⟩

omit [Fintype ι] in
theorem snd_mem_lagrangianSnd (i : ι) : e.snd i ∈ e.lagrangianSnd :=
  Submodule.subset_span ⟨i, rfl⟩

theorem isTotallyIsotropic_lagrangianFst : h.IsTotallyIsotropic e.lagrangianFst := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hy
  simp [h.map_sum_left, h.map_sum_right, h.map_smul_left, h.map_smul_right, fst, e.apply_inl_inl]

theorem isTotallyIsotropic_lagrangianSnd : h.IsTotallyIsotropic e.lagrangianSnd := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hy
  simp [h.map_sum_left, h.map_sum_right, h.map_smul_left, h.map_smul_right, snd, e.apply_inr_inr]

theorem finrank_lagrangianFst : finrank D e.lagrangianFst = Fintype.card ι :=
  finrank_span_eq_card (e.basis.linearIndependent.comp _ Sum.inl_injective)

theorem finrank_lagrangianSnd : finrank D e.lagrangianSnd = Fintype.card ι :=
  finrank_span_eq_card (e.basis.linearIndependent.comp _ Sum.inr_injective)

include e in
theorem finrank_eq : finrank D V = 2 * Fintype.card ι := by
  rw [Module.finrank_eq_card_basis e.basis, Fintype.card_sum, two_mul]

theorem isLagrangian_lagrangianFst : h.IsLagrangian e.lagrangianFst :=
  have : FiniteDimensional D V := Module.Finite.of_basis e.basis
  isLagrangian_of_two_mul_finrank e.nondegenerate e.isTotallyIsotropic_lagrangianFst
    (by rw [e.finrank_lagrangianFst, e.finrank_eq])

theorem isLagrangian_lagrangianSnd : h.IsLagrangian e.lagrangianSnd :=
  have : FiniteDimensional D V := Module.Finite.of_basis e.basis
  isLagrangian_of_two_mul_finrank e.nondegenerate e.isTotallyIsotropic_lagrangianSnd
    (by rw [e.finrank_lagrangianSnd, e.finrank_eq])

theorem isCompl_lagrangianFst_lagrangianSnd : IsCompl e.lagrangianFst e.lagrangianSnd := by
  have : FiniteDimensional D V := Module.Finite.of_basis e.basis
  rw [e.isLagrangian_lagrangianFst.isCompl_iff_disjoint e.nondegenerate
    e.isLagrangian_lagrangianSnd]
  have := e.basis.linearIndependent.disjoint_span_image (s := Set.range Sum.inl)
    (t := Set.range Sum.inr) (by
      rw [Set.disjoint_iff]; rintro _ ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩; exact Sum.inr_ne_inl hj)
  rw [← Set.range_comp, ← Set.range_comp] at this
  exact this

/-- Two spaces with standard bases indexed by the same type are isometric: the linear isomorphism
sending one standard basis to the other is an isometry (for `ι` with one element: the uniqueness of
the hyperbolic plane, GKT Proposition B.9). -/
def isometryEquiv {V' : Type*} [AddCommGroup V'] [Module D V'] {h' : EpsilonHermitianForm τ ε V'}
    (e' : h'.StandardBasis ι) : IsometryEquiv h h' where
  toLinearEquiv := e.basis.equiv e'.basis (Equiv.refl _)
  map_app' x y := by
    have key : h'.comp (e.basis.equiv e'.basis (Equiv.refl _)).toLinearMap = h := by
      apply ext_basis e.basis
      rintro (i | i) (j | j) <;>
        simp [Module.Basis.equiv_apply, e.apply_inl_inl, e'.apply_inl_inl, e.apply_inr_inr,
          e'.apply_inr_inr, e.apply_inl_inr, e'.apply_inl_inr, apply_inr_inl]
    exact congrArg (fun k : EpsilonHermitianForm τ ε V => k x y) key

omit [Fintype ι] in
theorem isometryEquiv_apply_basis {V' : Type*} [AddCommGroup V'] [Module D V']
    {h' : EpsilonHermitianForm τ ε V'} (e' : h'.StandardBasis ι) (k : ι ⊕ ι) :
    e.isometryEquiv e' (e.basis k) = e'.basis k := by
  change (e.basis.equiv e'.basis (Equiv.refl _)) (e.basis k) = e'.basis k
  rw [Module.Basis.equiv_apply, Equiv.refl_apply]

omit [Fintype ι] in
/-- Reindexing a standard basis along a bijection of the index sets. -/
def reindex {κ : Type*} [DecidableEq κ] (σ : ι ≃ κ) : h.StandardBasis κ where
  basis := e.basis.reindex (Equiv.sumCongr σ σ)
  apply_inl_inl i j := by
    simpa [Module.Basis.reindex_apply] using e.apply_inl_inl (σ.symm i) (σ.symm j)
  apply_inr_inr i j := by
    simpa [Module.Basis.reindex_apply] using e.apply_inr_inr (σ.symm i) (σ.symm j)
  apply_inl_inr i j := by
    simpa [Module.Basis.reindex_apply, σ.symm.injective.eq_iff] using
      e.apply_inl_inr (σ.symm i) (σ.symm j)

end StandardBasis

/-- A standard basis exists for every polarization `V = X ⊕ Y` and every basis `b` of `X`: there
is a standard basis with `eᵢ = bᵢ`, `span {eᵢ} = X` and `span {eᵢ*} = Y` (GKT Definition 4.8 and
the proof of Lemma 4.9). -/
theorem exists_standardBasis [FiniteDimensional D V] (hh : h.Nondegenerate) {X Y : Submodule D V}
    (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y) (hXY : IsCompl X Y) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι D X) :
    ∃ e : h.StandardBasis ι, (∀ i, e.fst i = b i) ∧ e.lagrangianFst = X ∧ e.lagrangianSnd = Y := by
  have hd : Disjoint Y (h.orthogonal X) := by rw [hX]; exact hXY.disjoint.symm
  have hdim : finrank D Y = finrank D X := by
    have := hX.two_mul_finrank hh; have := hY.two_mul_finrank hh; omega
  obtain ⟨c, hcY, hc⟩ := exists_dual_family hd hdim b
  set c' : ι → Y := fun j => ⟨c j, hcY j⟩
  have hli : LinearIndependent D c' := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have := congrArg (fun y : Y => h (b i : V) (y : V)) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul, h.map_sum_right, h.map_smul_right, c', hc,
      ZeroMemClass.coe_zero, map_zero_right] at this
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
    exact (RingInvo.conj_eq_zero_iff τ).1 this
  have hcard : Fintype.card ι = finrank D Y := by
    rw [hdim, Module.finrank_eq_card_basis b]
  set bY : Module.Basis ι D Y := basisOfLinearIndependentOfCardEqFinrank' c' hli hcard
  have hbY : ∀ j, (bY j : V) = c j := fun j => by
    simp [bY, c']
  set B : Module.Basis (ι ⊕ ι) D V :=
    (b.prod bY).map (Submodule.prodEquivOfIsCompl X Y hXY)
  have hBl : ∀ i, B (.inl i) = b i := fun i => by
    simp [B, Module.Basis.prod_apply]
  have hBr : ∀ j, B (.inr j) = c j := fun j => by
    simp [B, Module.Basis.prod_apply, hbY]
  refine ⟨⟨B, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩, fun i => hBl i, ?_, ?_⟩
  · rw [hBl, hBl]; exact hX.apply_eq_zero (b i).2 (b j).2
  · rw [hBr, hBr]; exact hY.apply_eq_zero (hcY i) (hcY j)
  · rw [hBl, hBr, hc]
  · apply le_antisymm
    · rw [StandardBasis.lagrangianFst, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (show B (.inl i) ∈ X from (hBl i).symm ▸ (b i).2)
    · intro x hx
      have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hx']
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by
          simp only [StandardBasis.fst, hBl]⟩)
  · apply le_antisymm
    · rw [StandardBasis.lagrangianSnd, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (show B (.inr i) ∈ Y from (hBr i).symm ▸ hcY i)
    · intro y hy
      have hy' : y = ∑ i, bY.repr ⟨y, hy⟩ i • (bY i : V) := by
        have := congrArg Subtype.val (bY.sum_repr ⟨y, hy⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hy']
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by
          simp only [StandardBasis.snd, hBr, hbY]⟩)

/-- GKT Lemma 4.9 across two spaces: for polarizations `V = X ⊕ Y` and `V' = X' ⊕ Y'` of two
non-degenerate spaces, every linear isomorphism `f : X ≅ X'` extends to an isometry `φ : V ≅ V'`
with `φ Y = Y'`. -/
theorem exists_isometryEquiv_extend [FiniteDimensional D V] {V' : Type*} [AddCommGroup V']
    [Module D V'] [FiniteDimensional D V'] {h' : EpsilonHermitianForm τ ε V'}
    (hh : h.Nondegenerate) (hh' : h'.Nondegenerate) {X Y : Submodule D V} {X' Y' : Submodule D V'}
    (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y) (hXY : IsCompl X Y)
    (hX' : h'.IsLagrangian X') (hY' : h'.IsLagrangian Y') (hX'Y' : IsCompl X' Y')
    (f : X ≃ₗ[D] X') :
    ∃ φ : IsometryEquiv h h', (∀ x : X, φ x = f x) ∧ Y.map φ.toLinearEquiv.toLinearMap = Y' := by
  classical
  set b := Module.finBasis D X
  obtain ⟨e, he, -, heY⟩ := exists_standardBasis hh hX hY hXY b
  obtain ⟨e', he', -, he'Y⟩ := exists_standardBasis hh' hX' hY' hX'Y' (b.map f)
  refine ⟨e.isometryEquiv e', fun x => ?_, ?_⟩
  · have key : (e.isometryEquiv e').toLinearEquiv.toLinearMap.comp X.subtype =
        X'.subtype.comp f.toLinearMap := by
      apply b.ext
      intro i
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv]
      rw [← he i, StandardBasis.fst, StandardBasis.isometryEquiv_apply_basis]
      have := he' i
      rw [StandardBasis.fst, Module.Basis.map_apply] at this
      exact this
    exact LinearMap.congr_fun key x
  · rw [← heY, ← he'Y, StandardBasis.lagrangianSnd, StandardBasis.lagrangianSnd,
      Submodule.map_span, ← Set.range_comp]
    have : ⇑(e.isometryEquiv e').toLinearEquiv.toLinearMap ∘ e.snd = e'.snd := funext fun i => by
      simp only [Function.comp_apply, LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv,
        StandardBasis.snd, StandardBasis.isometryEquiv_apply_basis]
    rw [this]

end EpsilonHermitianForm

end Langlands

end
