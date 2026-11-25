import Langlands.LinearAlgebra.EpsilonHermitian.Witt

/-!
# The Leray invariant of a triple of Lagrangians

GKT §4.2.2–§4.2.4: Lemma 4.12, Definition 4.13, Definition 4.15 with (4.2), Lemmas 4.16 and 4.17;
(4.3).

Let `h` be a non-degenerate `-ε`-Hermitian form on a finite-dimensional left `D`-module `V` (the
book's `W`). For a pairwise transverse triple `(X₁, X₂, X₃)` of Lagrangians, `V = X₃ ⊕ X₁`; let
`p : V → X₃` be the projection along `X₁`, so that for `x ∈ X₂`, `p x = x + b x` with `b x ∈ X₁`
(the book's `u = [[1, b], [0, 1]]` on `X₁ ⊕ X₂`, `u x = p x`). The Leray form on `X₂` is

`(x, x')_b = h (p x) x' = h (b x) x'`,

a non-degenerate `ε`-Hermitian form (Lemma 4.12); its isometry class is the Leray invariant
`L(X₁, X₂, X₃)` (Definition 4.13). For an arbitrary triple, with
`M = X₁ ∩ X₂ + X₂ ∩ X₃ + X₃ ∩ X₁`, the images `X_{iM}` of `Xᵢ ∩ M^⊥` in `M^⊥/M` are a pairwise
transverse triple of Lagrangians, and `L(X₁, X₂, X₃) = L(X₁M, X₂M, X₃M)` (Definition 4.15).
-/

noncomputable section

namespace Langlands

namespace EpsilonHermitianForm

open Module
open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V]

/-! ### Transverse triples -/

section Transverse

variable {ε' : ℤˣ} (h : EpsilonHermitianForm τ ε' V)

/-- A pairwise transverse triple of Lagrangians (GKT §4.2.2). -/
structure IsTransverseTriple (X₁ X₂ X₃ : Submodule D V) : Prop where
  isLagrangian₁ : h.IsLagrangian X₁
  isLagrangian₂ : h.IsLagrangian X₂
  isLagrangian₃ : h.IsLagrangian X₃
  disjoint₁₂ : Disjoint X₁ X₂
  disjoint₂₃ : Disjoint X₂ X₃
  disjoint₁₃ : Disjoint X₁ X₃

variable {h} {X₁ X₂ X₃ : Submodule D V}

theorem IsTransverseTriple.swap₁₂ (hT : h.IsTransverseTriple X₁ X₂ X₃) :
    h.IsTransverseTriple X₂ X₁ X₃ :=
  ⟨hT.2, hT.1, hT.3, hT.4.symm, hT.6, hT.5⟩

theorem IsTransverseTriple.swap₂₃ (hT : h.IsTransverseTriple X₁ X₂ X₃) :
    h.IsTransverseTriple X₁ X₃ X₂ :=
  ⟨hT.1, hT.3, hT.2, hT.6, hT.5.symm, hT.4⟩

theorem IsTransverseTriple.swap₁₃ (hT : h.IsTransverseTriple X₁ X₂ X₃) :
    h.IsTransverseTriple X₃ X₂ X₁ :=
  ⟨hT.3, hT.2, hT.1, hT.5.symm, hT.4.symm, hT.6.symm⟩

variable [FiniteDimensional D V]

theorem IsTransverseTriple.isCompl₃₁ (hT : h.IsTransverseTriple X₁ X₂ X₃)
    (hh : h.Nondegenerate) : IsCompl X₃ X₁ :=
  (hT.3.isCompl_iff_disjoint hh hT.1).2 hT.6.symm

theorem IsTransverseTriple.isCompl₁₂ (hT : h.IsTransverseTriple X₁ X₂ X₃)
    (hh : h.Nondegenerate) : IsCompl X₁ X₂ :=
  (hT.1.isCompl_iff_disjoint hh hT.2).2 hT.4

/-- The projection `p : V → V` onto `X₃` along `X₁` (so `p x = u x` for `x ∈ X₂`). -/
def lerayProj (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate) : V →ₗ[D] V :=
  X₃.projection X₁ (hT.isCompl₃₁ hh)

theorem lerayProj_mem (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate) (x : V) :
    lerayProj hT hh x ∈ X₃ :=
  Submodule.projection_apply_mem _ x

theorem lerayProj_sub_mem (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate) (x : V) :
    lerayProj hT hh x - x ∈ X₁ := by
  have := Submodule.sub_projection_mem (hT.isCompl₃₁ hh) x
  rw [← neg_sub]; exact X₁.neg_mem this

/-- `p x` is the only vector of `X₃` congruent to `x` modulo `X₁`. -/
theorem lerayProj_eq_of (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate) {x y : V}
    (hy : y ∈ X₃) (hxy : y - x ∈ X₁) : lerayProj hT hh x = y := by
  have h1 : lerayProj hT hh x - y ∈ X₃ := X₃.sub_mem (lerayProj_mem hT hh x) hy
  have h2 : lerayProj hT hh x - y ∈ X₁ := by
    have := X₁.sub_mem (lerayProj_sub_mem hT hh x) hxy
    rwa [sub_sub_sub_cancel_right] at this
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 hT.6 _ h2 h1)

end Transverse

/-! ### The Leray form of a transverse triple (GKT Lemma 4.12, Definition 4.13) -/

section LerayForm

variable {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional D V] {X₁ X₂ X₃ : Submodule D V}

/-- `h(p x, y) + h(x, p y) = 0` for `x, y ∈ X₂` (the computation of GKT Lemma 4.12). -/
theorem lerayProj_apply_add (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate)
    {x y : V} (hx : x ∈ X₂) (hy : y ∈ X₂) :
    h (lerayProj hT hh x) y + h x (lerayProj hT hh y) = 0 := by
  set px := lerayProj hT hh x
  set py := lerayProj hT hh y
  have hpp : h px py = 0 := hT.3.apply_eq_zero (lerayProj_mem hT hh x) (lerayProj_mem hT hh y)
  have hab : h (px - x) (py - y) = 0 :=
    hT.1.apply_eq_zero (lerayProj_sub_mem hT hh x) (lerayProj_sub_mem hT hh y)
  have hxy : h x y = 0 := hT.2.apply_eq_zero hx hy
  have : h px py = h px y + h x py + h (px - x) (py - y) - h x y := by
    simp only [h.map_sub_left, h.map_sub_right]; abel
  rw [hpp, hab, hxy, add_zero, sub_zero] at this
  exact this.symm

variable (h) in
/-- The Leray form `(x, x')_b = h (p x) x'` on `X₂` of a transverse triple (GKT §4.2.2): an
`ε`-Hermitian form, `h` being `-ε`-Hermitian (GKT Lemma 4.12). -/
def lerayForm (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate) :
    EpsilonHermitianForm τ ε X₂ where
  toFun x y := h (lerayProj hT hh x) y
  map_add_left' x y z := by
    simp only [Submodule.coe_add, map_add, h.map_add_left]
  map_smul_left' a x y := by
    simp only [Submodule.coe_smul, map_smul, h.map_smul_left]
  conj_swap' x y := by
    have e := lerayProj_apply_add hT hh x.2 y.2
    change h (lerayProj hT hh y) x = ((ε : ℤ) : D) * conj τ (h (lerayProj hT hh x) y)
    rw [h.conj_swap (x : V) (lerayProj hT hh y), Units.val_neg, Int.cast_neg,
      eq_neg_of_add_eq_zero_right e, RingInvo.conj_neg]
    noncomm_ring

theorem lerayForm_apply (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate) (x y : X₂) :
    h.lerayForm hT hh x y = h (lerayProj hT hh x) y := rfl

/-- The book's formula `(x, x')_b = ⟨b x, x'⟩` with `b x = p x - x ∈ X₁`. -/
theorem lerayForm_apply_eq_sub (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate)
    (x y : X₂) : h.lerayForm hT hh x y = h (lerayProj hT hh x - x) y := by
  rw [lerayForm_apply, h.map_sub_left, hT.2.apply_eq_zero x.2 y.2, sub_zero]

/-- The book's formula `(x, x')_b = ⟨u x, x'⟩` for any isometry `u` that is the identity on `X₁` and
maps `X₂` into `X₃` (GKT §4.2.2). -/
theorem lerayForm_apply_of_isometry (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate)
    (u : h.isometryGroup) (hu₁ : ∀ x ∈ X₁, (u : V ≃ₗ[D] V) x = x)
    (hu₂ : ∀ x ∈ X₂, (u : V ≃ₗ[D] V) x ∈ X₃) (x y : X₂) :
    h.lerayForm hT hh x y = h ((u : V ≃ₗ[D] V) x) y := by
  rw [lerayForm_apply, lerayProj_eq_of hT hh (hu₂ x x.2)]
  rw [← hT.1]
  intro z hz
  have e : h z ((u : V ≃ₗ[D] V) x) = h z x := by
    conv_lhs => rw [← hu₁ z hz]
    exact isometryGroup_apply u z x
  rw [h.apply_eq_zero_comm, h.map_sub_right, e, sub_self]

/-- The Leray form is non-degenerate (GKT Lemma 4.12). -/
theorem lerayForm_nondegenerate (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate) :
    (h.lerayForm hT hh).Nondegenerate := by
  intro x hx
  set a := lerayProj hT hh x - x
  have ha : ∀ v, h a v = 0 := by
    intro v
    have : v ∈ X₁ ⊔ X₂ := by rw [(hT.isCompl₁₂ hh).sup_eq_top]; trivial
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.1 this
    rw [h.map_add_right, hT.1.apply_eq_zero (lerayProj_sub_mem hT hh x) hv₁, zero_add]
    have := hx ⟨v₂, hv₂⟩
    rwa [lerayForm_apply_eq_sub] at this
  have ha0 : a = 0 := hh a ha
  have hx3 : (x : V) ∈ X₃ := by
    have := lerayProj_mem hT hh x
    rwa [sub_eq_zero.1 ha0] at this
  exact Subtype.ext (Submodule.disjoint_def.1 hT.5 _ x.2 hx3)

/-! ### Naturality and the action of the isometry group -/

section Naturality

variable {V' : Type*} [AddCommGroup V'] [Module D V'] [FiniteDimensional D V']
  {h' : EpsilonHermitianForm τ (-ε) V'} {Y₁ Y₂ Y₃ : Submodule D V'}

/-- An isometry `φ : V ≅ V'` carrying a transverse triple to another one is an isometry of the
Leray forms on `X₂` and `φ X₂` (the first half of GKT Lemma 4.17). -/
def lerayFormIsometryEquiv (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate)
    (hT' : h'.IsTransverseTriple Y₁ Y₂ Y₃) (hh' : h'.Nondegenerate) (φ : IsometryEquiv h h')
    (h₁ : X₁.map φ.toLinearEquiv.toLinearMap = Y₁) (h₂ : X₂.map φ.toLinearEquiv.toLinearMap = Y₂)
    (h₃ : X₃.map φ.toLinearEquiv.toLinearMap = Y₃) :
    IsometryEquiv (h.lerayForm hT hh) (h'.lerayForm hT' hh') where
  toLinearEquiv := (φ.toLinearEquiv.submoduleMap X₂).trans (LinearEquiv.ofEq _ _ h₂)
  map_app' x y := by
    change h' (lerayProj hT' hh' (φ x)) (φ y) = h (lerayProj hT hh x) y
    have : lerayProj hT' hh' (φ x) = φ (lerayProj hT hh x) := by
      apply lerayProj_eq_of
      · rw [← h₃]; exact ⟨_, lerayProj_mem hT hh x, rfl⟩
      · rw [← map_sub, ← h₁]
        exact ⟨_, lerayProj_sub_mem hT hh x, rfl⟩
    rw [this, φ.map_app]

end Naturality

/-- An element of the isometry group as an isometry of the space onto itself. -/
def isometryEquivOfIsometryGroup (g : h.isometryGroup) : IsometryEquiv h h where
  toLinearEquiv := g
  map_app' x y := g.2 x y

end LerayForm

/-! ### Permutations of the triple (GKT Lemma 4.16) -/

section Permutation

variable {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional D V] {X₁ X₂ X₃ : Submodule D V}

/-- An injective linear map between two submodules of the same dimension, as an equivalence. -/
private def equivOfInjective {A B : Submodule D V} (f : A →ₗ[D] B) (hf : Function.Injective f)
    (hd : finrank D A = finrank D B) : A ≃ₗ[D] B :=
  LinearEquiv.ofBijective f ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hf⟩

theorem finrank_eq_of_isLagrangian (hh : h.Nondegenerate) {A B : Submodule D V}
    (hA : h.IsLagrangian A) (hB : h.IsLagrangian B) : finrank D A = finrank D B := by
  have := hA.two_mul_finrank hh; have := hB.two_mul_finrank hh; omega

/-- GKT Lemma 4.16 for the transposition `(1 2)`: `L(X₂, X₁, X₃) = -L(X₁, X₂, X₃)`, through
`b : X₂ → X₁`, `x ↦ p x - x`. -/
theorem nonempty_isometryEquiv_lerayForm_swap₁₂ (hT : h.IsTransverseTriple X₁ X₂ X₃)
    (hh : h.Nondegenerate) :
    Nonempty (IsometryEquiv (-h.lerayForm hT hh) (h.lerayForm hT.swap₁₂ hh)) := by
  set b : X₂ →ₗ[D] X₁ := (lerayProj hT hh - LinearMap.id).comp X₂.subtype |>.codRestrict X₁
    (fun x => lerayProj_sub_mem hT hh x)
  have hb : ∀ x : X₂, (b x : V) = lerayProj hT hh x - x := fun _ => rfl
  have hinj : Function.Injective b := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h0 : lerayProj hT hh x = x := sub_eq_zero.1 (by rw [← hb, hx, Submodule.coe_zero])
    have : (x : V) ∈ X₃ := h0 ▸ lerayProj_mem hT hh x
    exact (Submodule.mem_bot D).2 (Subtype.ext (Submodule.disjoint_def.1 hT.5 _ x.2 this))
  set e := equivOfInjective b hinj (finrank_eq_of_isLagrangian hh hT.2 hT.1)
  refine ⟨⟨e, fun x y => ?_⟩⟩
  change h (lerayProj hT.swap₁₂ hh (b x)) (b y) = -h (lerayProj hT hh x) y
  have hp : lerayProj hT.swap₁₂ hh (b x) = lerayProj hT hh x := by
    apply lerayProj_eq_of _ hh (lerayProj_mem hT hh x)
    rw [hb, sub_sub_cancel]; exact x.2
  rw [hp, hb, h.map_sub_right, hT.3.apply_eq_zero (lerayProj_mem hT hh x) (lerayProj_mem hT hh y),
    zero_sub, eq_neg_of_add_eq_zero_left (lerayProj_apply_add hT hh x.2 y.2), neg_neg]

/-- GKT Lemma 4.16 for the transposition `(2 3)`: `L(X₁, X₃, X₂) = -L(X₁, X₂, X₃)`, through
`u = p : X₂ → X₃`. -/
theorem nonempty_isometryEquiv_lerayForm_swap₂₃ (hT : h.IsTransverseTriple X₁ X₂ X₃)
    (hh : h.Nondegenerate) :
    Nonempty (IsometryEquiv (-h.lerayForm hT hh) (h.lerayForm hT.swap₂₃ hh)) := by
  set u : X₂ →ₗ[D] X₃ := ((lerayProj hT hh).comp X₂.subtype).codRestrict X₃
    (fun x => lerayProj_mem hT hh x)
  have hu : ∀ x : X₂, (u x : V) = lerayProj hT hh x := fun _ => rfl
  have hinj : Function.Injective u := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h0 : lerayProj hT hh x = 0 := by rw [← hu, hx, Submodule.coe_zero]
    have : (x : V) ∈ X₁ := by
      have := lerayProj_sub_mem hT hh x; rw [h0, zero_sub] at this; simpa using this
    exact (Submodule.mem_bot D).2 (Subtype.ext (Submodule.disjoint_def.1 hT.4 _ this x.2))
  set e := equivOfInjective u hinj (finrank_eq_of_isLagrangian hh hT.2 hT.3)
  refine ⟨⟨e, fun x y => ?_⟩⟩
  change h (lerayProj hT.swap₂₃ hh (u x)) (u y) = -h (lerayProj hT hh x) y
  have hp : lerayProj hT.swap₂₃ hh (u x) = x := by
    apply lerayProj_eq_of _ hh x.2
    rw [hu, ← neg_sub]; exact X₁.neg_mem (lerayProj_sub_mem hT hh x)
  rw [hp, hu, ← eq_neg_of_add_eq_zero_right (lerayProj_apply_add hT hh x.2 y.2)]

/-- GKT Lemma 4.16 for the transposition `(1 3)`: `L(X₃, X₂, X₁) = -L(X₁, X₂, X₃)`, through the
identity of `X₂`. -/
theorem nonempty_isometryEquiv_lerayForm_swap₁₃ (hT : h.IsTransverseTriple X₁ X₂ X₃)
    (hh : h.Nondegenerate) :
    Nonempty (IsometryEquiv (-h.lerayForm hT hh) (h.lerayForm hT.swap₁₃ hh)) := by
  refine ⟨⟨LinearEquiv.refl D X₂, fun x y => ?_⟩⟩
  change h (lerayProj hT.swap₁₃ hh x) y = -h (lerayProj hT hh x) y
  have hp : lerayProj hT.swap₁₃ hh x = x - lerayProj hT hh x := by
    apply lerayProj_eq_of _ hh
    · rw [← neg_sub]; exact X₁.neg_mem (lerayProj_sub_mem hT hh x)
    · rw [sub_sub_cancel_left]; exact X₃.neg_mem (lerayProj_mem hT hh x)
  rw [hp, h.map_sub_left, hT.2.apply_eq_zero x.2 y.2, zero_sub]

end Permutation

/-! ### Transverse triples with isometric Leray forms are conjugate (GKT Lemma 4.17) -/

section Conjugate

variable {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional D V] {X₁ X₂ X₃ : Submodule D V}
  {V' : Type*} [AddCommGroup V'] [Module D V'] [FiniteDimensional D V']
  {h' : EpsilonHermitianForm τ (-ε) V'} {Y₁ Y₂ Y₃ : Submodule D V'}

/-- GKT Lemma 4.17 (in the form of two spaces): two transverse triples are carried to each other by
an isometry if and only if their Leray forms are isometric. -/
theorem exists_isometryEquiv_iff_lerayForm (hT : h.IsTransverseTriple X₁ X₂ X₃)
    (hh : h.Nondegenerate) (hT' : h'.IsTransverseTriple Y₁ Y₂ Y₃) (hh' : h'.Nondegenerate) :
    (∃ φ : IsometryEquiv h h', X₁.map φ.toLinearEquiv.toLinearMap = Y₁ ∧
        X₂.map φ.toLinearEquiv.toLinearMap = Y₂ ∧ X₃.map φ.toLinearEquiv.toLinearMap = Y₃) ↔
      Nonempty (IsometryEquiv (h.lerayForm hT hh) (h'.lerayForm hT' hh')) := by
  constructor
  · rintro ⟨φ, h₁, h₂, h₃⟩
    exact ⟨lerayFormIsometryEquiv hT hh hT' hh' φ h₁ h₂ h₃⟩
  · rintro ⟨σ⟩
    obtain ⟨φ, hφ₂, hφ₁⟩ := exists_isometryEquiv_extend hh hh' hT.2 hT.1 (hT.isCompl₁₂ hh).symm
      hT'.2 hT'.1 (hT'.isCompl₁₂ hh').symm σ.toLinearEquiv
    have hφ₂' : X₂.map φ.toLinearEquiv.toLinearMap = Y₂ := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, hφ₂ ⟨x, hx⟩]
        exact (σ ⟨x, hx⟩).2
      · intro y hy
        refine ⟨(σ.symm ⟨y, hy⟩ : X₂), (σ.symm ⟨y, hy⟩).2, ?_⟩
        rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, hφ₂]
        change ((σ (σ.symm ⟨y, hy⟩) : Y₂) : V') = y
        rw [IsometryEquiv.apply_symm_apply]
    refine ⟨φ, hφ₁, hφ₂', ?_⟩
    -- `φ X₃ ⊆ Y₃^⊥ = Y₃`, and both are Lagrangians
    have hle : X₃.map φ.toLinearEquiv.toLinearMap ≤ Y₃ := by
      rw [← hT'.3]
      rintro _ ⟨z, hz, rfl⟩
      set x : X₂ := ⟨X₂.projection X₁ (hT.isCompl₁₂ hh).symm z, Submodule.projection_apply_mem _ z⟩
      have hzx : lerayProj hT hh x = z :=
        lerayProj_eq_of hT hh hz (Submodule.sub_projection_mem _ z)
      intro w hw
      set y : Y₂ :=
        ⟨Y₂.projection Y₁ (hT'.isCompl₁₂ hh').symm w, Submodule.projection_apply_mem _ w⟩
      have hwy : lerayProj hT' hh' y = w :=
        lerayProj_eq_of hT' hh' hw (Submodule.sub_projection_mem _ w)
      set a := lerayProj hT hh x - x
      have ha : a ∈ X₁ := lerayProj_sub_mem hT hh x
      have hφa : φ a ∈ Y₁ := by rw [← hφ₁]; exact ⟨a, ha, rfl⟩
      have hφx : φ (x : V) = (σ x : V') := hφ₂ x
      have hσy : φ ((σ.symm y : X₂) : V) = y := by
        rw [hφ₂]; congr 1; exact σ.apply_symm_apply y
      have hz' : (z : V) = x + a := by rw [← hzx, add_sub_cancel]
      have hw' : w = y + (lerayProj hT' hh' y - y) := by rw [add_sub_cancel, hwy]
      change h' (φ z) w = 0
      rw [hz', map_add, hφx, h'.map_add_left]
      have e1 : h' (σ x : V') w = -h' (lerayProj hT' hh' (σ x)) y := by
        rw [← hwy]; exact eq_neg_of_add_eq_zero_right (lerayProj_apply_add hT' hh' (σ x).2 y.2)
      have e2 : h' (φ a) w = h' (lerayProj hT' hh' (σ x)) y := by
        have e3 : h' (φ a) w = h' (φ a) y := by
          rw [hw', h'.map_add_right, hT'.1.apply_eq_zero hφa (lerayProj_sub_mem hT' hh' y),
            add_zero]
        have e4 : h' (φ a) y = h a ((σ.symm y : X₂) : V) := by
          conv_lhs => rw [← hσy]
          exact φ.map_app _ _
        have e5 : h a ((σ.symm y : X₂) : V) = h.lerayForm hT hh x (σ.symm y) :=
          (lerayForm_apply_eq_sub hT hh x _).symm
        have e6 : h.lerayForm hT hh x (σ.symm y) = h'.lerayForm hT' hh' (σ x) y := by
          have := σ.map_app x (σ.symm y)
          rw [IsometryEquiv.apply_symm_apply] at this
          exact this.symm
        rw [e3, e4, e5, e6]; rfl
      rw [e1, e2, neg_add_cancel]
    have hL : h'.IsLagrangian (X₃.map φ.toLinearEquiv.toLinearMap) := by
      rw [IsLagrangian, ← φ.map_orthogonal, hT.3]
    apply le_antisymm hle
    calc Y₃ = h'.orthogonal Y₃ := hT'.3.symm
      _ ≤ h'.orthogonal (X₃.map φ.toLinearEquiv.toLinearMap) := orthogonal_le_orthogonal hle
      _ = _ := hL

end Conjugate

/-! ### Isometries of `M^⊥/M` induced by isometries of the space -/

section ReductionEquiv

variable {ε' : ℤˣ} {h : EpsilonHermitianForm τ ε' V}
  {V' : Type*} [AddCommGroup V'] [Module D V'] {h' : EpsilonHermitianForm τ ε' V'}

/-- An isometry `φ : V ≅ V'` with `φ M = M'` induces an isometry `M^⊥/M ≅ M'^⊥/M'`. -/
def reductionEquiv (φ : IsometryEquiv h h') {M : Submodule D V} {M' : Submodule D V'}
    (hM : M.map φ.toLinearEquiv.toLinearMap = M') :
    IsometryEquiv (h.reduction M) (h'.reduction M') :=
  let e : h.orthogonal M ≃ₗ[D] h'.orthogonal M' :=
    (φ.toLinearEquiv.submoduleMap (h.orthogonal M)).trans
      (LinearEquiv.ofEq _ _ (by rw [φ.map_orthogonal, hM]))
  { toLinearEquiv := Submodule.Quotient.equiv (M.comap (h.orthogonal M).subtype)
      (M'.comap (h'.orthogonal M').subtype) e (by
        ext x
        simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
          LinearEquiv.coe_coe]
        constructor
        · rintro ⟨y, hy, rfl⟩
          have : φ (y : V) ∈ M' := hM ▸ ⟨(y : V), hy, rfl⟩
          exact this
        · intro hx
          have hx' : (x : V') ∈ M.map φ.toLinearEquiv.toLinearMap := hM.symm ▸ hx
          obtain ⟨y, hy, hyx⟩ := hx'
          refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
          have : ((e.symm x : h.orthogonal M) : V) = y := by
            apply φ.toLinearEquiv.injective
            have hyx' : φ.toLinearEquiv y = x := hyx
            rw [hyx']
            exact congrArg Subtype.val (e.apply_symm_apply x)
          rw [this]; exact hy)
    map_app' := fun a b => by
      induction a using Submodule.Quotient.induction_on
      induction b using Submodule.Quotient.induction_on
      exact φ.map_app _ _ }

theorem reductionEquiv_apply_mk (φ : IsometryEquiv h h') {M : Submodule D V}
    {M' : Submodule D V'} (hM : M.map φ.toLinearEquiv.toLinearMap = M') (x : h.orthogonal M) :
    ((reductionEquiv φ hM (h.reductionMap M x)) : h'.ReductionSpace M') =
      h'.reductionMap M' ⟨φ x, by
        rw [← hM, ← φ.map_orthogonal]; exact ⟨x, x.2, rfl⟩⟩ := rfl

theorem map_reductionSubmodule (φ : IsometryEquiv h h') {M : Submodule D V} {M' : Submodule D V'}
    (hM : M.map φ.toLinearEquiv.toLinearMap = M') (X : Submodule D V) :
    (h.reductionSubmodule M X).map (reductionEquiv φ hM).toLinearEquiv.toLinearMap =
      h'.reductionSubmodule M' (X.map φ.toLinearEquiv.toLinearMap) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨x, hxX, rfl⟩ := mem_reductionSubmodule.1 hb
    exact mem_reductionSubmodule.2 ⟨_, ⟨x, hxX, rfl⟩, rfl⟩
  · intro ha
    obtain ⟨y, ⟨x, hxX, hxy⟩, rfl⟩ := mem_reductionSubmodule.1 ha
    have hxM : x ∈ h.orthogonal M := by
      have : φ x ∈ h'.orthogonal M' := hxy ▸ y.2
      rw [← hM, ← φ.map_orthogonal] at this
      obtain ⟨x', hx', hx'x⟩ := this
      have : x' = x := φ.toLinearEquiv.injective hx'x
      exact this ▸ hx'
    refine ⟨h.reductionMap M ⟨x, hxM⟩, mem_reductionSubmodule.2 ⟨⟨x, hxM⟩, hxX, rfl⟩, ?_⟩
    change reductionEquiv φ hM (h.reductionMap M ⟨x, hxM⟩) = _
    rw [reductionEquiv_apply_mk]
    congr 1
    exact Subtype.ext hxy

/-- For `M = 0`, the space `M^⊥/M` is the space itself. -/
def reductionEquivOfEqBot (M : Submodule D V) (hM : M = ⊥) : IsometryEquiv (h.reduction M) h where
  toLinearEquiv := (Submodule.quotEquivOfEqBot (M.comap (h.orthogonal M).subtype) (by
      rw [hM, Submodule.comap_bot, Submodule.ker_subtype])).trans
    (LinearEquiv.ofTop (h.orthogonal M) (by rw [hM, orthogonal_bot]))
  map_app' a b := by
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    rfl

theorem map_reductionSubmodule_eqBot (M : Submodule D V) (hM : M = ⊥) (X : Submodule D V) :
    (h.reductionSubmodule M X).map (reductionEquivOfEqBot (h := h) M hM).toLinearEquiv.toLinearMap
      = X := by
  ext v
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hxX, rfl⟩ := mem_reductionSubmodule.1 ha
    exact hxX
  · intro hv
    have hvM : v ∈ h.orthogonal M := by rw [hM, orthogonal_bot]; trivial
    exact ⟨h.reductionMap M ⟨v, hvM⟩, mem_reductionSubmodule.2 ⟨⟨v, hvM⟩, hv, rfl⟩, rfl⟩

end ReductionEquiv

/-! ### The Leray invariant of an arbitrary triple (GKT Definition 4.15) -/

section General

/-- The isotropic subspace `M(X₁, X₂, X₃) = X₁ ∩ X₂ + X₂ ∩ X₃ + X₃ ∩ X₁` (GKT §4.2.3). -/
def lerayM (X₁ X₂ X₃ : Submodule D V) : Submodule D V := X₁ ⊓ X₂ ⊔ X₂ ⊓ X₃ ⊔ X₃ ⊓ X₁

theorem lerayM_comm₁₂ (X₁ X₂ X₃ : Submodule D V) : lerayM X₂ X₁ X₃ = lerayM X₁ X₂ X₃ := by
  unfold lerayM; ac_rfl

theorem lerayM_comm₂₃ (X₁ X₂ X₃ : Submodule D V) : lerayM X₁ X₃ X₂ = lerayM X₁ X₂ X₃ := by
  unfold lerayM; ac_rfl

theorem lerayM_rotate (X₁ X₂ X₃ : Submodule D V) : lerayM X₂ X₃ X₁ = lerayM X₁ X₂ X₃ := by
  unfold lerayM; ac_rfl

theorem lerayM_eq_bot {X₁ X₂ X₃ : Submodule D V} (h₁₂ : Disjoint X₁ X₂) (h₂₃ : Disjoint X₂ X₃)
    (h₁₃ : Disjoint X₁ X₃) : lerayM X₁ X₂ X₃ = ⊥ := by
  simp [lerayM, disjoint_iff.1 h₁₂, disjoint_iff.1 h₂₃, disjoint_iff.1 h₁₃.symm]

/-- `(X₁ + M) ∩ (X₂ + M) = M`: the images of `X₁` and `X₂` in `M^⊥/M` are transverse. -/
theorem sup_lerayM_inf_sup_lerayM (X₁ X₂ X₃ : Submodule D V) :
    (X₁ ⊔ lerayM X₁ X₂ X₃) ⊓ (X₂ ⊔ lerayM X₁ X₂ X₃) = lerayM X₁ X₂ X₃ := by
  apply le_antisymm _ (le_inf le_sup_right le_sup_right)
  rintro v ⟨hv₁, hv₂⟩
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.1 hv₁
  obtain ⟨m₁₂, hm₁₂, m₃, hm₃, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.1 hm₁₂
  obtain ⟨b, hb, n, hn, hbn⟩ := Submodule.mem_sup.1 hv₂
  obtain ⟨n₁₂, hn₁₂, n₃, hn₃, rfl⟩ := Submodule.mem_sup.1 hn
  obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := Submodule.mem_sup.1 hn₁₂
  -- `v = a' + m₂ = b' + n₃` with `a' ∈ X₁`, `m₂ ∈ X₂ ∩ X₃`, `b' ∈ X₂`, `n₃ ∈ X₃ ∩ X₁`
  set a' := a + m₁ + m₃
  have ha' : a' ∈ X₁ := X₁.add_mem (X₁.add_mem ha hm₁.1) hm₃.2
  set b' := b + n₁ + n₂
  have hb' : b' ∈ X₂ := X₂.add_mem (X₂.add_mem hb hn₁.2) hn₂.1
  have hv : a + (m₁ + m₂ + m₃) = a' + m₂ := by simp only [a']; abel
  have hv' : a + (m₁ + m₂ + m₃) = b' + n₃ := by rw [← hbn]; simp only [b']; abel
  have hab : a' - n₃ ∈ X₁ ⊓ X₂ := ⟨X₁.sub_mem ha' hn₃.2, by
    have : a' - n₃ = b' - m₂ := by
      rw [sub_eq_sub_iff_add_eq_add, ← hv', hv, add_comm]
    rw [this]; exact X₂.sub_mem hb' hm₂.1⟩
  rw [hv, show a' + m₂ = (a' - n₃) + m₂ + n₃ by abel]
  exact Submodule.add_mem_sup (Submodule.add_mem_sup hab hm₂) hn₃

variable {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional D V] {X₁ X₂ X₃ : Submodule D V}

omit [FiniteDimensional D V] in
private theorem le_orthogonal_of_le_lagrangian {X A B : Submodule D V} (hX : h.IsLagrangian X)
    (hA : A ≤ X) (hB : B ≤ X) : A ≤ h.orthogonal B :=
  hA.trans (hX.symm.le.trans (orthogonal_le_orthogonal hB))

omit [FiniteDimensional D V] in
theorem isTotallyIsotropic_lerayM (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) : h.IsTotallyIsotropic (lerayM X₁ X₂ X₃) := by
  rw [isTotallyIsotropic_iff_le_orthogonal]
  simp only [lerayM, orthogonal_sup, sup_le_iff, le_inf_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
  all_goals first
    | exact le_orthogonal_of_le_lagrangian h₁ inf_le_left inf_le_left
    | exact le_orthogonal_of_le_lagrangian h₁ inf_le_left inf_le_right
    | exact le_orthogonal_of_le_lagrangian h₁ inf_le_right inf_le_left
    | exact le_orthogonal_of_le_lagrangian h₁ inf_le_right inf_le_right
    | exact le_orthogonal_of_le_lagrangian h₂ inf_le_left inf_le_left
    | exact le_orthogonal_of_le_lagrangian h₂ inf_le_left inf_le_right
    | exact le_orthogonal_of_le_lagrangian h₂ inf_le_right inf_le_left
    | exact le_orthogonal_of_le_lagrangian h₃ inf_le_left inf_le_right
    | exact le_orthogonal_of_le_lagrangian h₃ inf_le_right inf_le_left

omit [FiniteDimensional D V] in
/-- A vector of `M^⊥` whose class lies in `X_M` lies in `X + M`. -/
private theorem mem_sup_of_reductionMap_mem {M X : Submodule D V} {w : h.orthogonal M}
    (hw : h.reductionMap M w ∈ h.reductionSubmodule M X) : (w : V) ∈ X ⊔ M := by
  obtain ⟨x, hxX, hxw⟩ := mem_reductionSubmodule.1 hw
  rw [← sub_eq_zero, ← map_sub, reductionMap_eq_zero_iff] at hxw
  have : (w : V) = x + -((x : V) - w) := by abel
  rw [this]
  exact Submodule.add_mem_sup hxX (M.neg_mem (by simpa using hxw))

omit [FiniteDimensional D V] in
private theorem disjoint_reductionSubmodule {A B : Submodule D V}
    (hAB : (A ⊔ lerayM X₁ X₂ X₃) ⊓ (B ⊔ lerayM X₁ X₂ X₃) = lerayM X₁ X₂ X₃) :
    Disjoint (h.reductionSubmodule (lerayM X₁ X₂ X₃) A)
      (h.reductionSubmodule (lerayM X₁ X₂ X₃) B) := by
  rw [Submodule.disjoint_def]
  intro a haA haB
  obtain ⟨w, rfl⟩ := h.reductionMap_surjective _ a
  rw [reductionMap_eq_zero_iff]
  have hmem : (w : V) ∈ (A ⊔ lerayM X₁ X₂ X₃) ⊓ (B ⊔ lerayM X₁ X₂ X₃) :=
    ⟨mem_sup_of_reductionMap_mem haA, mem_sup_of_reductionMap_mem haB⟩
  rw [hAB] at hmem
  exact hmem

/-- The images `X_{iM}` of a triple of Lagrangians in `M^⊥/M` form a transverse triple
(GKT §4.2.3, before Definition 4.15). -/
theorem isTransverseTriple_reduction (hh : h.Nondegenerate) (h₁ : h.IsLagrangian X₁)
    (h₂ : h.IsLagrangian X₂) (h₃ : h.IsLagrangian X₃) :
    (h.reduction (lerayM X₁ X₂ X₃)).IsTransverseTriple (h.reductionSubmodule (lerayM X₁ X₂ X₃) X₁)
      (h.reductionSubmodule (lerayM X₁ X₂ X₃) X₂) (h.reductionSubmodule (lerayM X₁ X₂ X₃) X₃) := by
  have hM := isTotallyIsotropic_lerayM h₁ h₂ h₃
  refine ⟨h₁.reduction hh hM, h₂.reduction hh hM, h₃.reduction hh hM, ?_, ?_, ?_⟩
  · exact disjoint_reductionSubmodule (sup_lerayM_inf_sup_lerayM X₁ X₂ X₃)
  · apply disjoint_reductionSubmodule
    have := sup_lerayM_inf_sup_lerayM X₂ X₃ X₁
    rwa [lerayM_rotate] at this
  · apply disjoint_reductionSubmodule
    have := sup_lerayM_inf_sup_lerayM X₁ X₃ X₂
    rwa [lerayM_comm₂₃] at this

variable (h) in
/-- The Leray invariant of an arbitrary triple of Lagrangians (GKT Definition 4.15, (4.2)): the
Leray form of the transverse triple `(X₁M, X₂M, X₃M)` of `M^⊥/M`, an `ε`-Hermitian form on `X₂M`. -/
def lerayInvariant (hh : h.Nondegenerate) (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) :
    EpsilonHermitianForm τ ε (h.reductionSubmodule (lerayM X₁ X₂ X₃) X₂) :=
  (h.reduction _).lerayForm (isTransverseTriple_reduction hh h₁ h₂ h₃)
    (reduction_nondegenerate hh _)

theorem lerayInvariant_nondegenerate (hh : h.Nondegenerate) (h₁ : h.IsLagrangian X₁)
    (h₂ : h.IsLagrangian X₂) (h₃ : h.IsLagrangian X₃) :
    (h.lerayInvariant hh h₁ h₂ h₃).Nondegenerate :=
  lerayForm_nondegenerate _ _

/-- For a transverse triple, the Leray invariant of Definition 4.15 is that of Definition 4.13. -/
theorem nonempty_isometryEquiv_lerayInvariant_lerayForm (hh : h.Nondegenerate)
    (hT : h.IsTransverseTriple X₁ X₂ X₃) :
    Nonempty (IsometryEquiv (h.lerayInvariant hh hT.1 hT.2 hT.3) (h.lerayForm hT hh)) :=
  ⟨lerayFormIsometryEquiv _ _ hT hh (reductionEquivOfEqBot _ (lerayM_eq_bot hT.4 hT.5 hT.6))
    (map_reductionSubmodule_eqBot _ _ _) (map_reductionSubmodule_eqBot _ _ _)
    (map_reductionSubmodule_eqBot _ _ _)⟩

omit [FiniteDimensional D V] in
theorem IsLagrangian.map_isometryEquiv {V' : Type*} [AddCommGroup V'] [Module D V']
    {h' : EpsilonHermitianForm τ (-ε) V'} {X : Submodule D V} (hX : h.IsLagrangian X)
    (φ : IsometryEquiv h h') : h'.IsLagrangian (X.map φ.toLinearEquiv.toLinearMap) := by
  rw [IsLagrangian, ← φ.map_orthogonal, hX]

omit [FiniteDimensional D V] in
theorem map_lerayM {V' : Type*} [AddCommGroup V'] [Module D V'] (f : V ≃ₗ[D] V')
    (X₁ X₂ X₃ : Submodule D V) :
    (lerayM X₁ X₂ X₃).map f.toLinearMap =
      lerayM (X₁.map f.toLinearMap) (X₂.map f.toLinearMap) (X₃.map f.toLinearMap) := by
  simp only [lerayM, Submodule.map_sup, Submodule.map_inf _ f.injective]

/-- The Leray invariant is invariant under isometries (GKT (4.3), for an isometry between two
spaces). -/
theorem nonempty_isometryEquiv_lerayInvariant_map {V' : Type*} [AddCommGroup V'] [Module D V']
    [FiniteDimensional D V'] {h' : EpsilonHermitianForm τ (-ε) V'} (hh : h.Nondegenerate)
    (hh' : h'.Nondegenerate) (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) (φ : IsometryEquiv h h') :
    Nonempty (IsometryEquiv (h.lerayInvariant hh h₁ h₂ h₃)
      (h'.lerayInvariant hh' (h₁.map_isometryEquiv φ) (h₂.map_isometryEquiv φ)
        (h₃.map_isometryEquiv φ))) :=
  ⟨lerayFormIsometryEquiv _ _ _ _ (reductionEquiv φ (map_lerayM φ.toLinearEquiv X₁ X₂ X₃))
    (map_reductionSubmodule _ _ _) (map_reductionSubmodule _ _ _)
    (map_reductionSubmodule _ _ _)⟩

/-- GKT (4.3): `L(g X₁, g X₂, g X₃) = L(X₁, X₂, X₃)` for `g` in the isometry group. -/
theorem nonempty_isometryEquiv_lerayInvariant_map_isometryGroup (hh : h.Nondegenerate)
    (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂) (h₃ : h.IsLagrangian X₃)
    (g : h.isometryGroup) :
    Nonempty (IsometryEquiv (h.lerayInvariant hh h₁ h₂ h₃)
      (h.lerayInvariant hh (h₁.map g) (h₂.map g) (h₃.map g))) :=
  nonempty_isometryEquiv_lerayInvariant_map hh hh h₁ h₂ h₃ (isometryEquivOfIsometryGroup g)

end General

/-! ### Similitudes (GKT Proposition 4.26) -/

section Similitude

variable {ε'' : ℤˣ} {k : EpsilonHermitianForm τ ε'' V} {a : D} (ha : a ≠ 0)
  (hac : ∀ d : D, a * d = d * a) (haτ : conj τ a = a)

include ha in
theorem orthogonal_smul (U : Submodule D V) : (k.smul a hac haτ).orthogonal U = k.orthogonal U := by
  ext v
  simp only [mem_orthogonal, smul_apply]
  exact forall₂_congr fun u _ => ⟨fun e => (mul_eq_zero.1 e).resolve_left ha,
    fun e => by rw [e, mul_zero]⟩

include ha in
theorem isLagrangian_smul_iff {X : Submodule D V} :
    (k.smul a hac haτ).IsLagrangian X ↔ k.IsLagrangian X := by
  rw [IsLagrangian, IsLagrangian, orthogonal_smul ha]

include ha in
theorem nondegenerate_smul (hk : k.Nondegenerate) : (k.smul a hac haτ).Nondegenerate :=
  fun x hx => hk x fun y => (mul_eq_zero.1 (hx y)).resolve_left ha

/-- Scaling the form scales the Leray form of a transverse triple. -/
theorem lerayForm_smul {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional D V]
    {X₁ X₂ X₃ : Submodule D V} (hT : h.IsTransverseTriple X₁ X₂ X₃) (hh : h.Nondegenerate)
    (hT' : (h.smul a hac haτ).IsTransverseTriple X₁ X₂ X₃)
    (hh' : (h.smul a hac haτ).Nondegenerate) :
    (h.smul a hac haτ).lerayForm hT' hh' = (h.lerayForm hT hh).smul a hac haτ := by
  ext x y
  rfl

/-- The reduction of a scaled form is the scaled reduction. -/
def reductionSmulEquiv (M : Submodule D V) :
    IsometryEquiv ((k.smul a hac haτ).reduction M) ((k.reduction M).smul a hac haτ) where
  toLinearEquiv :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (orthogonal_smul ha hac haτ M))
    (by ext x; simp)
  map_app' x y := by
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    rfl

theorem map_reductionSmulEquiv (M X : Submodule D V) :
    ((k.smul a hac haτ).reductionSubmodule M X).map
        (reductionSmulEquiv ha hac haτ M).toLinearEquiv.toLinearMap =
      k.reductionSubmodule M X := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨x, hxX, rfl⟩ := mem_reductionSubmodule.1 hc
    exact mem_reductionSubmodule.2 ⟨⟨x, (orthogonal_smul ha hac haτ M) ▸ x.2⟩, hxX, rfl⟩
  · intro hb
    obtain ⟨x, hxX, rfl⟩ := mem_reductionSubmodule.1 hb
    refine ⟨(k.smul a hac haτ).reductionMap M ⟨x, (orthogonal_smul ha hac haτ M).symm ▸ x.2⟩,
      mem_reductionSubmodule.2 ⟨_, hxX, rfl⟩, rfl⟩

include ha in
/-- GKT Proposition 4.26: for a similitude `T : V → V'` with factor `a` (`a` central and fixed by
`τ`), `L(T X₁, T X₂, T X₃) = a L(X₁, X₂, X₃)`. -/
theorem nonempty_isometryEquiv_lerayInvariant_similitude {h : EpsilonHermitianForm τ (-ε) V}
    [FiniteDimensional D V] {V' : Type*} [AddCommGroup V'] [Module D V'] [FiniteDimensional D V']
    {h' : EpsilonHermitianForm τ (-ε) V'} (hh : h.Nondegenerate) (hh' : h'.Nondegenerate)
    {X₁ X₂ X₃ : Submodule D V} (h₁ : h.IsLagrangian X₁) (h₂ : h.IsLagrangian X₂)
    (h₃ : h.IsLagrangian X₃) (T : V ≃ₗ[D] V') (hT : ∀ x y, h' (T x) (T y) = a * h x y) :
    ∃ (k₁ : h'.IsLagrangian (X₁.map T.toLinearMap)) (k₂ : h'.IsLagrangian (X₂.map T.toLinearMap))
      (k₃ : h'.IsLagrangian (X₃.map T.toLinearMap)),
      Nonempty (IsometryEquiv ((h.lerayInvariant hh h₁ h₂ h₃).smul a hac haτ)
        (h'.lerayInvariant hh' k₁ k₂ k₃)) := by
  set φ : IsometryEquiv (h.smul a hac haτ) h' := ⟨T, hT⟩
  have hs₁ := (isLagrangian_smul_iff ha hac haτ).2 h₁
  have hs₂ := (isLagrangian_smul_iff ha hac haτ).2 h₂
  have hs₃ := (isLagrangian_smul_iff ha hac haτ).2 h₃
  have hsh := nondegenerate_smul ha hac haτ hh
  refine ⟨hs₁.map_isometryEquiv φ, hs₂.map_isometryEquiv φ, hs₃.map_isometryEquiv φ, ?_⟩
  obtain ⟨e₁⟩ := nonempty_isometryEquiv_lerayInvariant_map hsh hh' hs₁ hs₂ hs₃ φ
  -- `L_{a h}(X) = a L_h(X)`
  set M := lerayM X₁ X₂ X₃
  have hT₀ := isTransverseTriple_reduction hh h₁ h₂ h₃
  have hT' : ((h.reduction M).smul a hac haτ).IsTransverseTriple (h.reductionSubmodule M X₁)
      (h.reductionSubmodule M X₂) (h.reductionSubmodule M X₃) :=
    ⟨(isLagrangian_smul_iff ha hac haτ).2 hT₀.1, (isLagrangian_smul_iff ha hac haτ).2 hT₀.2,
      (isLagrangian_smul_iff ha hac haτ).2 hT₀.3, hT₀.4, hT₀.5, hT₀.6⟩
  have hnd' := nondegenerate_smul ha hac haτ (reduction_nondegenerate hh M)
  have e₂ := lerayFormIsometryEquiv (isTransverseTriple_reduction hsh hs₁ hs₂ hs₃)
    (reduction_nondegenerate hsh M) hT' hnd' (reductionSmulEquiv ha hac haτ M)
    (map_reductionSmulEquiv ha hac haτ M X₁) (map_reductionSmulEquiv ha hac haτ M X₂)
    (map_reductionSmulEquiv ha hac haτ M X₃)
  rw [lerayForm_smul hac haτ hT₀ (reduction_nondegenerate hh M) hT' hnd'] at e₂
  exact ⟨e₂.symm.trans e₁⟩

end Similitude

end EpsilonHermitianForm

end Langlands

end
