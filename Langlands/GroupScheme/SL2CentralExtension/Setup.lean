import Langlands.AbelianScheme.GroupScheme
import Langlands.GroupScheme.SL2CentralExtension.Covers
import Langlands.GroupScheme.SL2CentralExtension.Matrices
import Mathlib.Tactic.Group

/-! # Abstract central extensions of `SL₂` on points, and commutators of local lifts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

/-- Restriction of determinant-one matrices along a morphism of test schemes. -/
abbrev res {V T : Over S} (g : V ⟶ T) : Mat.SL2 Γ(T.left, ⊤) →* Mat.SL2 Γ(V.left, ⊤) :=
  Matrix.SpecialLinearGroup.map (ring g)

theorem res_comp {W V T : Over S} (k : W ⟶ V) (g : V ⟶ T) (m : Mat.SL2 Γ(T.left, ⊤)) :
    res (k ≫ g) m = res k (res g m) :=
  rfl

theorem ring_id_apply {T : Over S} (a : Γ(T.left, ⊤)) : ring (𝟙 T) a = a := by
  simp [ring]

theorem res_id {T : Over S} (m : Mat.SL2 Γ(T.left, ⊤)) : res (𝟙 T) m = m := by
  ext i j
  exact ring_id_apply _

/-! ### Group identities -/

section Group

variable {G : Type*} [Group G]

/-- Central factors do not change a commutator. -/
theorem commutator_mul_central (a b k l : G) (hk : ∀ y, Commute k y) (hl : ∀ y, Commute l y) :
    a * k * (b * l) * (a * k)⁻¹ * (b * l)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h1 : a * k * (b * l) * (a * k)⁻¹ * (b * l)⁻¹ =
      a * (k * (b * (l * (k⁻¹ * (a⁻¹ * (l⁻¹ * b⁻¹)))))) := by group
  have h2 : k * (b * (l * (k⁻¹ * (a⁻¹ * (l⁻¹ * b⁻¹))))) =
      b * (l * (k * k⁻¹ * (a⁻¹ * (l⁻¹ * b⁻¹)))) := by
    rw [← mul_assoc k b, (hk b).eq, mul_assoc b, ← mul_assoc k l, (hk l).eq, mul_assoc l,
      mul_assoc k]
  rw [h1, h2, mul_inv_cancel, one_mul, ← mul_assoc l a⁻¹, (hl a⁻¹).eq, mul_assoc a⁻¹,
    ← mul_assoc l l⁻¹, mul_inv_cancel, one_mul]
  group

/-- The commutator `[a, b c]` when `[a, c]` is central. -/
theorem commutator_mul_right (a b c : G) (hc : ∀ y, Commute (a * c * a⁻¹ * c⁻¹) y) :
    a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * a⁻¹ * b⁻¹ * (a * c * a⁻¹ * c⁻¹) := by
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹
      = a * b * a⁻¹ * ((a * c * a⁻¹ * c⁻¹) * b⁻¹) := by group
    _ = a * b * a⁻¹ * (b⁻¹ * (a * c * a⁻¹ * c⁻¹)) := by rw [(hc b⁻¹).eq]
    _ = a * b * a⁻¹ * b⁻¹ * (a * c * a⁻¹ * c⁻¹) := by group

/-- The commutator `[a c, b]` when `[c, b]` is central. -/
theorem commutator_mul_left (a c b : G) (hc : ∀ y, Commute (c * b * c⁻¹ * b⁻¹) y) :
    a * c * b * (a * c)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ * (c * b * c⁻¹ * b⁻¹) := by
  calc a * c * b * (a * c)⁻¹ * b⁻¹
      = a * (c * b * c⁻¹ * b⁻¹) * b * a⁻¹ * b⁻¹ := by group
    _ = (c * b * c⁻¹ * b⁻¹) * a * b * a⁻¹ * b⁻¹ := by
        rw [← (hc a).eq]
    _ = (c * b * c⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) := by group
    _ = a * b * a⁻¹ * b⁻¹ * (c * b * c⁻¹ * b⁻¹) := (hc _).eq

/-- Conjugating a commutator conjugates both entries. -/
theorem conj_commutator (e a b : G) :
    e * (a * b * a⁻¹ * b⁻¹) * e⁻¹ =
      (e * a * e⁻¹) * (e * b * e⁻¹) * (e * a * e⁻¹)⁻¹ * (e * b * e⁻¹)⁻¹ := by
  group

end Group

/-! ### Central extensions of `SL₂` on points -/

/-- The point-level data of a central extension of `SL₂` over `S`: a group scheme `E`, natural
homomorphisms `Q` from its points to determinant-one matrices over global sections, whose
kernels are central, every matrix lifting fppf-locally, and matrices determined fppf-locally. -/
structure Ext (S : Scheme.{u}) where
  /-- The extension group scheme. -/
  E : GroupScheme S
  /-- The projection on points. -/
  Q : ∀ T : Over S, (T ⟶ E.X) →* Mat.SL2 Γ(T.left, ⊤)
  Q_nat : ∀ {T V : Over S} (g : V ⟶ T) (e : T ⟶ E.X), Q V (g ≫ e) = res g (Q T e)
  central : ∀ {T : Over S} (e e' : T ⟶ E.X), Q T e = 1 → Commute e e'
  lift : ∀ {T : Over S} (m : Mat.SL2 Γ(T.left, ⊤)),
    Loc (fun V (g : V ⟶ T) => ∃ e : V ⟶ E.X, Q V e = res g m)
  sep : ∀ {T : Over S} (m m' : Mat.SL2 Γ(T.left, ⊤)),
    Loc (fun V (g : V ⟶ T) => res g m = res g m') → m = m'

namespace Ext

variable (X : Ext S)

/-- Two lifts of the same matrix differ by a central element. -/
theorem central_of_eq {T : Over S} {e e' : T ⟶ X.E.X} (h : X.Q T e = X.Q T e') :
    ∀ y, Commute (e⁻¹ * e') y :=
  fun y => X.central _ y (by rw [map_mul, map_inv, h, inv_mul_cancel])

/-- The commutator of two lifts only depends on the lifted matrices. -/
theorem commutator_eq {T : Over S} {e₁ e₂ e₁' e₂' : T ⟶ X.E.X} (h₁ : X.Q T e₁ = X.Q T e₁')
    (h₂ : X.Q T e₂ = X.Q T e₂') :
    e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = e₁' * e₂' * e₁'⁻¹ * e₂'⁻¹ := by
  have := commutator_mul_central e₁ e₂ (e₁⁻¹ * e₁') (e₂⁻¹ * e₂') (X.central_of_eq h₁)
    (X.central_of_eq h₂)
  simpa only [mul_inv_cancel_left] using this.symm

/-- A point whose image is central in `SL₂` modulo nothing: the commutator of lifts of commuting
matrices is central. -/
theorem commutator_central {T : Over S} {e₁ e₂ : T ⟶ X.E.X}
    (h : Commute (X.Q T e₁) (X.Q T e₂)) : ∀ y, Commute (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) y :=
  fun y => X.central _ y (by
    simp only [map_mul, map_inv]
    rw [h.eq, mul_inv_cancel_right, mul_inv_cancel])

/-- Restriction of a commutator. -/
theorem comp_commutator {V T : Over S} (g : V ⟶ T) (e₁ e₂ : T ⟶ X.E.X) :
    g ≫ (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) = (g ≫ e₁) * (g ≫ e₂) * (g ≫ e₁)⁻¹ * (g ≫ e₂)⁻¹ := by
  simp only [MonObj.comp_mul, GrpObj.comp_inv]

/-- Restriction of a conjugate. -/
theorem comp_conj {V T : Over S} (g : V ⟶ T) (e a : T ⟶ X.E.X) :
    g ≫ (e * a * e⁻¹) = (g ≫ e) * (g ≫ a) * (g ≫ e)⁻¹ := by
  simp only [MonObj.comp_mul, GrpObj.comp_inv]

theorem exists_comm {T : Over S} (m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)) :
    ∃ c : T ⟶ X.E.X, ∀ ⦃V : Over S⦄ (g : V ⟶ T) (e₁ e₂ : V ⟶ X.E.X),
      X.Q V e₁ = res g m₁ → X.Q V e₂ = res g m₂ → g ≫ c = e₁ * e₂ * e₁⁻¹ * e₂⁻¹ := by
  obtain ⟨c, hc⟩ := Loc.glue (X := X.E.X)
    (fun V g x => ∃ e₁ e₂ : V ⟶ X.E.X, X.Q V e₁ = res g m₁ ∧ X.Q V e₂ = res g m₂ ∧
      x = e₁ * e₂ * e₁⁻¹ * e₂⁻¹)
    (by
      rintro V W g k x ⟨e₁, e₂, h₁, h₂, rfl⟩
      refine ⟨k ≫ e₁, k ≫ e₂, ?_, ?_, X.comp_commutator k e₁ e₂⟩
      · rw [X.Q_nat, h₁, res_comp]
      · rw [X.Q_nat, h₂, res_comp])
    (by
      rintro V g x y ⟨e₁, e₂, h₁, h₂, rfl⟩ ⟨e₁', e₂', h₁', h₂', rfl⟩
      exact X.commutator_eq (h₁.trans h₁'.symm) (h₂.trans h₂'.symm))
    (((X.lift m₁).and (X.lift m₂)).mono fun V g ⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ =>
      ⟨_, e₁, e₂, h₁, h₂, rfl⟩)
  exact ⟨c, fun V g e₁ e₂ h₁ h₂ => hc g _ ⟨e₁, e₂, h₁, h₂, rfl⟩⟩

/-- The commutator of fppf-local lifts of two matrices, glued to a point of `E`. -/
def comm {T : Over S} (m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)) : T ⟶ X.E.X :=
  (X.exists_comm m₁ m₂).choose

theorem comm_spec {T : Over S} (m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)) ⦃V : Over S⦄ (g : V ⟶ T)
    (e₁ e₂ : V ⟶ X.E.X) (h₁ : X.Q V e₁ = res g m₁) (h₂ : X.Q V e₂ = res g m₂) :
    g ≫ X.comm m₁ m₂ = e₁ * e₂ * e₁⁻¹ * e₂⁻¹ :=
  (X.exists_comm m₁ m₂).choose_spec g e₁ e₂ h₁ h₂

theorem comm_eq {T : Over S} {m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)} {e₁ e₂ : T ⟶ X.E.X}
    (h₁ : X.Q T e₁ = m₁) (h₂ : X.Q T e₂ = m₂) : X.comm m₁ m₂ = e₁ * e₂ * e₁⁻¹ * e₂⁻¹ := by
  have := X.comm_spec m₁ m₂ (𝟙 T) e₁ e₂ (by rw [res_id, h₁]) (by rw [res_id, h₂])
  rwa [Category.id_comp] at this

/-- The glued commutator is computed by local lifts over any further restriction. -/
theorem comm_res {V T : Over S} (g : V ⟶ T) (m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)) :
    g ≫ X.comm m₁ m₂ = X.comm (res g m₁) (res g m₂) := by
  apply Loc.ext
  refine ((X.lift (res g m₁)).and (X.lift (res g m₂))).mono ?_
  rintro W k ⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩
  rw [← Category.assoc, X.comm_spec m₁ m₂ (k ≫ g) e₁ e₂ h₁ h₂,
    X.comm_spec (res g m₁) (res g m₂) k e₁ e₂ h₁ h₂]

theorem Q_comm {T : Over S} (m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)) :
    X.Q T (X.comm m₁ m₂) = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by
  apply X.sep
  refine ((X.lift m₁).and (X.lift m₂)).mono ?_
  rintro V g ⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩
  rw [← X.Q_nat, X.comm_spec m₁ m₂ g e₁ e₂ h₁ h₂]
  simp only [map_mul, map_inv, h₁, h₂]

/-- Two points of `E` agreeing fppf-locally are equal. -/
theorem ext_loc {T : Over S} {e e' : T ⟶ X.E.X}
    (h : Loc (fun V (g : V ⟶ T) => g ≫ e = g ≫ e')) : e = e' :=
  Loc.ext h

end Ext

end Langlands.GroupScheme.SL2CentralExtension
