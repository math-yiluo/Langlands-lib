import Langlands.GroupScheme.AutomorphicAction

/-! # Automorphic actions on the image of restriction of points -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H G : GroupScheme S}
  (a : AutomorphicAction H G) {U T : Over S} (res : T ⟶ U)

/-- A point of the acting group preserves the image of the points restricted along `res`. -/
def PreservesRestrictionImage (x : T ⟶ H.X) : Prop :=
  ∀ g : T ⟶ G.X,
    (∃ y : U ⟶ G.X, g = a.act x (res ≫ y)) ↔
      ∃ y : U ⟶ G.X, g = res ≫ y

/-- A restricted acting point preserves the restriction image. -/
theorem preservesRestrictionImage_restrict (x : U ⟶ H.X) :
    a.PreservesRestrictionImage res (res ≫ x) := by
  intro g
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨a.act x y, (a.naturality res x y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨a.act x⁻¹ y, ?_⟩
    rw [← a.naturality, a.act_act_inv]

/-- Preserving the restriction image is closed under multiplication of acting points. -/
theorem PreservesRestrictionImage.mul {x z : T ⟶ H.X}
    (hx : a.PreservesRestrictionImage res x)
    (hz : a.PreservesRestrictionImage res z) :
    a.PreservesRestrictionImage res (x * z) := by
  intro g
  constructor
  · rintro ⟨y, rfl⟩
    rw [a.act_mul_left]
    obtain ⟨y', hy'⟩ := (hz (a.act z (res ≫ y))).1 ⟨y, rfl⟩
    exact (hx _).1 ⟨y', congrArg (a.act x) hy'⟩
  · intro hg
    obtain ⟨y, hy⟩ := (hx g).2 hg
    obtain ⟨z', hz'⟩ := (hz (res ≫ y)).2 ⟨y, rfl⟩
    refine ⟨z', ?_⟩
    rw [a.act_mul_left, ← hz', ← hy]

/-- Preserving the restriction image is closed under inversion of acting points. -/
theorem PreservesRestrictionImage.inv {x : T ⟶ H.X}
    (hx : a.PreservesRestrictionImage res x) :
    a.PreservesRestrictionImage res x⁻¹ := by
  intro g
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := (hx (res ≫ y)).2 ⟨y, rfl⟩
    exact ⟨z, (congrArg (a.act x⁻¹) hz).trans (a.act_inv_act x (res ≫ z))⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ := (hx (a.act x g)).1 ⟨z, congrArg (a.act x) hz⟩
    exact ⟨y, by rw [← hy, a.act_inv_act]⟩

variable (p : G ⟶ H)
  (hlift : ∀ (h g : T ⟶ G.X), a.act (h ≫ p.hom.hom) g = h * g * h⁻¹)

include hlift in
/-- Conjugacy of a translated restriction image is equivalent to preservation after
removing one lifted acting point. -/
theorem conjugacy_iff_exists_preservesRestrictionImage (x : T ⟶ H.X) :
    (∃ h : T ⟶ G.X, ∀ g : T ⟶ G.X,
      (∃ y : U ⟶ G.X, g = a.act x (res ≫ y)) ↔
        ∃ y : U ⟶ G.X, g = h * (res ≫ y) * h⁻¹) ↔
      ∃ h : T ⟶ G.X,
        a.PreservesRestrictionImage res ((h ≫ p.hom.hom)⁻¹ * x) := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, fun g => ?_⟩
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := (hh (a.act x (res ≫ y))).1 ⟨y, rfl⟩
      refine ⟨z, ?_⟩
      rw [a.act_mul_left, hz, ← hlift, a.act_inv_act]
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := (hh (h * (res ≫ y) * h⁻¹)).2 ⟨y, rfl⟩
      refine ⟨z, ?_⟩
      rw [a.act_mul_left, ← hz, ← hlift, a.act_inv_act]
  · rintro ⟨h, hh⟩
    refine ⟨h, fun g => ?_⟩
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := (hh (a.act ((h ≫ p.hom.hom)⁻¹ * x) (res ≫ y))).1 ⟨y, rfl⟩
      refine ⟨z, ?_⟩
      have he := congrArg (a.act (h ≫ p.hom.hom)) hz
      rw [a.act_mul_left, a.act_act_inv, hlift] at he
      exact he
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := (hh (res ≫ y)).2 ⟨y, rfl⟩
      refine ⟨z, ?_⟩
      have he := congrArg (a.act (h ≫ p.hom.hom)) hz
      rw [a.act_mul_left, a.act_act_inv, hlift] at he
      exact he

include hlift in
/-- The formal conjugacy criterion follows whenever the only acting points that preserve
the restriction image are themselves restricted points. -/
theorem conjugacy_iff_factorization_of_preservesRestrictionImage
    (hnormal : ∀ z : T ⟶ H.X, a.PreservesRestrictionImage res z →
      ∃ y : U ⟶ H.X, z = res ≫ y)
    (x : T ⟶ H.X) :
    (∃ h : T ⟶ G.X, ∀ g : T ⟶ G.X,
      (∃ y : U ⟶ G.X, g = a.act x (res ≫ y)) ↔
        ∃ y : U ⟶ G.X, g = h * (res ≫ y) * h⁻¹) ↔
      ∃ (h : T ⟶ G.X) (y : U ⟶ H.X),
        x = (h ≫ p.hom.hom) * (res ≫ y) := by
  rw [a.conjugacy_iff_exists_preservesRestrictionImage res p hlift]
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨y, hy⟩ := hnormal _ hh
    exact ⟨h, y, (inv_mul_eq_iff_eq_mul).1 hy⟩
  · rintro ⟨h, y, rfl⟩
    exact ⟨h, by
      rw [inv_mul_cancel_left]
      exact a.preservesRestrictionImage_restrict res y⟩

end Langlands.GroupScheme.AutomorphicAction
