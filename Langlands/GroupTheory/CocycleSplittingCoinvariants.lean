import Langlands.GroupTheory.CocycleSplittingExtension
import Mathlib.GroupTheory.Abelianization.Defs

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.NormalizedTwoCocycle.SplittingModule

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

variable {G A : Type u} [Group G] [Fintype G] [CommGroup A]
  [MulDistribMulAction G A] (c : NormalizedTwoCocycle G A)

local instance coinvariantsCoefficientModule : Module Scalars.{u} (Additive A) := ULift.module
local instance coinvariantsTargetModule :
    Module Scalars.{u} (Additive (Abelianization c.Extension)) := ULift.module

/-- The coefficient inclusion followed by abelianization, in additive form. -/
def coefficientAbelianization :
    Additive A →ₗ[Scalars.{u}] Additive (Abelianization c.Extension) where
  toFun a := Additive.ofMul (Abelianization.of (Extension.inl c a.toMul))
  map_add' a b := by
    change Additive.ofMul (Abelianization.of (Extension.inl c (a.toMul * b.toMul))) = _
    simp only [map_mul]
    rfl
  map_smul' r a := by
    change Additive.ofMul (Abelianization.of (Extension.inl c (a.toMul ^ r.down))) =
      Additive.ofMul (Abelianization.of (Extension.inl c a.toMul) ^ r.down)
    simp only [map_zpow]

omit [Fintype G] in
lemma coefficientAbelianization_action (g : G) (a : Additive A) :
    coefficientAbelianization c (coefficientAction g a) =
      coefficientAbelianization c a := by
  change Additive.ofMul (Abelianization.of (Extension.inl c (g • a.toMul))) = _
  have h := Extension.conjugate_inl c (Extension.sectionMap c g) a.toMul
  simp only [Extension.sectionMap_right] at h
  rw [← h]
  simp [coefficientAbelianization]

/-- The distinguished section, projected to the additive abelianization. -/
def sectionAbelianization (g : G) : Additive (Abelianization c.Extension) :=
  Additive.ofMul (Abelianization.of (Extension.sectionMap c g))

omit [Fintype G] in
lemma sectionAbelianization_mul (g h : G) :
    sectionAbelianization c g + sectionAbelianization c h =
      coefficientAbelianization c (Additive.ofMul (c (g, h))) +
        sectionAbelianization c (g * h) := by
  change Additive.ofMul (Abelianization.of
    (Extension.sectionMap c g * Extension.sectionMap c h)) = _
  rw [Extension.sectionMap_mul]
  rfl

/-- Extend the section values linearly to integral coordinate vectors. -/
def sectionLinear :
    (G → Scalars.{u}) →ₗ[Scalars.{u}] Additive (Abelianization c.Extension) where
  toFun f := ∑ x : G, f x • sectionAbelianization c x⁻¹
  map_add' f k := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [smul_smul, Finset.smul_sum]

lemma sectionLinear_apply (f : G → Scalars.{u}) :
    sectionLinear c f = ∑ x : G, f x • sectionAbelianization c x⁻¹ := rfl

lemma sectionLinear_regular (g : G) (f : G → Scalars.{u}) :
    sectionLinear c ((regular G).ρ g f) =
      ∑ x : G, f x • sectionAbelianization c (g * x⁻¹) := by
  rw [sectionLinear_apply]
  calc
    _ = ∑ x : G, f (x * g) • sectionAbelianization c (g * (x * g)⁻¹) := by
      simp only [regular_apply, mul_inv_rev, mul_inv_cancel_left]
    _ = _ := Equiv.sum_comp (Equiv.mulRight g)
      (fun x => f x • sectionAbelianization c (g * x⁻¹))

lemma twist_sectionLinear (g : G) (f : G → Scalars.{u}) :
    coefficientAbelianization c (twist c g f) +
        sectionLinear c ((regular G).ρ g f) =
      coordinateSum G f • sectionAbelianization c g + sectionLinear c f := by
  rw [twist_apply, map_sum, sectionLinear_regular, coordinateSum_apply,
    Finset.sum_smul, sectionLinear_apply]
  simp only [map_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← smul_add, ← smul_add, ← sectionAbelianization_mul]

/-- The coordinate map from the splitting module to the extension abelianization. -/
def abelianizationCoordinates :
    Carrier (G := G) (A := A) →ₗ[Scalars.{u}] Additive (Abelianization c.Extension) :=
  (coefficientAbelianization c).comp (LinearMap.fst _ _ _) +
    (sectionLinear c).comp ((coordinateSum G).ker.subtype.comp (LinearMap.snd _ _ _))

lemma abelianizationCoordinates_apply (x : Carrier (G := G) (A := A)) :
    abelianizationCoordinates c x =
      coefficientAbelianization c x.1 + sectionLinear c x.2.val := rfl

lemma abelianizationCoordinates_invariant (g : G) (x : Carrier (G := G) (A := A)) :
    abelianizationCoordinates c ((splitting c).ρ g x) =
      abelianizationCoordinates c x := by
  change coefficientAbelianization c (coefficientAction g x.1 + twist c g x.2.val) +
      sectionLinear c ((regular G).ρ g x.2.val) =
    coefficientAbelianization c x.1 + sectionLinear c x.2.val
  rw [map_add, coefficientAbelianization_action, add_assoc, twist_sectionLinear]
  have hx : coordinateSum G x.2.val = 0 := x.2.property
  rw [hx, zero_smul, zero_add]

/-- The induced linear map from splitting-module coinvariants to the abelianization. -/
def coinvariantsToAbelianization :
    (splitting c).ρ.Coinvariants →ₗ[Scalars.{u}] Additive (Abelianization c.Extension) :=
  Representation.Coinvariants.lift _ (abelianizationCoordinates c) fun g =>
    LinearMap.ext fun x => abelianizationCoordinates_invariant c g x

end Langlands.NormalizedTwoCocycle.SplittingModule
