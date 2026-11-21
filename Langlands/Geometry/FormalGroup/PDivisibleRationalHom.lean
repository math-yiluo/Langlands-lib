import Langlands.Geometry.FormalGroup.PDivisiblePadicScalars
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Localization.BaseChange

/-! # Actual rational homomorphisms of p-divisible groups -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

universe u

open CategoryTheory TensorProduct
open scoped nonZeroDivisors

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]
variable {G H J K : PDivisibleGroup R p}

/-- Rational morphisms are obtained by extending actual tower Hom from ℤₚ to ℚₚ. -/
abbrev RationalHom (G H : PDivisibleGroup R p) := ℚ_[p] ⊗[ℤ_[p]] (G ⟶ H)

namespace RationalHom

/-- The canonical rational image of an integral tower morphism. -/
def ofHom : (G ⟶ H) →ₗ[ℤ_[p]] RationalHom G H :=
  TensorProduct.mk ℤ_[p] ℚ_[p] (G ⟶ H) 1

@[simp] theorem ofHom_apply (f : G ⟶ H) : ofHom f = 1 ⊗ₜ[ℤ_[p]] f := rfl

/-- Composition by tensor bilinearity. -/
def compLinear (G H J : PDivisibleGroup R p) :
    RationalHom G H →ₗ[ℤ_[p]] RationalHom H J →ₗ[ℤ_[p]] RationalHom G J :=
  TensorProduct.map₂ (LinearMap.mul ℤ_[p] ℚ_[p])
    (CategoryTheory.Linear.comp (S := ℤ_[p]) G H J)

/-- Composition in the order of the original tower arrows. -/
def comp (f : RationalHom G H) (g : RationalHom H J) : RationalHom G J := compLinear G H J f g

@[simp] theorem comp_tmul (a b : ℚ_[p]) (f : G ⟶ H) (g : H ⟶ J) :
    comp (a ⊗ₜ[ℤ_[p]] f) (b ⊗ₜ[ℤ_[p]] g) = (a * b) ⊗ₜ[ℤ_[p]] (f ≫ g) := rfl

@[simp] theorem add_comp (f f' : RationalHom G H) (g : RationalHom H J) :
    comp (f + f') g = comp f g + comp f' g := (compLinear G H J).map_add₂ f f' g

@[simp] theorem comp_add (f : RationalHom G H) (g g' : RationalHom H J) :
    comp f (g + g') = comp f g + comp f g' := (compLinear G H J f).map_add g g'

@[simp] theorem zero_comp (g : RationalHom H J) :
    comp (0 : RationalHom G H) g = 0 := (compLinear G H J).map_zero₂ g

@[simp] theorem comp_zero (f : RationalHom G H) :
    comp f (0 : RationalHom H J) = 0 := (compLinear G H J f).map_zero

/-- The rational identity is the image of the integral identity. -/
def id (G : PDivisibleGroup R p) : RationalHom G G := ofHom (𝟙 G)

@[simp] theorem id_comp (f : RationalHom G H) : comp (id G) f = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [id]
  | add f g hf hg => simp [hf, hg]

@[simp] theorem comp_id (f : RationalHom G H) : comp f (id H) = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [id]
  | add f g hf hg => simp [hf, hg]

theorem comp_assoc (f : RationalHom G H) (g : RationalHom H J) (h : RationalHom J K) :
    comp (comp f g) h = comp f (comp g h) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [hf, hf']
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [hg, hg']
    | tmul b g =>
      induction h using TensorProduct.inductionOn with
      | add h h' hh hh' => simp only [comp_add, hh, hh']
      | tmul c h => simp [mul_assoc, Category.assoc]

@[simp] theorem smul_comp (a : ℚ_[p]) (f : RationalHom G H) (g : RationalHom H J) :
    comp (a • f) g = a • comp f g := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [smul_add, hf, hf']
  | tmul b f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [smul_add, hg, hg']
    | tmul c g => simp only [smul_tmul', smul_eq_mul, comp_tmul, mul_assoc]

@[simp] theorem comp_smul (a : ℚ_[p]) (f : RationalHom G H) (g : RationalHom H J) :
    comp f (a • g) = a • comp f g := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [smul_add, hf, hf']
  | tmul b f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [smul_add, hg, hg']
    | tmul c g => simp only [smul_tmul', smul_eq_mul, comp_tmul, mul_left_comm]

@[simp] theorem ofHom_id (G : PDivisibleGroup R p) : ofHom (𝟙 G) = id G := rfl

@[simp] theorem ofHom_comp (f : G ⟶ H) (g : H ⟶ J) :
    ofHom (f ≫ g) = comp (ofHom f) (ofHom g) := by
  simp only [ofHom_apply, comp_tmul, one_mul]

/-- Every rational tower morphism has an integral numerator with p-power denominator. -/
theorem exists_pPower_ofHom (z : RationalHom G H) :
    ∃ (n : ℕ) (f : G ⟶ H), (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ n • z = ofHom f := by
  let i := ofHom (G := G) (H := H)
  let : IsLocalizedModule (ℤ_[p])⁰ i := IsLocalization.tensorProduct_isLocalizedModule (ℤ_[p])⁰ ℚ_[p]
  obtain ⟨⟨f, a⟩, ha⟩ := IsLocalizedModule.surj (ℤ_[p])⁰ i z
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero a.property) (PadicInt.irreducible_p (p := p))
  change (a : ℤ_[p]) • z = i f at ha
  rw [he, mul_smul] at ha
  refine ⟨n, (↑e⁻¹ : ℤ_[p]) • f, ?_⟩
  rw [← map_pow, IsScalarTower.algebraMap_smul ℚ_[p]]
  have h := congrArg (fun y : RationalHom G H => (↑e⁻¹ : ℤ_[p]) • y) ha
  simpa only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, ← i.map_smul] using h

end RationalHom

/-- The category with the same p-divisible groups and rational morphisms. -/
structure RationalCategory (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime] where
  of ::
  val : PDivisibleGroup R p

namespace RationalCategory

instance : Category (RationalCategory R p) where
  Hom X Y := RationalHom X.val Y.val
  id X := RationalHom.id X.val
  comp f g := RationalHom.comp f g
  id_comp := RationalHom.id_comp
  comp_id := RationalHom.comp_id
  assoc := RationalHom.comp_assoc

instance : Preadditive (RationalCategory R p) where
  homGroup X Y := inferInstanceAs (AddCommGroup (RationalHom X.val Y.val))
  add_comp _ _ _ := RationalHom.add_comp
  comp_add _ _ _ := RationalHom.comp_add

instance : CategoryTheory.Linear ℚ_[p] (RationalCategory R p) where
  homModule X Y := inferInstanceAs (Module ℚ_[p] (RationalHom X.val Y.val))
  smul_comp _ _ _ := RationalHom.smul_comp
  comp_smul _ _ _ f a g := RationalHom.comp_smul a f g

/-- The canonical functor from integral towers to the category up to isogeny. -/
def inclusion : PDivisibleGroup R p ⥤ RationalCategory R p where
  obj := of
  map := RationalHom.ofHom
  map_id _ := rfl
  map_comp f g := RationalHom.ofHom_comp f g

instance : (inclusion (R := R) (p := p)).Additive where
  map_add {_ _ f g} := map_add RationalHom.ofHom f g

end RationalCategory

/-- A quasi-isogeny is an isomorphism of the actual towers after rationalizing Hom. -/
abbrev QuasiIsogeny (G H : PDivisibleGroup R p) := RationalCategory.of G ≅ RationalCategory.of H

end Langlands.PDivisibleGroup
