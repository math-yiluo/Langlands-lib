import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Steinberg symbols and symbolic Milnor K₂

Milnor's presentation (§11.1) is realized by the tensor product of two copies of the abelian
unit group over `ℤ`, modulo the span of the Steinberg tensors. The resulting group is written
multiplicatively. A Steinberg symbol induces a homomorphism out of this quotient as in §11.3.
-/

open scoped TensorProduct

namespace Langlands.KTheory

universe u v

/-- A bimultiplicative function on field units with values in a commutative group, sending
any pair of units whose values sum to one to the identity. -/
structure SteinbergSymbol (F : Type u) [Field F] (A : Type v) [CommGroup A] where
  toFun : Fˣ → Fˣ → A
  map_mul_left' (a₁ a₂ b : Fˣ) : toFun (a₁ * a₂) b = toFun a₁ b * toFun a₂ b
  map_mul_right' (a b₁ b₂ : Fˣ) : toFun a (b₁ * b₂) = toFun a b₁ * toFun a b₂
  steinberg' (a b : Fˣ) : (a : F) + (b : F) = 1 → toFun a b = 1

variable {F : Type u} [Field F] {A : Type v} [CommGroup A]

namespace SteinbergSymbol

instance : FunLike (SteinbergSymbol F A) Fˣ (Fˣ → A) where
  coe := SteinbergSymbol.toFun
  coe_injective := by
    intro s t h
    cases s
    cases t
    cases h
    rfl

@[ext]
theorem ext {s t : SteinbergSymbol F A} (h : ∀ a b, s a b = t a b) : s = t :=
  DFunLike.ext _ _ fun a => funext (h a)

theorem map_mul_left (s : SteinbergSymbol F A) (a₁ a₂ b : Fˣ) :
    s (a₁ * a₂) b = s a₁ b * s a₂ b :=
  s.map_mul_left' a₁ a₂ b

theorem map_mul_right (s : SteinbergSymbol F A) (a b₁ b₂ : Fˣ) :
    s a (b₁ * b₂) = s a b₁ * s a b₂ :=
  s.map_mul_right' a b₁ b₂

theorem steinberg (s : SteinbergSymbol F A) (a b : Fˣ) (h : (a : F) + (b : F) = 1) :
    s a b = 1 :=
  s.steinberg' a b h

theorem steinberg_mk0 (s : SteinbergSymbol F A) (a : Fˣ) (h : 1 - (a : F) ≠ 0) :
    s a (Units.mk0 (1 - (a : F)) h) = 1 := by
  apply s.steinberg
  change (a : F) + (1 - (a : F)) = 1
  rw [add_comm, sub_add_cancel]

/-- With the group laws written additively, a bimultiplicative map is `ℤ`-bilinear. -/
private def toBilinear (s : SteinbergSymbol F A) :
    Additive Fˣ →ₗ[ℤ] Additive Fˣ →ₗ[ℤ] Additive A := by
  let right (a : Additive Fˣ) : Additive Fˣ →ₗ[ℤ] Additive A :=
    (AddMonoidHom.mk' (fun b => Additive.ofMul (s a.toMul b.toMul))
      (fun b c => congrArg Additive.ofMul (s.map_mul_right a.toMul b.toMul c.toMul))).toIntLinearMap
  exact (AddMonoidHom.mk' right (fun a b => LinearMap.ext fun c =>
    congrArg Additive.ofMul (s.map_mul_left a.toMul b.toMul c.toMul))).toIntLinearMap

end SteinbergSymbol

variable (F) in
/-- The tensor product over `ℤ` of the field unit group, written additively, with itself. -/
abbrev MilnorK2.UnitTensor : Type u := Additive Fˣ ⊗[ℤ] Additive Fˣ

variable (F) in
/-- The integer span of the pure tensors for pairs of units whose values sum to one. -/
def MilnorK2.steinbergRelations : Submodule ℤ (MilnorK2.UnitTensor F) :=
  Submodule.span ℤ
    {x | ∃ a b : Fˣ, (a : F) + (b : F) = 1 ∧ x = Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b}

variable (F) in
/-- The degree-two Milnor group, with multiplication given by addition in the quotient of
the integer tensor product by the Steinberg relations. -/
def MilnorK2 : Type u := Multiplicative (MilnorK2.UnitTensor F ⧸ MilnorK2.steinbergRelations F)

namespace MilnorK2

instance : CommGroup (MilnorK2 F) :=
  inferInstanceAs (CommGroup (Multiplicative (UnitTensor F ⧸ steinbergRelations F)))

variable (F) in
/-- The quotient homomorphism from the unit tensor product, written multiplicatively. -/
def ofTensor : Multiplicative (UnitTensor F) →* MilnorK2 F :=
  (steinbergRelations F).mkQ.toAddMonoidHom.toMultiplicative

theorem ofTensor_surjective : Function.Surjective (ofTensor F) :=
  (steinbergRelations F).mkQ_surjective

@[simp]
theorem ofTensor_eq_one (x : UnitTensor F) :
    ofTensor F (Multiplicative.ofAdd x) = 1 ↔ x ∈ steinbergRelations F :=
  Submodule.Quotient.mk_eq_zero _

variable (F) in
/-- The canonical Steinberg symbol `{a,b}`, the image of the pure tensor `a ⊗ b`. -/
def symbol : SteinbergSymbol F (MilnorK2 F) where
  toFun a b := ofTensor F (Multiplicative.ofAdd (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b))
  map_mul_left' a₁ a₂ b := by
    rw [ofMul_mul, TensorProduct.add_tmul, ofAdd_add, map_mul]
  map_mul_right' a b₁ b₂ := by
    rw [ofMul_mul, TensorProduct.tmul_add, ofAdd_add, map_mul]
  steinberg' a b hab :=
    (ofTensor_eq_one _).2 (Submodule.subset_span ⟨a, b, hab, rfl⟩)

theorem symbol_apply (a b : Fˣ) :
    symbol F a b = ofTensor F (Multiplicative.ofAdd (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b)) :=
  rfl

/-- The homomorphism induced by a Steinberg symbol, by descent from the tensor product. -/
def lift (s : SteinbergSymbol F A) : MilnorK2 F →* A :=
  let f := TensorProduct.lift s.toBilinear
  let descended := (steinbergRelations F).liftQ f (by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, hab, rfl⟩
    exact LinearMap.mem_ker.mpr (congrArg Additive.ofMul (s.steinberg a b hab)))
  descended.toAddMonoidHom.toMultiplicativeLeft

@[simp]
theorem lift_symbol (s : SteinbergSymbol F A) (a b : Fˣ) : lift s (symbol F a b) = s a b :=
  rfl

end MilnorK2

end Langlands.KTheory
