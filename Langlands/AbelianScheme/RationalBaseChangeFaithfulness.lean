import Langlands.AbelianScheme.RationalBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.Flat.Localization

/-! # Faithfulness of actual rational Hom pullback -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

/-- Pullback distinguishes actual rational homomorphisms of abelian schemes. -/
def RationalBaseChangeIsFaithful {S S' : Scheme.{u}} (b : S' ⟶ S) : Prop :=
  ∀ A B : AbelianScheme S, Function.Injective (rationalBaseChangeHom (A := A) (B := B) b)

variable {S S' : Scheme.{u}} (b : S' ⟶ S) [(Over.pullback b).Faithful]
  {A B : AbelianScheme S}

/-- Faithful scheme pullback distinguishes actual integral homomorphisms. -/
theorem baseChange_map_injective_of_faithful_over :
    Function.Injective (fun f : A ⟶ B => (baseChange b).map f) := by
  intro f g h
  have hOver : (groupHom f).hom.hom = (groupHom g).hom.hom :=
    (Over.pullback b).map_injective
      (congrArg (fun x => (groupHom x).hom.hom) h)
  exact congrArg Additive.ofMul (Grp.hom_ext _ _ hOver)

/-- Flatness of rationalization preserves the injectivity of actual Hom pullback. -/
theorem rationalBaseChangeHom_injective_of_faithful_over :
    Function.Injective (rationalBaseChangeHom (A := A) (B := B) b) := by
  let F : (A ⟶ B) →ₗ[ℤ] ((baseChange b).obj A ⟶ (baseChange b).obj B) :=
    (baseChange b).mapLinearMap ℤ
  have hF : Function.Injective F := baseChange_map_injective_of_faithful_over b
  have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hQ : Function.Injective (F.lTensor ℚ) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hF
  have hmap : ∀ f : Hom0 A B, rationalBaseChangeHom b f = F.lTensor ℚ f := by
    intro f
    induction f using TensorProduct.inductionOn with
    | tmul q f =>
        simp only [rationalBaseChangeHom_tmul, LinearMap.lTensor_tmul]
        rfl
    | add f g hf hg => simp only [_root_.map_add, hf, hg]
  intro f g h
  apply hQ
  rw [← hmap f, ← hmap g]
  exact h

include b in
/-- Faithful pullback on schemes implies faithful pullback on actual rational Hom. -/
theorem rationalBaseChangeIsFaithful_of_faithful_over :
    RationalBaseChangeIsFaithful b := by
  intro A B
  exact rationalBaseChangeHom_injective_of_faithful_over b

omit [(Over.pullback b).Faithful] in
/-- Faithfully flat quasi-compact base change distinguishes actual rational Hom. -/
theorem rationalBaseChangeIsFaithful_of_fpqc [Surjective b] [Flat b] [QuasiCompact b] :
    RationalBaseChangeIsFaithful b :=
  rationalBaseChangeIsFaithful_of_faithful_over b

/-- Every extension of fields distinguishes actual rational homomorphisms. -/
theorem rationalBaseChangeIsFaithful_field
    {k K : Type u} [Field k] [Field K]
    (c : Spec (.of K) ⟶ Spec (.of k)) : RationalBaseChangeIsFaithful c := by
  have : Surjective c := ⟨fun x => ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩⟩
  exact rationalBaseChangeIsFaithful_of_fpqc c

/-- A nonzero actual rational endomorphism stays nonzero under extension of fields. -/
theorem rationalBaseChangeHom_ne_zero_field
    {k K : Type u} [Field k] [Field K]
    (c : Spec (.of K) ⟶ Spec (.of k))
    {X Y : AbelianScheme (Spec (.of k))} {f : Hom0 X Y} (hf : f ≠ 0) :
    rationalBaseChangeHom c f ≠ 0 := by
  intro h
  apply hf
  apply rationalBaseChangeIsFaithful_field c X Y
  simpa only [map_zero] using h

end Langlands.AbelianScheme
