/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd

/-!
# Finite coproducts of finite morphisms

If `fᵢ : Yᵢ ⟶ X` is a finite family of finite morphisms, then `Sigma.desc f : ∐ Yᵢ ⟶ X` is
finite. This extends the binary case `coprod.desc` from Mathlib by induction on the index type.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsFinite

attribute [local instance high] instHasColimitOfHasColimitsOfShape hasColimitsOfShape_discrete

/-- The morphism `∐ᵢ Yᵢ ⟶ X` induced by a finite family of finite morphisms `Yᵢ ⟶ X` is
finite. -/
instance sigmaDesc {ι : Type v} [Finite ι] {X : Scheme.{u}} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsFinite (f i)] : IsFinite (Sigma.desc f) := by
  refine Finite.induction_empty_option (P := fun ι ↦ ∀ [Finite ι] (Y : ι → Scheme.{u})
      (f : ∀ i, Y i ⟶ X), (∀ i, IsFinite (f i)) → IsFinite (Sigma.desc f))
    ?_ ?_ ?_ ι Y f inferInstance
  · intro α β e hα _ Y f hf
    have : Finite α := Finite.of_equiv _ e.symm
    have := hα (fun a ↦ Y (e a)) (fun a ↦ f (e a)) fun a ↦ hf (e a)
    have h : (Sigma.whiskerEquiv e fun a ↦ Iso.refl (Y (e a))).hom ≫ Sigma.desc f =
        Sigma.desc fun a ↦ f (e a) := by
      ext a
      simp
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (Sigma.whiskerEquiv e fun a ↦ Iso.refl (Y (e a))).hom, h]
    infer_instance
  · intro _ Y f _
    have : IsEmpty ↥(∐ Y) := isInitial_iff_isEmpty.mp
      ⟨IsInitial.ofUniqueHom (fun _ ↦ Sigma.desc fun i ↦ i.elim)
        fun _ _ ↦ Sigma.hom_ext _ _ fun i ↦ i.elim⟩
    infer_instance
  · intro α _ hα _ Y f hf
    have := hα (fun i ↦ Y (some i)) (fun i ↦ f (some i)) fun i ↦ hf (some i)
    have := hf none
    have h : Sigma.desc f =
        (sigmaOptionIso Y).hom ≫ coprod.desc (f none) (Sigma.desc fun i ↦ f (some i)) := by
      ext (_ | i) <;> simp
    rw [h]
    infer_instance

end AlgebraicGeometry.IsFinite

namespace AlgebraicGeometry

/-- **A finite morphism to a locally Noetherian scheme is of finite presentation**: it is locally
of finite presentation, quasi-compact and quasi-separated. Over an affine open `Spec A` of the
target the source is `Spec B` with `B` a finite module over the Noetherian ring `A`, hence a
finitely presented `A`-algebra. (blueprint: `pqf-lem-finite-fp-locnoeth`; the definition
`pqf-def-locnoeth` is `AlgebraicGeometry.IsLocallyNoetherian`, and
`pqf-lem-affine-open-locnoeth` is `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian`) -/
theorem IsFinite.locallyOfFinitePresentation_of_isLocallyNoetherian {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y] :
    LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
