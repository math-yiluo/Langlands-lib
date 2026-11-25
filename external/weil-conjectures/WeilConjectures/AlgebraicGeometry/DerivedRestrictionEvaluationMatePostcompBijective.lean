/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.DerivedOpenTensorTestObjects

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048

-- The two scheme tensor structures need extra elaboration when composing Hom equivalences.
/-- The explicit restricted evaluation mate induces bijections on all Hom sets.
Source: Stacks Project, Tags 08DJ, 08DL and 08BS.
(blueprint: lem-sc-derived-restriction-evaluation-mate-postcomp-bijective).

Proof: use extension by zero as the left adjoint to restriction. The unit is an
isomorphism, and tensoring an object in the essential image of extension by zero
with an arbitrary complex remains in that image by the stalkwise K-flat tensor
calculation. Transpose a map along the adjunction and the canonical tensor-Hom
equivalences. Naturality of the supplied tensor comparison identifies the resulting
map with postcomposition by the displayed mate. Every operation in this composite
is a bijection, proving the assertion.
-/
theorem derivedRestriction_evaluationMate_postcomp_bijective
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))] :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    ∀ (t : ∀ K L : schemeDerivedCategory X, R.obj (K ⊗ L) ≅ R.obj K ⊗ R.obj L),
      (∀ K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
        R.map (a ⊗ₘ b) ≫ (t K' L').hom =
          (t K L).hom ≫ (R.map a ⊗ₘ R.map b)) →
      ∀ L E, ∀ A : schemeDerivedCategory U.toScheme,
        Function.Bijective (fun f : A ⟶ R.obj (H.obj (op L, E)) ↦
          f ≫ (schemeDerivedTensorHomEquiv U.toScheme
            (R.obj (H.obj (op L, E))) (R.obj L) (R.obj E)).symm
            ((t (H.obj (op L, E)) L).inv ≫
              R.map (schemeDerivedTensorHomEquiv X
                (H.obj (op L, E)) L E (𝟙 _)))) := by
  classical
  -- Keep the functor abbreviations shared throughout the Hom-equivalence calculation.
  intro R H t ht L E A
  let V := H.obj (op L, E)
  let eX := schemeDerivedTensorHomEquiv X
  let eU := schemeDerivedTensorHomEquiv U.toScheme
  let ev := eX V L E (𝟙 V)
  let m := (eU (R.obj V) (R.obj L) (R.obj E)).symm
    ((t V L).inv ≫ R.map ev)
  change Function.Bijective (fun f : A ⟶ R.obj V ↦ f ≫ m)
  obtain ⟨B, ⟨i⟩, hB, hBL⟩ := exists_derivedOpen_tensorTestObject X U A
  let e₀ : (B ⟶ V) ≃ (A ⟶ R.obj V) :=
    (Equiv.ofBijective (fun f ↦ R.map f) (hB V)).trans
      (Iso.homFromEquiv i).symm
  let s : A ⊗ R.obj L ≅ R.obj (B ⊗ L) :=
    tensorIso i (Iso.refl _) ≪≫ (t B L).symm
  let e₁ : (B ⟶ V) ≃ (A ⟶
      (derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
        U.toScheme.toRingedSpace.sheaf).obj (op (R.obj L), R.obj E)) :=
    (eX B L E).trans
      ((Equiv.ofBijective (fun f ↦ R.map f) (hBL L E)).trans
        ((Iso.homFromEquiv s).symm.trans (eU A (R.obj L) (R.obj E)).symm))
  have hnX := (Classical.choose_spec (exists_canonicalDerivedTensorHom X)).1
  have hnU := (Classical.choose_spec
    (exists_canonicalDerivedTensorHom U.toScheme)).1
  have hx (f : B ⟶ V) : eX B L E f = (f ⊗ₘ 𝟙 L) ≫ ev := by
    have hn := hnX V B L L E E f (𝟙 L) (𝟙 E) (𝟙 V)
    have hi : H.map ((𝟙 L).op, 𝟙 E) = 𝟙 V := H.map_id (op L, E)
    change eX B L E (f ≫ 𝟙 V ≫ H.map ((𝟙 L).op, 𝟙 E)) =
      (f ⊗ₘ 𝟙 L) ≫ ev ≫ 𝟙 E at hn
    simpa only [hi, Category.comp_id] using hn
  have hu (f : A ⟶ R.obj V) :
      eU A (R.obj L) (R.obj E) (f ≫ m) =
        (f ⊗ₘ 𝟙 (R.obj L)) ≫ (t V L).inv ≫ R.map ev := by
    have hn := hnU (R.obj V) A (R.obj L) (R.obj L) (R.obj E) (R.obj E)
      f (𝟙 _) (𝟙 _) m
    let HU := derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
      U.toScheme.toRingedSpace.sheaf
    have hi : HU.map ((𝟙 (R.obj L)).op, 𝟙 (R.obj E)) =
        𝟙 (HU.obj (op (R.obj L), R.obj E)) := HU.map_id _
    change eU A (R.obj L) (R.obj E)
      (f ≫ m ≫ HU.map ((𝟙 (R.obj L)).op, 𝟙 (R.obj E))) =
        (f ⊗ₘ 𝟙 (R.obj L)) ≫ eU (R.obj V) (R.obj L) (R.obj E) m ≫ 𝟙 _ at hn
    -- Simplify the argument directly, without rewriting inside the chosen equivalence.
    have hm : m ≫ HU.map ((𝟙 (R.obj L)).op, 𝟙 (R.obj E)) = m :=
      (congrArg (fun k ↦ m ≫ k) hi).trans (Category.comp_id m)
    have hn' := (congrArg (fun k ↦ eU A (R.obj L) (R.obj E) (f ≫ k)) hm).symm.trans hn
    simpa only [m, Equiv.apply_symm_apply, Category.comp_id, Category.assoc] using hn'
  have hc (f : B ⟶ V) :
      (R.map f ⊗ₘ 𝟙 (R.obj L)) ≫ (t V L).inv =
        (t B L).inv ≫ R.map (f ⊗ₘ 𝟙 L) := by
    apply (cancel_epi (t B L).hom).1
    simpa [Category.assoc] using
      congrArg (fun q ↦ q ≫ (t V L).inv) (ht B V L L f (𝟙 L)).symm
  have he (f : B ⟶ V) : e₀ f ≫ m = e₁ f := by
    apply (eU A (R.obj L) (R.obj E)).injective
    rw [hu]
    change (((i.hom ≫ R.map f) ⊗ₘ 𝟙 (R.obj L)) ≫
      (t V L).inv ≫ R.map ev) =
      eU A (R.obj L) (R.obj E)
        ((eU A (R.obj L) (R.obj E)).symm (s.hom ≫ R.map (eX B L E f)))
    rw [Equiv.apply_symm_apply]
    simp only [hx, R.map_comp]
    dsimp only [s, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom]
    change ((i.hom ≫ R.map f) ⊗ₘ 𝟙 (R.obj L)) ≫ (t V L).inv ≫ R.map ev =
      ((i.hom ⊗ₘ 𝟙 (R.obj L)) ≫ (t B L).inv) ≫
        R.map (f ⊗ₘ 𝟙 L) ≫ R.map ev
    simpa only [tensorHom_id, comp_whiskerRight, Category.assoc] using
      congrArg (fun q ↦ (i.hom ⊗ₘ 𝟙 (R.obj L)) ≫ q ≫ R.map ev) (hc f)
  apply (Function.Bijective.of_comp_iff (fun f : A ⟶ R.obj V ↦ f ≫ m)
    e₀.bijective).mp
  have heq : (fun f : A ⟶ R.obj V ↦ f ≫ m) ∘ e₀ = e₁ := funext he
  rw [heq]
  exact e₁.bijective

end AlgebraicGeometry.Scheme
