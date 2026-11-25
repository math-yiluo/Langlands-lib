/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Internal Hom and a dualizable coefficient

Source: the finite-free coefficient argument in
`lem-coef-integral-hom-reduction.proof.md`, paragraph 1.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C]

private def coefficientAssociator (X D : C) :
    tensorLeft X ⋙ tensorRight D ≅ tensorRight D ⋙ tensorLeft X :=
  NatIso.ofComponents (fun T ↦ α_ X T D) (by
    intro T T' f
    exact associator_naturality_middle X f D)

/-- The same coefficient exchange for any specified right adjoint of left tensor.
Source: blueprint integral-Hom reduction, paragraph 1.
Proof: conjugate the associator between the two composites of left adjoints.
The counit characterization of conjugation identifies its component with the
specified transpose. Thus no choice of closed adjunction affects invertibility.
(blueprint: lem-sf-dualizable-coefficient-hom-action). -/
private theorem isIso_coefficientTranspose {H : C ⥤ C} (X : C)
    (ad : tensorLeft X ⊣ H) (Z D N : C) [ExactPairing D N] :
    IsIso (ad.homEquiv (H.obj Z ⊗ N) (Z ⊗ N)
      ((α_ X (H.obj Z) N).inv ≫ ad.counit.app Z ▷ N)) := by
  let a := (tensorRightAdjunction D N).comp ad
  let b := ad.comp (tensorRightAdjunction D N)
  let e := coefficientAssociator X D
  let c := conjugateEquiv a b e.hom
  let theta := ad.homEquiv (H.obj Z ⊗ N) (Z ⊗ N)
    ((α_ X (H.obj Z) N).inv ≫ ad.counit.app Z ▷ N)
  have hc : IsIso (c.app Z) := by
    dsimp only [c]
    infer_instance
  have ht : X ◁ theta ≫ ad.counit.app (Z ⊗ N) =
      (α_ X (H.obj Z) N).inv ≫ ad.counit.app Z ▷ N := by
    exact (ad.homEquiv_counit _ _ theta).symm.trans
      ((ad.homEquiv _ _).symm_apply_apply _)
  have he : c.app Z = theta := by
    apply (b.homEquiv _ Z).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      conjugateEquiv_counit]
    dsimp only [a, b, e, coefficientAssociator]
    simp only [Adjunction.comp_counit_app, tensorRightAdjunction_counit_app,
      NatIso.ofComponents_hom_app, Functor.comp_map]
    dsimp only [tensorLeft, tensorRight, curriedTensor, Functor.flip, Functor.comp_obj]
    rw [← comp_whiskerRight_assoc, ht, comp_whiskerRight_assoc]
    erw [associator_naturality_left_assoc (ad.counit.app Z) N D,
      ← whisker_exchange_assoc, rightUnitor_naturality]
    monoidal
  change IsIso theta
  rw [← he]
  exact hc

/-- A normalized coefficient model transports invertibility to any tensor presentation.
Source: blueprint integral-Hom reduction, paragraphs 1--2.
Proof: transport the specified adjunction along e. The coefficient normalization
and naturality of r identify its evaluation transpose with coefficient exchange,
conjugated by r. The preceding duality argument makes exchange invertible.
(blueprint: lem-sf-dualizable-coefficient-hom-action). -/
private theorem isIso_transpose_of_coefficient_model
    {A H B : C ⥤ C} (X : C) (ad : A ⊣ H) (e : A ≅ tensorLeft X)
    (Z D N : C) [ExactPairing D N] (r : B ≅ tensorRight N)
    (p : ∀ V : C, A.obj (B.obj V) ⟶ B.obj (A.obj V))
    (hp : ∀ V : C,
      e.hom.app (B.obj V) ≫ X ◁ r.hom.app V ≫ (α_ X V N).inv =
        p V ≫ r.hom.app (A.obj V) ≫ e.hom.app V ▷ N) :
    IsIso (ad.homEquiv (B.obj (H.obj Z)) (B.obj Z)
      (p (H.obj Z) ≫ B.map (ad.counit.app Z))) := by
  let a := ad.ofNatIsoLeft e
  let q := a.homEquiv (H.obj Z ⊗ N) (Z ⊗ N)
    ((α_ X (H.obj Z) N).inv ≫ a.counit.app Z ▷ N)
  have hq : IsIso q := isIso_coefficientTranspose X a Z D N
  let theta := ad.homEquiv (B.obj (H.obj Z)) (B.obj Z)
    (p (H.obj Z) ≫ B.map (ad.counit.app Z))
  have he : theta ≫ H.map (r.hom.app Z) = r.hom.app (H.obj Z) ≫ q := by
    change ad.homEquiv _ _ _ ≫ H.map (r.hom.app Z) =
      r.hom.app (H.obj Z) ≫ a.homEquiv _ _ _
    rw [← ad.homEquiv_naturality_right, ← a.homEquiv_naturality_left]
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
    congr 1
    dsimp only [a, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerRight_app]
    dsimp only [tensorLeft, curriedTensor, Adjunction.ofNatIsoLeft]
    simp only [Category.assoc]
    rw [← Category.assoc (X ◁ r.hom.app (H.obj Z)),
      ← Category.assoc (e.hom.app (B.obj (H.obj Z))), hp]
    simp only [Category.assoc, ← comp_whiskerRight]
    rw [r.hom.naturality]
    dsimp only [tensorRight, curriedTensor, Functor.flip, NatTrans.comp_app,
      Functor.whiskerLeft_app]
    simp only [Iso.hom_inv_id_app_assoc]
  have hc : IsIso (theta ≫ H.map (r.hom.app Z)) := by
    rw [he]
    infer_instance
  change IsIso theta
  exact (isIso_comp_right_iff theta (H.map (r.hom.app Z))).1 hc

section Strength

variable (B : C ⥤ C)
  (p : ∀ X Y : C, X ⊗ B.obj Y ⟶ B.obj (X ⊗ Y))
  (hn : ∀ (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y'),
    (f ⊗ₘ B.map g) ≫ p X' Y' = p X Y ≫ B.map (f ⊗ₘ g))
  (ha : ∀ X Y Z : C,
    X ◁ p Y Z ≫ p X (Y ⊗ Z) ≫ B.map (α_ X Y Z).inv =
      (α_ X Y (B.obj Z)).inv ≫ p (X ⊗ Y) Z)
  [∀ X Y, IsIso (p X Y)]

private noncomputable def strengthCoefficientIso : tensorRight (B.obj (𝟙_ C)) ≅ B :=
  NatIso.ofComponents
    (fun X ↦ asIso (p X (𝟙_ C)) ≪≫ B.mapIso (ρ_ X)) (by
      intro X Y f
      dsimp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
      have h := hn X Y (𝟙_ C) (𝟙_ C) f (𝟙 _)
      rw [B.map_id, tensorHom_id, tensorHom_id] at h
      change (f ▷ B.obj (𝟙_ C)) ≫ (p Y (𝟙_ C) ≫ B.map (ρ_ Y).hom) =
        (p X (𝟙_ C) ≫ B.map (ρ_ X).hom) ≫ B.map f
      rw [← Category.assoc, h, Category.assoc, ← B.map_comp,
        rightUnitor_naturality, B.map_comp, Category.assoc])

include ha in
private theorem strengthCoefficientIso_associativity (X V : C) :
    X ◁ (strengthCoefficientIso B p hn).hom.app V ≫ p X V =
      (α_ X V (B.obj (𝟙_ C))).inv ≫
        (strengthCoefficientIso B p hn).hom.app (X ⊗ V) := by
  dsimp only [strengthCoefficientIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [whiskerLeft_comp, Category.assoc]
  have h := hn X X (V ⊗ 𝟙_ C) V (𝟙 X) (ρ_ V).hom
  rw [id_tensorHom, id_tensorHom] at h
  rw [h, ← Category.assoc, ← Category.assoc]
  have h' := congrArg (fun f ↦ f ≫ B.map (ρ_ (X ⊗ V)).hom) (ha X V (𝟙_ C))
  simp only [Category.assoc, ← B.map_comp] at h' ⊢
  rw [← h']
  have hu : X ◁ (ρ_ V).hom =
      (α_ X V (𝟙_ C)).inv ≫ (ρ_ (X ⊗ V)).hom := by monoidal
  rw [hu]

include hn ha in
/-- An invertible associative tensor strength is tensor by its value on the unit.
Source: the coefficient argument of blueprint integral-Hom reduction, paragraph 1.
Proof: evaluate the strength at the unit, then apply the right unitor. Naturality
makes these maps a natural isomorphism. Associativity at (X,V,unit), followed by
the right-unit coherence, identifies the strength with tensor reassociation.
Conjugate the coefficient transpose by this isomorphism and use duality.
(blueprint: lem-sf-dualizable-coefficient-hom-action). -/
theorem isIso_transpose_of_strength
    {H : C ⥤ C} (X : C) (ad : tensorLeft X ⊣ H) (Z D : C)
    [ExactPairing D (B.obj (𝟙_ C))] :
    IsIso (ad.homEquiv (B.obj (H.obj Z)) (B.obj Z)
      (p X (H.obj Z) ≫ B.map (ad.counit.app Z))) := by
  let s := strengthCoefficientIso B p hn
  apply isIso_transpose_of_coefficient_model X ad (Iso.refl _) Z D
    (B.obj (𝟙_ C)) s.symm (p X)
  intro V
  dsimp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp, tensorLeft, curriedTensor,
    Iso.symm_hom, whiskerRight_id, Category.comp_id]
  have hs := strengthCoefficientIso_associativity B p hn ha X V
  apply (cancel_epi (X ◁ s.hom.app V)).1
  simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id_app, whiskerLeft_id,
    Category.id_comp]
  change (α_ X V (B.obj (𝟙_ C))).inv =
    X ◁ s.hom.app V ≫ p X V ≫ s.inv.app (X ⊗ V) ≫
      (𝟙 (X ⊗ V)) ▷ B.obj (𝟙_ C)
  rw [← Category.assoc, ← Category.assoc, hs]
  dsimp only [s]
  simp only [Category.assoc, Iso.hom_inv_id_app, id_whiskerRight]
  change _ = _ ≫ 𝟙 _ ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id]

end Strength

end CategoryTheory.MonoidalClosed
