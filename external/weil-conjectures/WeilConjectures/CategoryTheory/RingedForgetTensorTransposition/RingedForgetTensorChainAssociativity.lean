/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Associativity of a summand-normalized complex tensor comparison

Source: Stacks Project, Tag 06YN
(blueprint: lem-sf-ringed-forget-chain-associativity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.RingedForgetTensorTransposition

private theorem tensor_map₂_eq
    {B : Type b} [Category.{vb} B] [Preadditive B] [HasZeroObject B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    {P P' Q Q' : CochainComplex B ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex)).map
        (X := (P, Q)) (Y := (P', Q')) (f, g) = f ⊗ₘ g := by
  change ((f ⊗ₘ 𝟙 Q) ≫ (𝟙 P' ⊗ₘ g)) = f ⊗ₘ g
  rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

/-- A summand-normalized tensor comparison lifts inverse associativity to cochain complexes.
Source: Stacks Project, Tag 06YN; the proof of
`Functor.mapCochainComplexμIso_associativity` in the adopted source library.
(blueprint: lem-sf-ringed-forget-chain-associativity)

Proof: invert the summand equation by cancelling the comparison component. Restrict
both sides to each triple coproduct summand. Apply this equation twice, naturality
of the inverse underived comparison, and its associativity equation. The native
complex associator has exactly the same summand equation. Coproduct extensionality
and degreewise extensionality finish the proof; preservation of coproducts by the
functor is not required. -/
private theorem chain_inverse_associativity
    {B : Type b} [Category.{vb} B] [Preadditive B] [HasZeroObject B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    {A : Type a} [Category.{va} A] [Preadditive A] [HasZeroObject A]
    [MonoidalCategory A] [MonoidalPreadditive A]
    [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (F : B ⥤ A) [F.Additive]
    (ν : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    (δ : MonoidalCategory.tensor (CochainComplex B ℤ) ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ))) ⋙
        MonoidalCategory.tensor (CochainComplex A ℤ))
    (hδ : ∀ (P Q : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (δ.hom.app (P, Q)).f n =
        ν.hom.app (P.X p, Q.X q) ≫
          HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)
    (hν : ∀ X Y Z : B,
      (ν.inv.app (X, Y) ▷ F.obj Z) ≫ ν.inv.app (X ⊗ Y, Z) ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
          (F.obj X ◁ ν.inv.app (Y, Z)) ≫ ν.inv.app (X, Y ⊗ Z))
    (P Q N : CochainComplex B ℤ) :
    (δ.inv.app (P, Q) ▷ (F.mapHomologicalComplex (.up ℤ)).obj N) ≫
        δ.inv.app (P ⊗ Q, N) ≫ (F.mapHomologicalComplex (.up ℤ)).map (α_ P Q N).hom =
      (α_ ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q)
        ((F.mapHomologicalComplex (.up ℤ)).obj N)).hom ≫
        ((F.mapHomologicalComplex (.up ℤ)).obj P ◁ δ.inv.app (Q, N)) ≫
          δ.inv.app (P, Q ⊗ N) := by
  have hi (K L : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n) :
      HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫ (δ.inv.app (K, L)).f n =
        ν.inv.app (K.X p, L.X q) ≫ F.map (HomologicalComplex.ιTensorObj K L p q n h) := by
    apply (cancel_mono ((δ.hom.app (K, L)).f n)).1
    have hh : (δ.inv.app (K, L)).f n ≫ (δ.hom.app (K, L)).f n = 𝟙 _ :=
      congrArg (fun f ↦ f.f n) (δ.app (K, L)).inv_hom_id
    simp only [Category.assoc, hh, hδ, Iso.inv_hom_id_app_assoc]
    erw [Category.comp_id]
  have hir (X : A) (K L : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n) :
      (HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L) p q n h ▷ X) ≫
        ((δ.inv.app (K, L)).f n ▷ X) =
      (ν.inv.app (K.X p, L.X q) ▷ X) ≫
        (F.map (HomologicalComplex.ιTensorObj K L p q n h) ▷ X) := by
    simpa only [comp_whiskerRight] using congrArg (fun f ↦ f ▷ X) (hi K L p q n h)
  have hil (X : A) (K L : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n) :
      (X ◁ HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L) p q n h) ≫
        (X ◁ (δ.inv.app (K, L)).f n) =
      (X ◁ ν.inv.app (K.X p, L.X q)) ≫
        (X ◁ F.map (HomologicalComplex.ιTensorObj K L p q n h)) := by
    simpa only [MonoidalCategory.whiskerLeft_comp] using
      congrArg (fun f ↦ X ◁ f) (hi K L p q n h)
  have hnl {X X' Y : B} (f : X ⟶ X') :
      (F.map f ▷ F.obj Y) ≫ ν.inv.app (X', Y) =
        ν.inv.app (X, Y) ≫ F.map (f ▷ Y) := by
    have hn := ν.inv.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y)
    dsimp only [Functor.comp_obj, Functor.prod_obj] at hn
    simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id] at hn
    erw [tensorHom_id, tensorHom_id] at hn
    exact hn
  have hnr {X Y Y' : B} (f : Y ⟶ Y') :
      (F.obj X ◁ F.map f) ≫ ν.inv.app (X, Y') =
        ν.inv.app (X, Y) ≫ F.map (X ◁ f) := by
    have hn := ν.inv.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, f)
    dsimp only [Functor.comp_obj, Functor.prod_obj] at hn
    simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id] at hn
    erw [id_tensorHom, id_tensorHom] at hn
    exact hn
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q t h
  have hn : p + q + t = n := h
  have hn' : p + (q + t) = n := by omega
  have key := CochainComplex.Monoidal.ι₁₂_associator_hom P Q N p q t n hn
  rw [CochainComplex.Monoidal.ι₁₂_eq P Q N p q t (p + q) n rfl hn,
    CochainComplex.Monoidal.ι₂₃_eq P Q N p q t (q + t) n rfl hn'] at key
  have key' := congrArg F.map key
  simp only [Functor.map_comp] at key'
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [CochainComplex.Monoidal.ι₁₂_eq _ _ _ p q t (p + q) n rfl hn,
    CochainComplex.Monoidal.ι₁₂_associator_hom_assoc,
    CochainComplex.Monoidal.ι₂₃_eq _ _ _ p q t (q + t) n rfl hn']
  on_goal 2 => exact hn
  simp only [Category.assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f_assoc, reassoc_of% hir _ P Q p q (p + q) rfl,
    reassoc_of% hil _ Q N q t (q + t) rfl,
    reassoc_of% hi (P ⊗ Q) N (p + q) t n hn, hi P (Q ⊗ N) p (q + t) n hn']
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.mapHomologicalComplex_obj_X]
  erw [reassoc_of% hnl (Y := N.X t) (HomologicalComplex.ιTensorObj P Q p q (p + q) rfl),
    reassoc_of% hnr (X := P.X p) (HomologicalComplex.ιTensorObj Q N q t (q + t) rfl)]
  simp only [Category.assoc] at key'
  rw [key']
  exact (reassoc_of% hν (P.X p) (Q.X q) (N.X t)) _

/-- A summand-normalized comparison respects the cochain tensor associator.
Source: Stacks Project, Tag 06YN; the proof of
`Functor.mapCochainComplexμIso_associativity` in the adopted source library.
(blueprint: lem-sf-ringed-forget-chain-associativity)

Proof: the uncurried total tensor maps a pair of morphisms in two successive
steps, whose composite is the native tensor of morphisms by tensor functoriality.
Use this equality to view the comparison as one for the native tensor functors.
Invert the summand equation and restrict the two inverse associativity composites
to each target triple coproduct summand. The summand equation twice, naturality,
and the given underived associativity identify them. Cancel the comparison
isomorphisms to recover the forward equation. No coproduct preservation by F is
required. -/
theorem tensorComparison_chain_associativity
    {B : Type b} [Category.{vb} B] [Preadditive B] [HasZeroObject B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    {A : Type a} [Category.{va} A] [Preadditive A] [HasZeroObject A]
    [MonoidalCategory A] [MonoidalPreadditive A]
    [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (F : B ⥤ A) [F.Additive]
    (ν : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    (δ : Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex) ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex))
    (hδ : ∀ (P Q : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (δ.hom.app (P, Q)).f n =
        ν.hom.app (P.X p, Q.X q) ≫
          HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)
    (hν : ∀ X Y Z : B,
      (ν.inv.app (X, Y) ▷ F.obj Z) ≫ ν.inv.app (X ⊗ Y, Z) ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
          (F.obj X ◁ ν.inv.app (Y, Z)) ≫ ν.inv.app (X, Y ⊗ Z))
    (P Q N : CochainComplex B ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (α_ P Q N).hom ≫ δ.hom.app (P, Q ⊗ N) ≫
        (Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)).map
          (X := ((F.mapHomologicalComplex (.up ℤ)).obj P,
            (F.mapHomologicalComplex (.up ℤ)).obj (Q ⊗ N)))
          (Y := ((F.mapHomologicalComplex (.up ℤ)).obj P,
            (F.mapHomologicalComplex (.up ℤ)).obj Q ⊗ (F.mapHomologicalComplex (.up ℤ)).obj N))
          (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj P), δ.hom.app (Q, N)) =
      δ.hom.app (P ⊗ Q, N) ≫
        (Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)).map
          (X := ((F.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q),
            (F.mapHomologicalComplex (.up ℤ)).obj N))
          (Y := ((F.mapHomologicalComplex (.up ℤ)).obj P ⊗ (F.mapHomologicalComplex (.up ℤ)).obj Q,
            (F.mapHomologicalComplex (.up ℤ)).obj N))
          (δ.hom.app (P, Q), 𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj N)) ≫
        (α_ ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)
          ((F.mapHomologicalComplex (.up ℤ)).obj N)).hom := by
  let V := F.mapHomologicalComplex (.up ℤ)
  let ε : MonoidalCategory.tensor (CochainComplex B ℤ) ⋙ V ≅
      (V.prod V) ⋙ MonoidalCategory.tensor (CochainComplex A ℤ) :=
    NatIso.ofComponents (fun X ↦ δ.app X) (by
      intro X Y f
      rcases f with ⟨f, g⟩
      have hn := δ.hom.naturality (X := X) (Y := Y) (f, g)
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      erw [tensor_map₂_eq (B := B) f g,
        tensor_map₂_eq (B := A) (V.map f) (V.map g)] at hn
      dsimp only [V, Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
        Functor.map₂CochainComplex, Functor.map₂HomologicalComplex_obj_obj] at hn ⊢
      simpa only [Functor.comp_map, Functor.prod_map, tensor_map, Iso.app_hom] using hn)
  have h := chain_inverse_associativity F ν ε hδ hν P Q N
  have hf : V.map (α_ P Q N).hom ≫ ε.hom.app (P, Q ⊗ N) ≫
        (V.obj P ◁ ε.hom.app (Q, N)) =
      ε.hom.app (P ⊗ Q, N) ≫ (ε.hom.app (P, Q) ▷ V.obj N) ≫
        (α_ (V.obj P) (V.obj Q) (V.obj N)).hom := by
    apply (cancel_epi ((ε.inv.app (P, Q) ▷ V.obj N) ≫ ε.inv.app (P ⊗ Q, N))).1
    simp only [Category.assoc]
    rw [reassoc_of% h]
    have hl : (V.obj P ◁ ε.inv.app (Q, N)) ≫ (V.obj P ◁ ε.hom.app (Q, N)) = 𝟙 _ := by
      rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app,
        MonoidalCategory.whiskerLeft_id]
    have hr : (ε.inv.app (P, Q) ▷ V.obj N) ≫ (ε.hom.app (P, Q) ▷ V.obj N) = 𝟙 _ := by
      rw [← comp_whiskerRight, Iso.inv_hom_id_app, id_whiskerRight]
    simp only [Iso.inv_hom_id_app_assoc, reassoc_of% hr]
    erw [hl, Category.comp_id]
  erw [tensor_map₂_eq (B := A) (𝟙 (V.obj P)) (δ.hom.app (Q, N)),
    tensor_map₂_eq (B := A) (δ.hom.app (P, Q)) (𝟙 (V.obj N))]
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.map₂CochainComplex, Functor.map₂HomologicalComplex_obj_obj] at hf ⊢
  simpa only [V, ε, NatIso.ofComponents_hom_app, Iso.app_hom,
    id_tensorHom, tensorHom_id] using hf

end CategoryTheory.RingedForgetTensorTransposition
