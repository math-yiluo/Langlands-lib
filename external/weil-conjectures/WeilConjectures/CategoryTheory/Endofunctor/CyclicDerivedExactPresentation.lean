/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedOffDiagonalPresentation
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact transport of strict cyclic presentations

Source: Stacks Project, Derived Categories, Tag 0152; the exact-functor part of
steps 5--6 of `lem-sf-cyclic-derived-hom-exact-sequence`.
(blueprint: lem-sf-cyclic-derived-exact-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]
  (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private theorem exactComparison_factors (K : CochainComplex (IsoAlgebra F) ℤ) :
    (cyclicDerivedExactForgetComparison F G L e).hom.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map ((forget F).mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app
          (((forget F).mapHomologicalComplex (.up ℤ)).obj K) =
      (forget G).mapDerivedCategory.map ((mapOfNatIso e).mapDerivedCategoryFactors.hom.app K) ≫
        (forget G).mapDerivedCategoryFactors.hom.app
          (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fac (mapOfNatIso e) (forget G) K
  have h₂ := Functor.mapDerivedCategoryCompIso_fac (forget F) L K
  have h₃ := Functor.mapDerivedCategoryNatIso_fac (mapOfNatIsoCompForgetIso e) K
  have id₁ : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (mapOfNatIso e ⋙ forget G)) (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have id₂ : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (forget F ⋙ L)) (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have id₃ : (NatTrans.mapHomologicalComplex (mapOfNatIsoCompForgetIso e).hom
      (.up ℤ)).app K = 𝟙 _ := rfl
  erw [id₁, Functor.map_id, Category.comp_id] at h₁
  erw [id₂, Functor.map_id, Category.comp_id] at h₂
  erw [id₃, Functor.map_id, Category.comp_id] at h₃
  dsimp only [cyclicDerivedExactForgetComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [h₂, h₃, ← h₁]
  simp

private theorem exactComparison_shift (X : DerivedCategory (IsoAlgebra F)) :
    let U := (forget F).mapDerivedCategory
    let V := (forget G).mapDerivedCategory
    let J := (mapOfNatIso e).mapDerivedCategory
    let H := L.mapDerivedCategory
    let α := cyclicDerivedExactForgetComparison F G L e
    α.hom.app X ≫ H.map (U.map
        ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).inv.app X)) ≫
      H.map ((U.commShiftIso (-1 : ℤ)).hom.app (X⟦(1 : ℤ)⟧)) ≫
      (H.commShiftIso (-1 : ℤ)).hom.app (U.obj (X⟦(1 : ℤ)⟧)) =
    V.map ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).inv.app (J.obj X)) ≫
      (V.commShiftIso (-1 : ℤ)).hom.app ((J.obj X)⟦(1 : ℤ)⟧) ≫
      (V.map ((J.commShiftIso (1 : ℤ)).inv.app X))⟦(-1 : ℤ)⟧' ≫
      (α.hom.app (X⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' := by
  dsimp only
  let α := cyclicDerivedExactForgetComparison F G L e
  have : NatTrans.CommShift α.hom ℤ := by
    dsimp [α, cyclicDerivedExactForgetComparison]
    infer_instance
  have h := NatTrans.shift_app_comm α.hom (-1 : ℤ) (X⟦(1 : ℤ)⟧)
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] at h
  rw [← Functor.comp_map, ← α.hom.naturality_assoc]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [← h, Functor.map_shiftFunctorCompIsoId_inv_app]
  simp [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
    ← Functor.commShiftIso_hom_naturality_assoc]
  rfl

private theorem exactComparison_core
    {A B : CochainComplex (IsoAlgebra F) ℤ}
    (z : ((forget F).mapHomologicalComplex (.up ℤ)).obj B ⟶
      ((forget F).mapHomologicalComplex (.up ℤ)).obj A) :
    let V := (forget G).mapDerivedCategory
    let H := L.mapDerivedCategory
    let α := cyclicDerivedExactForgetComparison F G L e
    α.hom.app (DerivedCategory.Q.obj B) ≫
      H.map ((forget F).mapDerivedCategoryFactors.hom.app B ≫ DerivedCategory.Q.map z ≫
        (forget F).mapDerivedCategoryFactors.inv.app A) =
      V.map ((mapOfNatIso e).mapDerivedCategoryFactors.hom.app B) ≫
        (forget G).mapDerivedCategoryFactors.hom.app
          (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj B) ≫
        DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map z) ≫
        (forget G).mapDerivedCategoryFactors.inv.app
          (((mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj A) ≫
        V.map ((mapOfNatIso e).mapDerivedCategoryFactors.inv.app A) ≫
        α.hom.app (DerivedCategory.Q.obj A) := by
  dsimp only
  apply (cancel_mono (L.mapDerivedCategory.map
    ((forget F).mapDerivedCategoryFactors.hom.app A) ≫
      L.mapDerivedCategoryFactors.hom.app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj A))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [exactComparison_factors F G L e A]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]
  rw [Functor.map_comp, Category.assoc, L.mapDerivedCategoryFactors_hom_naturality]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ DerivedCategory.Q.map
      ((L.mapHomologicalComplex (.up ℤ)).map z)) (exactComparison_factors F G L e B)

private theorem exactTransport_endpoints
    {M N M' N' : DerivedCategory (IsoAlgebra F)} (a : M ⟶ M') (c : N' ⟶ N)
    (z : CyclicDerivedHom F M' N' (-1)) :
    let U := (forget F).mapDerivedCategory
    let V := (forget G).mapDerivedCategory
    let J := (mapOfNatIso e).mapDerivedCategory
    let H := L.mapDerivedCategory
    let α := cyclicDerivedExactForgetComparison F G L e
    cyclicDerivedHomTransport F G J H (fun r ↦ H.commShiftIso r) α M N (-1)
      (U.map a ≫ z ≫ (U.map c)⟦(-1 : ℤ)⟧') =
      V.map (J.map a) ≫
        cyclicDerivedHomTransport F G J H (fun r ↦ H.commShiftIso r) α M' N' (-1) z ≫
        (V.map (J.map c))⟦(-1 : ℤ)⟧' := by
  dsimp only
  let α := cyclicDerivedExactForgetComparison F G L e
  have ha := α.hom.naturality a
  have hc := α.inv.naturality c
  simp only [Functor.comp_map, Functor.comp_obj] at ha hc
  dsimp only [α] at ha hc
  dsimp only [cyclicDerivedHomTransport]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
  rw [← reassoc_of% ha]
  rw [← (shiftFunctor (DerivedCategory D) (-1 : ℤ)).map_comp, hc]
  simp only [Functor.map_comp]

private theorem cancellation_natural
    {X Y : DerivedCategory (IsoAlgebra G)} (b : X ⟶ Y) :
    let V := (forget G).mapDerivedCategory
    let η := shiftFunctorCompIsoId (DerivedCategory (IsoAlgebra G)) (1 : ℤ) (-1) (by omega)
    V.map b ≫ V.map (η.inv.app Y) ≫
        (V.commShiftIso (-1 : ℤ)).hom.app (Y⟦(1 : ℤ)⟧) =
      V.map (η.inv.app X) ≫ (V.commShiftIso (-1 : ℤ)).hom.app (X⟦(1 : ℤ)⟧) ≫
        (V.map (b⟦(1 : ℤ)⟧'))⟦(-1 : ℤ)⟧' := by
  dsimp only
  let η := shiftFunctorCompIsoId (DerivedCategory (IsoAlgebra G)) (1 : ℤ) (-1) (by omega)
  have h := η.inv.naturality b
  change b ≫ η.inv.app Y = η.inv.app X ≫ b⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧' at h
  rw [← Functor.map_comp_assoc, h, Functor.map_comp]
  simp only [Category.assoc, Functor.commShiftIso_hom_naturality]
  rfl

private theorem exactTransport_class
    {S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)}
    (z : ((forget F).mapHomologicalComplex (.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (.up ℤ)).obj S.X₁) :
    let V := (forget G).mapDerivedCategory
    let J := (mapOfNatIso e).mapDerivedCategory
    let Jc := (mapOfNatIso e).mapHomologicalComplex (.up ℤ)
    let H := L.mapDerivedCategory
    let α := cyclicDerivedExactForgetComparison F G L e
    cyclicDerivedHomTransport F G J H (fun r ↦ H.commShiftIso r) α
        (DerivedCategory.Q.obj S.X₃) ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧) (-1)
        (cyclicDerivedOffDiagonalClass F z) =
      V.map ((mapOfNatIso e).mapDerivedCategoryFactors.hom.app S.X₃) ≫
        cyclicDerivedOffDiagonalClass G (S := S.map Jc)
          ((L.mapHomologicalComplex (.up ℤ)).map z) ≫
        (V.map (((mapOfNatIso e).mapDerivedCategoryFactors.inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
          (J.commShiftIso (1 : ℤ)).inv.app (DerivedCategory.Q.obj S.X₁)))⟦(-1 : ℤ)⟧' := by
  dsimp only
  let U := (forget F).mapDerivedCategory
  let V := (forget G).mapDerivedCategory
  let J := (mapOfNatIso e).mapDerivedCategory
  let H := L.mapDerivedCategory
  let α := cyclicDerivedExactForgetComparison F G L e
  let X := DerivedCategory.Q.obj S.X₁
  let η := shiftFunctorCompIsoId (DerivedCategory (IsoAlgebra F)) (1 : ℤ) (-1) (by omega)
  let core := (forget F).mapDerivedCategoryFactors.hom.app S.X₃ ≫
    DerivedCategory.Q.map z ≫ (forget F).mapDerivedCategoryFactors.inv.app S.X₁
  calc
    _ = (α.hom.app (DerivedCategory.Q.obj S.X₃) ≫ H.map core) ≫
        H.map (U.map (η.inv.app X)) ≫ H.map ((U.commShiftIso (-1 : ℤ)).hom.app
          (X⟦(1 : ℤ)⟧)) ≫ (H.commShiftIso (-1 : ℤ)).hom.app (U.obj (X⟦(1 : ℤ)⟧)) ≫
          (α.inv.app (X⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' := by
      simp only [cyclicDerivedHomTransport, cyclicDerivedOffDiagonalClass, core,
        Functor.map_comp, Category.assoc]
      rfl
    _ = _ := by
      rw [exactComparison_core F G L e z]
      simp only [Category.assoc]
      rw [reassoc_of% (exactComparison_shift F G L e X)]
      have hα := ((shiftFunctor (DerivedCategory D) (-1 : ℤ)).mapIso
        (α.app (X⟦(1 : ℤ)⟧))).hom_inv_id
      change (α.hom.app (X⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' ≫
        (α.inv.app (X⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' = 𝟙 _ at hα
      rw [hα]
      erw [Category.comp_id]
      rw [reassoc_of% (cancellation_natural G
        ((mapOfNatIso e).mapDerivedCategoryFactors.inv.app S.X₁))]
      simp only [cyclicDerivedOffDiagonalClass, Functor.map_comp, Category.assoc]
      rfl

/-- Applying the exact equivariant functor to a strict presentation preserves its
underlying shifted class and its native connecting morphism.

Proof: apply the termwise functor to the short exact complex sequence. The image of
its underlying splitting is still a splitting. Apply L to the off-diagonal equation
and use naturality of e to move it through the two chain maps; this gives exactly
the target off-diagonal equation. The endpoint isomorphisms are the images of the
old ones composed with the exact localization factors and the canonical shift
comparison. The localization composition comparisons identify the new shifted class
with cyclicDerivedHomTransport of the old one. Finally
DerivedCategory.map_triangleOfSESδ identifies the transported native morphism with
the image SES boundary, including its sign. No injective representative or bound is
needed, since L is exact on all short exact sequences.

Source: Stacks Tag 0152; exact case of parent steps 5--6.
(blueprint: lem-sf-cyclic-derived-exact-presentation). -/
theorem cyclicDerivedOffDiagonalPresentation_mapExact
    {M N : DerivedCategory (IsoAlgebra F)} {u : CyclicDerivedHom F M N (-1)}
    {f : M ⟶ N} (hp : CyclicDerivedOffDiagonalPresentation F u f) :
    CyclicDerivedOffDiagonalPresentation G
      (cyclicDerivedHomTransport F G (mapOfNatIso e).mapDerivedCategory
        L.mapDerivedCategory (fun r ↦ L.mapDerivedCategory.commShiftIso r)
        (cyclicDerivedExactForgetComparison F G L e) M N (-1) u)
      ((mapOfNatIso e).mapDerivedCategory.map f) := by
  obtain ⟨S, hS, u₀, s, a, c, hs, he, hu, hf⟩ := hp
  let J := (mapOfNatIso e).mapDerivedCategory
  let Jc := (mapOfNatIso e).mapHomologicalComplex (.up ℤ)
  let Lc := L.mapHomologicalComplex (.up ℤ)
  let a' := J.mapIso a ≪≫ (mapOfNatIso e).mapDerivedCategoryFactors.app S.X₃
  let c' := (shiftFunctor _ (1 : ℤ)).mapIso
      ((mapOfNatIso e).mapDerivedCategoryFactors.app S.X₁).symm ≪≫
    (J.commShiftIso (1 : ℤ)).symm.app (DerivedCategory.Q.obj S.X₁) ≪≫ J.mapIso c
  refine ⟨S.map Jc, hS.map_of_exact Jc, Lc.map u₀, Lc.map s, a', c', ?_, ?_, ?_, ?_⟩
  · change Lc.map s ≫ Lc.map (((forget F).mapHomologicalComplex (.up ℤ)).map S.g) = 𝟙 _
    rw [← Lc.map_comp, hs, Lc.map_id]
  · intro n
    let en (X : C) : G.obj (L.obj X) ⟶ L.obj (F.obj X) := e.hom.app X
    let sn : (S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier := s.f n
    let un : (S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier := u₀.f n
    let jn : (S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier := (forget F).map (S.f.f n)
    change G.map (L.map sn) ≫
        (en (S.X₂.X n).carrier ≫ L.map (S.X₂.X n).str.hom) =
      (en (S.X₃.X n).carrier ≫ L.map (S.X₃.X n).str.hom) ≫ L.map sn +
        G.map (L.map un) ≫ (en (S.X₁.X n).carrier ≫
          L.map (S.X₁.X n).str.hom) ≫ L.map jn
    have h := congrArg L.map (he n)
    change L.map (F.map sn ≫ (S.X₂.X n).str.hom) =
      L.map ((S.X₃.X n).str.hom ≫ sn +
        F.map un ≫ (S.X₁.X n).str.hom ≫ jn) at h
    simp only [Functor.map_comp, Functor.map_add] at h
    have hn := e.hom.naturality sn
    have hn' := e.hom.naturality un
    change G.map (L.map sn) ≫ en (S.X₂.X n).carrier =
      en (S.X₃.X n).carrier ≫ L.map (F.map sn) at hn
    change G.map (L.map un) ≫ en (S.X₁.X n).carrier =
      en (S.X₃.X n).carrier ≫ L.map (F.map un) at hn'
    simp only [← Category.assoc]
    rw [hn, hn']
    simpa only [Category.assoc, Preadditive.comp_add] using
      congrArg (fun t ↦ en (S.X₃.X n).carrier ≫ t) h
  · rw [hu, exactTransport_endpoints F G L e a.hom c.hom,
      exactTransport_class F G L e u₀]
    simp only [a', c', Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.map_comp, Category.assoc]
    rfl
  · dsimp [a', c', J]
    rw [hf, Functor.map_comp, Functor.map_comp, DerivedCategory.map_triangleOfSESδ]
    simp only [Category.assoc]

end CategoryTheory.Endofunctor.IsoAlgebra
