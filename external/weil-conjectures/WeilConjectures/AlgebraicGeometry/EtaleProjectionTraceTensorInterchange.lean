/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # Interchanging a trace contraction with a symmetric coefficient

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, second triangle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

variable (A : Type (u + 1)) [CommRing A]

section Generic
open MonoidalCategory Functor.OplaxMonoidal
variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Braided]

private theorem self_symmetry (L : C) (hL : (β_ L L).hom = 𝟙 _) :
    (β_ (F.obj L) (F.obj L)).hom = 𝟙 _ := by
  apply (cancel_mono (Functor.LaxMonoidal.μ F L L)).1
  rw [← Functor.LaxBraided.braided, hL, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]

private noncomputable def leftProjection (K : C) (E : D) :
    K ⊗ G.obj E ⟶ G.obj (F.obj K ⊗ E) :=
  (β_ K (G.obj E)).hom ≫
    ((adj.rightAdjointProjectionMap (δNatTrans F)).app E).app K ≫
    G.map (β_ E (F.obj K)).hom

private theorem leftProjection_counit (K : C) (E : D) :
    F.map (leftProjection adj K E) ≫ adj.counit.app _ =
      δ F K (G.obj E) ≫ F.obj K ◁ adj.counit.app E := by
  simp only [leftProjection, Functor.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  rw [adj.map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  simp only [curriedTensor_map_app, Functor.OplaxMonoidal.δNatTrans_app_app]
  rw [Functor.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← BraidedCategory.braiding_naturality_right_assoc]
  simp only [SymmetricCategory.symmetry, Category.comp_id]

private theorem tensor_shuffle (K B L : C) (e : F.obj B ⟶ F.obj L)
    (h : (β_ (F.obj L) (F.obj L)).hom = 𝟙 _) :
    δ F (K ⊗ B) L ≫ δ F K B ▷ F.obj L ≫ (F.obj K ◁ e) ▷ F.obj L =
      F.map ((α_ K B L).hom ≫ K ◁ (β_ B L).hom ≫ (α_ K L B).inv) ≫
        δ F (K ⊗ L) B ≫ δ F K L ▷ F.obj B ≫ (F.obj K ⊗ F.obj L) ◁ e := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.associativity_inv_assoc,
    ← Functor.OplaxMonoidal.δ_natural_right_assoc]
  have hb : F.map (β_ B L).hom ≫ δ F L B =
      δ F B L ≫ (β_ (F.obj B) (F.obj L)).hom := by
    rw [Functor.map_braiding]
    simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hb]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.associativity_assoc]
  congr 1
  rw [← associator_inv_naturality_right]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    ← BraidedCategory.braiding_naturality_left, h,
    Category.comp_id]
  rw [← associator_naturality_middle_assoc]
  simp only [Iso.hom_inv_id, Category.comp_id]

private theorem mixedProjection (K L : C)
    (h : (β_ (F.obj L) (F.obj L)).hom = 𝟙 _) :
    leftProjection adj K (F.obj L) ▷ L ≫
        ((adj.rightAdjointProjectionMap (δNatTrans F)).app (F.obj K ⊗ F.obj L)).app L =
      ((α_ K (G.obj (F.obj L)) L).hom ≫ K ◁ (β_ (G.obj (F.obj L)) L).hom ≫
        (α_ K L (G.obj (F.obj L))).inv) ≫
      leftProjection adj (K ⊗ L) (F.obj L) ≫ G.map (δ F K L ▷ F.obj L) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [adj.map_rightAdjointProjectionMap_app_app_comp_counit]
  simp only [curriedTensor_map_app, Functor.OplaxMonoidal.δNatTrans_app_app]
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc,
    ← comp_whiskerRight, leftProjection_counit]
  erw [adj.counit_naturality]
  rw [reassoc_of% (leftProjection_counit adj (K ⊗ L) (F.obj L))]
  rw [whisker_exchange]
  simp only [comp_whiskerRight]
  simpa only [Functor.map_comp, Category.assoc] using
    tensor_shuffle K (G.obj (F.obj L)) L (adj.counit.app (F.obj L)) h

private theorem trace_shuffle (K B L : C) (t : B ⟶ 𝟙_ C) :
    ((K ◁ t) ≫ (ρ_ K).hom) ▷ L =
      ((α_ K B L).hom ≫ K ◁ (β_ B L).hom ≫ (α_ K L B).inv) ≫
        (K ⊗ L) ◁ t ≫ (ρ_ (K ⊗ L)).hom := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← BraidedCategory.braiding_naturality_left]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    braiding_tensorUnit_left]
  rw [rightUnitor_tensor_hom, Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id,
    Category.comp_id, ← triangle_assoc_comp_right,
    ← associator_naturality_middle_assoc]
  simp only [Iso.hom_inv_id_assoc]

private theorem generic_interchange (K L : C)
    (h : (β_ (F.obj L) (F.obj L)).hom = 𝟙 _)
    (t : G.obj (F.obj L) ⟶ 𝟙_ C)
    (q : K ⊗ G.obj (F.obj L) ≅ G.obj (F.obj K ⊗ F.obj L))
    (q' : (K ⊗ L) ⊗ G.obj (F.obj L) ≅ G.obj (F.obj (K ⊗ L) ⊗ F.obj L))
    (hq : q.hom = leftProjection adj K (F.obj L))
    (hq' : q'.hom = leftProjection adj (K ⊗ L) (F.obj L)) :
    (G.map (δ F K L) ≫ q.inv ≫ K ◁ t ≫ (ρ_ K).hom) ▷ L =
      ((adj.rightAdjointProjectionMap (δNatTrans F)).app (F.obj (K ⊗ L))).app L ≫
        q'.inv ≫ (K ⊗ L) ◁ t ≫ (ρ_ (K ⊗ L)).hom := by
  let d := asIso (δ F K L)
  let p := q ≪≫ G.mapIso d.symm
  have n := NatTrans.congr_app
    ((adj.rightAdjointProjectionMap (δNatTrans F)).naturality d.inv) L
  change G.map d.inv ▷ L ≫
      ((adj.rightAdjointProjectionMap (δNatTrans F)).app (F.obj (K ⊗ L))).app L =
    ((adj.rightAdjointProjectionMap (δNatTrans F)).app (F.obj K ⊗ F.obj L)).app L ≫
      G.map (d.inv ▷ F.obj L) at n
  have hp : p.hom ▷ L ≫
      ((adj.rightAdjointProjectionMap (δNatTrans F)).app (F.obj (K ⊗ L))).app L =
      ((α_ K (G.obj (F.obj L)) L).hom ≫ K ◁ (β_ (G.obj (F.obj L)) L).hom ≫
        (α_ K L (G.obj (F.obj L))).inv) ≫ q'.hom := by
    dsimp only [p, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [comp_whiskerRight, Category.assoc, n, ← Category.assoc, hq,
      mixedProjection adj K L h]
    simp only [Category.assoc, ← G.map_comp, ← comp_whiskerRight]
    have hd : δ F K L ≫ d.inv = 𝟙 _ := d.hom_inv_id
    simp only [hd, id_whiskerRight, G.map_id, Category.comp_id]
    rw [hq']
  apply (cancel_epi (p.hom ▷ L)).1
  rw [← comp_whiskerRight]
  have hc : p.hom ≫ (G.map (δ F K L) ≫ q.inv ≫ K ◁ t ≫ (ρ_ K).hom) =
      K ◁ t ≫ (ρ_ K).hom := by
    dsimp only [p, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    simp only [Category.assoc]
    change q.hom ≫ G.map d.inv ≫ G.map d.hom ≫ q.inv ≫ _ = _
    simp only [← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp,
      Iso.hom_inv_id_assoc]
  rw [hc, reassoc_of% hp]
  simp only [Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using trace_shuffle K (G.obj (F.obj L)) L t

end Generic

open MonoidalCategory

private theorem interchange_general
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {W X : Scheme.{u}} (p : W ⟶ X)
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    (hL : ((derivedTensorSymmetry B X).app L).hom.app L = 𝟙 _)
    (t : (lowerStar B p).rightDerivedFunctor.obj
      ((upperStar B p).leftDerivedFunctor.obj L) ⟶
        𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology B)))
    (q : ((derivedTensor B X).obj K).obj
        ((lowerStar B p).rightDerivedFunctor.obj ((upperStar B p).leftDerivedFunctor.obj L)) ≅
      (lowerStar B p).rightDerivedFunctor.obj (((derivedTensor B W).obj
        ((upperStar B p).leftDerivedFunctor.obj K)).obj
          ((upperStar B p).leftDerivedFunctor.obj L)))
    (q' : ((derivedTensor B X).obj (((derivedTensor B X).obj K).obj L)).obj
        ((lowerStar B p).rightDerivedFunctor.obj ((upperStar B p).leftDerivedFunctor.obj L)) ≅
      (lowerStar B p).rightDerivedFunctor.obj (((derivedTensor B W).obj
        ((upperStar B p).leftDerivedFunctor.obj (((derivedTensor B X).obj K).obj L))).obj
          ((upperStar B p).leftDerivedFunctor.obj L)))
    (hq : q.hom = ((derivedTensorSymmetry B X).app K).hom.app
        ((lowerStar B p).rightDerivedFunctor.obj ((upperStar B p).leftDerivedFunctor.obj L)) ≫
      ((rightDerivedLowerStarProjectionMap B p).app
        ((upperStar B p).leftDerivedFunctor.obj L)).app K ≫
      (lowerStar B p).rightDerivedFunctor.map
        (((derivedTensorSymmetry B W).app ((upperStar B p).leftDerivedFunctor.obj L)).hom.app
          ((upperStar B p).leftDerivedFunctor.obj K)))
    (hq' : q'.hom = ((derivedTensorSymmetry B X).app
        (((derivedTensor B X).obj K).obj L)).hom.app
          ((lowerStar B p).rightDerivedFunctor.obj ((upperStar B p).leftDerivedFunctor.obj L)) ≫
      ((rightDerivedLowerStarProjectionMap B p).app
        ((upperStar B p).leftDerivedFunctor.obj L)).app (((derivedTensor B X).obj K).obj L) ≫
      (lowerStar B p).rightDerivedFunctor.map
        (((derivedTensorSymmetry B W).app ((upperStar B p).leftDerivedFunctor.obj L)).hom.app
          ((upperStar B p).leftDerivedFunctor.obj (((derivedTensor B X).obj K).obj L)))) :
    ((derivedTensor B X).map
      ((lowerStar B p).rightDerivedFunctor.map (leftDerivedUpperStarTensorIso B p K L).hom ≫
        q.inv ≫ ((derivedTensor B X).obj K).map t ≫
        (derivedTensorRightUnitor B X K).hom)).app L =
      ((rightDerivedLowerStarProjectionMap B p).app
        ((upperStar B p).leftDerivedFunctor.obj (((derivedTensor B X).obj K).obj L))).app L ≫
      q'.inv ≫ ((derivedTensor B X).obj (((derivedTensor B X).obj K).obj L)).map t ≫
        (derivedTensorRightUnitor B X (((derivedTensor B X).obj K).obj L)).hom := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology B)
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf W.smallEtaleTopology B)
  let := leftDerivedUpperStarMonoidal B p
  let : ((upperStar B p).leftDerivedFunctor).Braided :=
    { braided := leftDerivedUpperStar_μ_map_braiding_hom B p }
  have h : (CategoryTheory.BraidedCategory.braiding
      ((upperStar B p).leftDerivedFunctor.obj L)
      ((upperStar B p).leftDerivedFunctor.obj L)).hom = 𝟙 _ := by
    exact self_symmetry (F := (upperStar B p).leftDerivedFunctor) L hL
  exact generic_interchange (derivedUpperStarLowerStarAdjunction B p) K L h t q q' hq hq'

/-- Tensor extraction commutes with an extra copy of a self symmetric coefficient.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, second triangle, rearrangement of the even shifts;
Stacks 0B56, projection-formula map.
(auxiliary; not a blueprint node).

Proof: transpose the two projection composites under p* adjoint Rp*. Projection
associativity says that extracting K and then L agrees with extracting K tensor L,
with the canonical pullback tensor comparison and associators. Conjugate by the
canonical symmetries to put the outside coefficient first. The remaining permutation
interchanges the two copies of p*L. Braidedness of pullback transports hL to say this
permutation is identity. Naturality of the symmetry for t moves the trace onto the
other copy. Associator/right-unitor coherence cancels the tensor unit. All projection
maps are invertible because A is finite and p is proper, so invert the resulting
square to obtain this equality. This calculation uses just p and t, no self-product
square, exchange morphism, or trace base change hypothesis. -/
theorem projectionTraceTensorInterchange [Finite A] {W X : Scheme.{u}}
    (p : W ⟶ X) [IsProper p] (K L : DerivedCategoryModule A X)
    (hL : (swap A X L L).hom = 𝟙 _)
    (t : (push A p).obj ((pull A p).obj L) ⟶ constantComplex A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((push A p).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) p K L).hom ≫
          (orderedProjectionIso A p K ((pull A p).obj L)).inv ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj K).map t ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X K).hom)).app L =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app
        ((pull A p).obj (tensor A X K L))).app L ≫
      (orderedProjectionIso A p (tensor A X K L) ((pull A p).obj L)).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj (tensor A X K L)).map t ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X (tensor A X K L)).hom := by
  exact interchange_general (ModuleCat.{u + 1} A) p K L hL t
    (orderedProjectionIso A p K ((pull A p).obj L))
    (orderedProjectionIso A p (tensor A X K L) ((pull A p).obj L)) rfl rfl

end AlgebraicGeometry.Etale.CoordinateTrace
