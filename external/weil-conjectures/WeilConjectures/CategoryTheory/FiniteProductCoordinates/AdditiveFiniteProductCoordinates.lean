/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Pi.Basic

/-! # Coordinate bilimits of an additive finite-product equivalence

Source: the finite-product argument for the clopen derived decomposition.
(blueprint: lem-pur-additive-finite-product-coordinate-decomposition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.FiniteProductCoordinates

/-- Pointwise preadditivity on a family of categories.
Source: the pointwise additive-category construction
(blueprint: lem-pur-additive-finite-product-coordinate-decomposition). -/
@[instance_reducible]
def piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) where
  homGroup M N := inferInstanceAs (AddCommGroup (∀ i, M i ⟶ N i))
  add_comp _ _ _ f g h := funext (fun i ↦ Preadditive.add_comp _ _ _ (f i) (g i) (h i))
  comp_add _ _ _ f g h := funext (fun i ↦ Preadditive.comp_add _ _ _ (f i) (g i) (h i))

attribute [local instance] piPreadditive

private def coordinateTransport {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] {i k : J} (h : i = k) : D i ⥤ D k := by
  subst k
  exact 𝟭 _

private def coordinateInsertion {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] (i : J) : D i ⥤ ∀ k, D k := by
  classical
  exact Functor.pi' (fun k ↦ if h : i = k then coordinateTransport D h
    else (Functor.const _).obj (show D k from HasZeroObject.zero.choose))

private def coordinateProjection {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] [∀ i, HasZeroMorphisms (D i)]
    (i : J) : 𝟭 (∀ k, D k) ⟶ Pi.eval D i ⋙ coordinateInsertion D i := by
  classical
  apply NatTrans.pi'
  intro k
  change Pi.eval D k ⟶ Pi.eval D i ⋙
    (if h : i = k then coordinateTransport D h
      else (Functor.const _).obj (show D k from HasZeroObject.zero.choose))
  by_cases h : i = k
  · subst k
    simpa only [dite_true, coordinateTransport] using
      (Functor.rightUnitor (Pi.eval D i)).inv
  · exact 0

private def coordinateInclusion {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] [∀ i, HasZeroMorphisms (D i)]
    (i : J) : Pi.eval D i ⋙ coordinateInsertion D i ⟶ 𝟭 (∀ k, D k) := by
  classical
  apply NatTrans.pi'
  intro k
  change (Pi.eval D i ⋙
    (if h : i = k then coordinateTransport D h
      else (Functor.const _).obj (show D k from HasZeroObject.zero.choose)))
      ⟶ Pi.eval D k
  by_cases h : i = k
  · subst k
    simpa only [dite_true, coordinateTransport] using
      (Functor.rightUnitor (Pi.eval D i)).hom
  · exact 0

private def coordinateBicone {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)] :
    Bicone (fun i ↦ Pi.eval D i ⋙ coordinateInsertion D i) := by
  classical
  refine
    { pt := 𝟭 _
      π := coordinateProjection D
      ι := coordinateInclusion D
      ι_π := ?_ }
  intro i k
  by_cases h : i = k
  · subst k
    simp only [dite_true, eqToHom_refl]
    apply NatTrans.ext
    funext M l
    by_cases hl : i = l
    · subst l
      simp [coordinateProjection, coordinateInclusion, coordinateInsertion,
        coordinateTransport, NatTrans.pi', Functor.pi', Pi.eval]
    · have hz : IsZero ((coordinateInsertion D i).obj (M i) l) := by
        simpa only [coordinateInsertion, Functor.pi'_obj, dite_eq_right hl, Functor.const_obj_obj]
          using (HasZeroObject.zero (C := D l)).choose_spec
      exact hz.eq_of_src _ _
  · simp only [dite_eq_right h]
    apply NatTrans.ext
    funext M l
    by_cases hi : i = l
    · subst l
      simp [coordinateProjection, coordinateInclusion, NatTrans.pi', Ne.symm h]
      rfl
    · simp [coordinateProjection, coordinateInclusion, NatTrans.pi', hi]
      rfl

private theorem coordinateBicone_total {J : Type*} [Fintype J] (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)] :
    ∑ i, (coordinateBicone D).π i ≫ (coordinateBicone D).ι i = 𝟙 _ := by
  classical
  apply NatTrans.ext
  funext M k
  rw [NatTrans.app_sum]
  have he {S : Finset J} (f : J → ∀ i, M i ⟶ M i) :
      (∑ i ∈ S, f i) k = ∑ i ∈ S, f i k := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi hS => simp [Finset.sum_insert hi, hS]
  rw [he]
  change (∑ i, (coordinateProjection D i).app M k ≫
    (coordinateInclusion D i).app M k) = 𝟙 (M k)
  rw [Finset.sum_eq_single k]
  · simp [coordinateProjection, coordinateInclusion, NatTrans.pi',
      coordinateTransport]
  · intro i _ hi
    simp [coordinateProjection, coordinateInclusion, NatTrans.pi', hi]
  · simp

/-- An additive equivalence with a finite product gives zero insertions and two bilimits.
Source: finite-product calculation in the clopen derived decomposition
(blueprint: lem-pur-additive-finite-product-coordinate-decomposition).

Proof: insert at one coordinate and use the chosen zero object at all other coordinates.
The coordinate projection-inclusion composites sum to the identity. Map this bicone
through the additive inverse equivalence to obtain a bilimit on the product side and,
after conjugating by the unit isomorphism, a bilimit on the source side. The diagonal
and off-diagonal comparison formulas follow from the counit and the zero objects. -/
theorem equivalenceCoordinateDecomposition
    {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)] (E : C ≌ ∀ i, D i) [E.inverse.Additive] :
    ∃ e : ∀ i, D i ⥤ C,
      (∀ i, Nonempty (e i ⋙ (E.functor ⋙ Pi.eval D i) ≅ 𝟭 _)) ∧
      (∀ i k, i ≠ k → ∀ M, IsZero ((e k ⋙ (E.functor ⋙ Pi.eval D i)).obj M)) ∧
      (∃ s : ∀ i, D i ⥤ ∀ k, D k,
        ∀ i, e i = s i ⋙ E.inverse ∧
          Nonempty (s i ⋙ Pi.eval D i ≅ 𝟭 _) ∧
          (∀ k, k ≠ i → ∀ M, IsZero ((s i).obj M k))) ∧
      (∃ b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i),
        b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) ∧
      (∃ b : Bicone (fun i ↦ Pi.eval D i ⋙ e i),
        b.pt = E.inverse ∧ Nonempty b.IsBilimit) := by
  classical
  let := Fintype.ofFinite J
  let s := coordinateInsertion D
  let e (i : J) := s i ⋙ E.inverse
  have hs (i : J) : s i ⋙ Pi.eval D i ≅ 𝟭 _ := by
    dsimp only [s, coordinateInsertion]
    refine Functor.pi'CompEval _ i ≪≫ ?_
    simpa only [dite_true, coordinateTransport] using (Iso.refl (𝟭 (D i)))
  have hz (i k : J) (h : k ≠ i) (M : D i) : IsZero ((s i).obj M k) := by
    simpa [s, coordinateInsertion, Ne.symm h] using (HasZeroObject.zero (C := D k)).choose_spec
  refine ⟨e, ?_, ?_, ⟨s, fun i ↦ ⟨rfl, ⟨hs i⟩, hz i⟩⟩, ?_, ?_⟩
  · intro i
    exact ⟨Functor.associator (s i) E.inverse (E.functor ⋙ Pi.eval D i) ≪≫
      Functor.isoWhiskerLeft (s i) ((Functor.associator E.inverse E.functor (Pi.eval D i)).symm ≪≫
        Functor.isoWhiskerRight E.counitIso (Pi.eval D i) ≪≫ Functor.leftUnitor _) ≪≫ hs i⟩
  · intro i k hik M
    exact IsZero.of_iso (hz k i hik M) (Pi.isoApp (E.counitIso.app ((s k).obj M)) i)
  · let H : ((∀ i, D i) ⥤ ∀ i, D i) ⥤ (C ⥤ C) :=
      (Functor.whiskeringLeft C (∀ i, D i) (∀ i, D i)).obj E.functor ⋙
        (Functor.whiskeringRight C (∀ i, D i) C).obj E.inverse
    have : H.Additive := inferInstance
    let b' := H.mapBicone (coordinateBicone D)
    have ht : ∑ i, b'.π i ≫ b'.ι i = 𝟙 b'.pt := by
      change ∑ i, H.map _ ≫ H.map _ = 𝟙 _
      simp only [← H.map_comp, ← H.map_sum, coordinateBicone_total, H.map_id]
    let b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i) :=
      { pt := 𝟭 _
        π i := E.unitIso.hom ≫ b'.π i
        ι i := b'.ι i ≫ E.unitIso.inv
        ι_π i k := by
          change (b'.ι i ≫ E.unitIso.inv) ≫ (E.unitIso.hom ≫ b'.π k) = _
          rw [Category.assoc, Iso.inv_hom_id_assoc]
          exact b'.ι_π i k }
    refine ⟨b, rfl, ⟨isBilimitOfTotal b ?_⟩⟩
    change ∑ i, (E.unitIso.hom ≫ b'.π i) ≫ (b'.ι i ≫ E.unitIso.inv) = 𝟙 _
    have ht' : ∑ i, b'.π i ≫ b'.ι i = 𝟙 (E.functor ⋙ E.inverse) := ht
    simpa only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id] using
      congrArg (fun f ↦ E.unitIso.hom ≫ f ≫ E.unitIso.inv) ht'
  · let H : ((∀ i, D i) ⥤ ∀ i, D i) ⥤ ((∀ i, D i) ⥤ C) :=
      (Functor.whiskeringRight _ _ _).obj E.inverse
    let b' := H.mapBicone (coordinateBicone D)
    have ht : ∑ i, b'.π i ≫ b'.ι i = 𝟙 b'.pt := by
      change ∑ i, H.map _ ≫ H.map _ = 𝟙 _
      simp only [← H.map_comp, ← H.map_sum, coordinateBicone_total, H.map_id]
    exact ⟨b', rfl, ⟨isBilimitOfTotal b' ht⟩⟩

end CategoryTheory.FiniteProductCoordinates
