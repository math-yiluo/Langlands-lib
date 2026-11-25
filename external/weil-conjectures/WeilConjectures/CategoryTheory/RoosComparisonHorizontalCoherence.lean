/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.StrictRoosModel

/-! # Horizontal coherence of the canonical additive Roos comparison

Source: Stacks Tag 0941, lemma-derived-limit-is-ok, product-cone context, and the
explicit coordinate calculation in the blueprint proof
(auxiliary; not a blueprint node).

The comparison is constructed directly by Mathlib's `mappingCocone.lift` on the fixed
`roosF` model, using the two mapped projections and the canonical product comparison.
No exactness or preservation of products is assumed for its definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe uA vA uB vB uD vD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasCountableProducts D]

/-- Termwise application of an additive functor to a complex of strict towers.
Source: Stacks Tag 0941, product-cone context
(auxiliary; not a blueprint node). -/
def roosTowerAction (F : A ⥤ B) [F.Additive] :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The product comparison as a cochain map, determined by its product projections.
Source: Stacks Tag 0941, product-cone context
(auxiliary; not a blueprint node). -/
def roosProductComparison (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (roosP X) ⟶
      roosP ((roosTowerAction F).obj X) :=
  piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ))
    (fun n : ℕ ↦ X.asFunctor.obj (op n))

private lemma productComparison_u (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosU X) ≫
        roosProductComparison F X =
      roosProductComparison F X ≫ roosU ((roosTowerAction F).obj X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
    change FC.map (roosU X) ≫ piComparison FC _ =
      piComparison FC _ ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ FC.map (X.asFunctor.map (homOfLE (Nat.le_succ n)).op))
    apply Pi.hom_ext
    intro n
    simp [roosU, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, Functor.map_comp]

private lemma cocone_snd_delta (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0 (CochainComplex.mappingCocone.snd (roosU X)) =
      -CochainComplex.HomComplex.Cochain.ofHom
        (CochainComplex.mappingCocone.fst (roosU X) ≫ roosU X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    open CochainComplex.HomComplex in
    dsimp only [CochainComplex.mappingCocone.snd]
    rw [Cochain.δ_leftShift _ (-1) (-1) 0 (by omega) 1 (by omega),
      CochainComplex.mappingCone.δ_snd]
    simp [CochainComplex.mappingCocone.fst]

/-- The compatibility equation for the two coordinates of the additive Roos lift.
Source: Stacks Tag 0941, product-cone context
(auxiliary; not a blueprint node).
Proof: DAG steps 1-3. The mapping cocone projections satisfy
δ(snd) + ofHom(fst ≫ u) = 0, by the signed cone differential. Applying the additive
functor preserves this equation, since it preserves sums, negatives and composition.
Postcompose both coordinates with the product comparison. Its square with u = 1-s
commutes: after the nth product projection both sides are F(π_n - π_(n+1) ≫ t_n),
using `towerTransitionEndomorphism` and additivity. The differential of a cochain
postcomposed with a chain map is its differential postcomposed with that map.
Thus the mapped cocone equation becomes exactly the displayed lift condition. -/
theorem roosAdditiveComparison_lift_condition (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (((CochainComplex.mappingCocone.snd (roosU X)).map F).comp
          (CochainComplex.HomComplex.Cochain.ofHom (roosProductComparison F X))
          (add_zero (-1))) +
      CochainComplex.HomComplex.Cochain.ofHom
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (CochainComplex.mappingCocone.fst (roosU X)) ≫
          roosProductComparison F X) ≫ roosU ((roosTowerAction F).obj X)) = 0 := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    open CochainComplex.HomComplex in
    rw [δ_comp_ofHom, δ_map, cocone_snd_delta]
    simp only [Cochain.map_neg, Cochain.map_ofHom, Cochain.neg_comp,
      ← Cochain.ofHom_comp, Functor.map_comp]
    rw [Category.assoc, productComparison_u]
    simp only [Category.assoc, neg_add_cancel]

/-- The canonical two-coordinate comparison in the fixed `roosF` model, constructed
by the mapping cocone lift of the mapped projections followed by the product
comparison on both coordinates. The product comparison commutes with 1-s, as used
in `roosAdditiveComparison_lift_condition`.
Source: Stacks Tag 0941, product-cone context
(auxiliary; not a blueprint node). -/
def roosAdditiveComparison (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (roosF.obj X) ⟶
      roosF.obj ((roosTowerAction F).obj X) :=
  CochainComplex.mappingCocone.lift (roosU ((roosTowerAction F).obj X))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCocone.fst (roosU X)) ≫ roosProductComparison F X)
    (((CochainComplex.mappingCocone.snd (roosU X)).map F).comp
      (CochainComplex.HomComplex.Cochain.ofHom (roosProductComparison F X))
      (add_zero (-1)))
    (roosAdditiveComparison_lift_condition F X)

private lemma cocone_fst_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (CochainComplex.mappingCocone.fst (roosU X)).f (p + 1) =
      (roosχ X p).hom ≫ biprod.snd := roosProj_f X p

private lemma cocone_snd_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (CochainComplex.mappingCocone.snd (roosU X)).v (p + 1) p (by omega) =
      (roosχ X p).hom ≫ biprod.fst := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
        HomologicalComplex.homotopyCofiber.sndX (roosU X) r =
          (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) r q hq).hom ≫
            biprod.snd := by
      obtain rfl := (ComplexShape.up ℤ).next_eq' hq
      dsimp only [HomologicalComplex.homotopyCofiber.sndX]
      rw [dite_eq_left hq]
    simp [roosχ, CochainComplex.mappingCocone.snd,
      CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.snd,
      hs p (p + 1) rfl, show Int.negOnePow 2 = 1 by rfl]

/-- The fixed degree-p+1 formula: biproduct comparison followed by the product
comparisons in degrees p and p+1.
Source: Stacks Tag 0941 (auxiliary; not a blueprint node).
Proof: DAG steps 1-3. The biproduct comparison is determined by the images of the
projections, with inverse determined by the images of the inclusions. Additivity
preserves negatives and sums. The product comparison commutes with d and 1-s after
each product projection. The signed differential matrix therefore commutes with
the displayed comparison. The two projection identities for `mappingCocone.lift`,
transported through `roosχ`, give precisely the displayed coordinate formula. -/
theorem roosAdditiveComparison_coordinates (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom =
      F.map (roosχ X p).hom ≫ F.biprodComparison ((roosP X).X p)
        ((roosP X).X (p + 1)) ≫
        biprod.map ((roosProductComparison F X).f p)
          ((roosProductComparison F X).f (p + 1)) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, Functor.biprodComparison_fst_assoc]
      rw [← cocone_snd_coordinates]
      dsimp only [roosAdditiveComparison]
      rw [CochainComplex.mappingCocone.lift_f_snd_v]
      simp only [CochainComplex.HomComplex.Cochain.comp_v (n₁ := -1) (n₂ := 0) _ _ _
          (p + 1) p p (by omega) (add_zero p),
        CochainComplex.HomComplex.Cochain.map_v,
        CochainComplex.HomComplex.Cochain.ofHom_v, cocone_snd_coordinates,
        Functor.map_comp, Category.assoc]
    · simp only [Category.assoc, biprod.map_snd, Functor.biprodComparison_snd_assoc]
      rw [← cocone_fst_coordinates]
      dsimp only [roosAdditiveComparison]
      rw [CochainComplex.mappingCocone.lift_f_fst_f]
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        cocone_fst_coordinates, Functor.map_comp, Category.assoc]

private lemma comparison_fst (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom ≫ biprod.fst =
      F.map ((roosχ X p).hom ≫ biprod.fst) ≫ (roosProductComparison F X).f p := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosAdditiveComparison_coordinates]
    simp [Functor.map_comp]

private lemma comparison_snd (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom ≫ biprod.snd =
      F.map ((roosχ X p).hom ≫ biprod.snd) ≫
        (roosProductComparison F X).f (p + 1) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosAdditiveComparison_coordinates]
    simp [Functor.map_comp]

/-- Preservation of countable products makes this very comparison an isomorphism.
Source: Stacks Tag 0941 (auxiliary; not a blueprint node).
Proof: DAG step 6. Each product comparison is invertible by preservation of its
product cone. The biproduct comparison is invertible by additivity. Thus the
coordinate formula gives degreewise inverses; the chain-map equation implies
that these inverses commute with differentials, giving an inverse chain map. -/
theorem roosAdditiveComparison_isIso (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso (roosAdditiveComparison F X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have : PreservesLimitsOfShape (Discrete ℕ)
        (F.mapHomologicalComplex (ComplexShape.up ℤ)) := by
      apply HomologicalComplex.preservesLimitsOfShape_of_eval
      intro n
      exact inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
        (HomologicalComplex.eval A (ComplexShape.up ℤ) n ⋙ F))
    have : IsIso (roosProductComparison F X) := by
      dsimp only [roosProductComparison]
      infer_instance
    have : ∀ k : ℤ, IsIso ((roosAdditiveComparison F X).f k) := by
      intro k
      obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
      change IsIso ((roosAdditiveComparison F X).f (p + 1))
      have : IsIso ((roosAdditiveComparison F X).f (p + 1) ≫
          (roosχ ((roosTowerAction F).obj X) p).hom) := by
        rw [roosAdditiveComparison_coordinates]
        have : ∀ r : ℤ, IsIso ((roosProductComparison F X).f r) := fun r ↦
          inferInstanceAs (IsIso ((HomologicalComplex.eval B (ComplexShape.up ℤ) r).map
            (roosProductComparison F X)))
        have : PreservesBinaryBiproduct ((roosP X).X p) ((roosP X).X (p + 1)) F :=
          preservesBinaryBiproduct_of_preservesBiproduct F _ _
        have : IsIso (F.biprodComparison ((roosP X).X p) ((roosP X).X (p + 1))) :=
          (F.mapBiprod ((roosP X).X p) ((roosP X).X (p + 1))).isIso_hom
        have hfirst : IsIso (F.map (roosχ X p).hom) := (F.mapIso (roosχ X p)).isIso_hom
        have hlast : IsIso (biprod.map ((roosProductComparison F X).f p)
            ((roosProductComparison F X).f (p + 1))) :=
          (biprod.mapIso (asIso ((roosProductComparison F X).f p))
            (asIso ((roosProductComparison F X).f (p + 1)))).isIso_hom
        exact IsIso.comp_isIso' hfirst (IsIso.comp_isIso' inferInstance hlast)
      exact IsIso.of_isIso_comp_right _ (roosχ ((roosTowerAction F).obj X) p).hom
    exact HomologicalComplex.Hom.isIso_of_components _

/-- A strict augmentation retains its zero shifted coordinate and its mapped family.
Source: Stacks Tag 0941 (auxiliary; not a blueprint node).
Proof: DAG step 7. Compose the coordinate formula with F(q). Its first product
coordinates are F(0)=0 and its second product coordinates are F(q_n).
The original compatibility equation remains true after applying F. Product
extensionality gives the displayed biproduct-coordinate equality. -/
theorem roosAdditiveComparison_augmentation (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (P : CochainComplex A ℤ)
    (q : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hq : ∀ n : ℕ, q (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = q n)
    (p : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosAugment q hq) ≫
        roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom =
      biprod.lift 0
        ((Pi.lift (fun n : ℕ ↦
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (q n))).f (p + 1)) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    apply biprod.hom_ext
    · simp only [Category.assoc, comparison_fst]
      have h := congrArg (fun f ↦ f ≫ biprod.fst) (roosAugment_χ q hq p)
      simp only [Category.assoc, biprod.lift_fst] at h
      rw [← Category.assoc, ← F.map_comp, h, F.map_zero, zero_comp]
      exact (biprod.lift_fst _ _).symm
    · simp only [Category.assoc, comparison_snd, biprod.lift_snd]
      have h := congrArg (fun f ↦ f ≫ biprod.snd) (roosAugment_χ q hq p)
      simp only [Category.assoc, biprod.lift_snd] at h
      rw [← Category.assoc, ← F.map_comp, h]
      exact congrArg (fun f ↦ f.f (p + 1))
        (map_lift_piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (fun n : ℕ ↦ X.asFunctor.obj (op n)) P q)

end CategoryTheory
