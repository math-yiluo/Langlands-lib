/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Transporting derived comparisons through the homotopy quotient

Source: Stacks 06XN and 0FND; the quotient of complexes by chain homotopy.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a av b bv da db
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  (E : A ⥤ B) [E.Additive]

/-- A universal comparison on complexes descends to the homotopy category, with exactly
its original components. Source: Stacks 06XN, the ordinary localization construction
(auxiliary; not a blueprint node).
Proof: precomposition by the full, essentially surjective homotopy quotient is fully
faithful. Lift the comparison through this full functor. To prove its universal property,
whisker a competing comparison with the quotient and use the given universal property on
complexes. Faithfulness of precomposition proves the factorization identity. For uniqueness,
use the same faithfulness followed by uniqueness on complexes. All comparison isomorphisms
between the two quotient functors have identity components, so the lifted comparison has
the prescribed components. -/
theorem exists_homotopy_leftDerived_comparison
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (εc : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hc : T.IsLeftDerivedFunctor εc (HomologicalComplex.quasiIso A (.up ℤ))) :
    ∃ ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh,
      T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) ∧
        ∀ P : CochainComplex A ℤ,
          ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) =
            T.map ((DerivedCategory.quotientCompQhIso A).hom.app P) ≫ εc.app P ≫
              (DerivedCategory.quotientCompQhIso B).inv.app
                ((E.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let α : q ⋙ (DerivedCategory.Qh ⋙ T) ⟶ q ⋙ F :=
    Functor.whiskerRight i.hom T ≫ εc ≫ j.inv
  let H := (Functor.whiskeringLeft _ _ (DerivedCategory B)).obj q
  have : H.Full := inferInstance
  let ε := H.preimage α
  have hε : Functor.whiskerLeft q ε = α := H.map_preimage α
  have hkan : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := by
    let := hc.isRightKanExtension
    constructor
    constructor
    let β (X : Functor.RightExtension DerivedCategory.Qh F) :
        DerivedCategory.Q ⋙ X.left ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      Functor.whiskerRight i.inv X.left ≫ Functor.whiskerLeft q X.hom ≫ j.hom
    let γ (X : Functor.RightExtension DerivedCategory.Qh F) : X.left ⟶ T :=
      T.liftOfIsRightKanExtension εc X.left (β X)
    have hf (X : Functor.RightExtension DerivedCategory.Qh F) :
        Functor.whiskerLeft DerivedCategory.Qh (γ X) ≫ ε = X.hom := by
      apply H.map_injective
      ext P
      have he := congrArg (fun t ↦ t.app P) hε
      change ε.app (q.obj P) = _ at he
      change (γ X).app _ ≫ ε.app _ = _
      rw [he]
      change (γ X).app _ ≫ (T.map (i.hom.app P) ≫ εc.app P ≫ j.inv.app P) = _
      rw [← Category.assoc, ← NatTrans.naturality, Category.assoc]
      have hg := T.liftOfIsRightKanExtension_fac_app εc X.left (β X) P
      change (γ X).app _ ≫ εc.app P = _ at hg
      rw [← Category.assoc ((γ X).app _) (εc.app P), hg]
      change X.left.map (i.hom.app P) ≫
        ((X.left.map (i.inv.app P) ≫ X.hom.app (q.obj P) ≫ j.hom.app P) ≫ j.inv.app P) =
          X.hom.app (q.obj P)
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id_app]
      change X.left.map (i.hom.app P) ≫ (X.left.map (i.inv.app P) ≫
        (X.hom.app (q.obj P) ≫ 𝟙 _)) = _
      rw [Category.comp_id, ← Category.assoc, ← X.left.map_comp, Iso.hom_inv_id_app,
        X.left.map_id, Category.id_comp]
    refine ⟨IsTerminal.ofUniqueHom
      (fun X ↦ CostructuredArrow.homMk (γ X) (hf X)) ?_⟩
    intro X m
    apply CostructuredArrow.hom_ext
    apply T.hom_ext_of_isRightKanExtension εc
    ext P
    let μ : X.left ⟶ T := m.left
    have hm := congrArg (fun t ↦ t.app (q.obj P)) (CostructuredArrow.w m)
    have he := congrArg (fun t ↦ t.app P) hε
    change ε.app (q.obj P) = _ at he
    change μ.app _ ≫ ε.app _ = X.hom.app _ at hm
    rw [he] at hm
    have hg := T.liftOfIsRightKanExtension_fac_app εc X.left (β X) P
    change (γ X).app _ ≫ εc.app P = (β X).app P at hg
    change μ.app _ ≫ εc.app P = (γ X).app _ ≫ εc.app P
    rw [hg]
    apply (cancel_epi (X.left.map (i.hom.app P))).1
    apply (cancel_mono (j.inv.app P)).1
    change (X.left.map (i.hom.app P) ≫ (μ.app _ ≫ εc.app P)) ≫ j.inv.app P =
      (X.left.map (i.hom.app P) ≫ (X.left.map (i.inv.app P) ≫
        X.hom.app (q.obj P) ≫ j.hom.app P)) ≫ j.inv.app P
    rw [← Category.assoc (X.left.map _) (μ.app _), μ.naturality,
      Category.assoc, Category.assoc]
    change μ.app _ ≫ α.app P = _
    rw [hm]
    rw [Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_app]
    change _ = X.left.map (i.hom.app P) ≫ (X.left.map (i.inv.app P) ≫
      (X.hom.app (q.obj P) ≫ 𝟙 _))
    rw [Category.comp_id, ← Category.assoc, ← X.left.map_comp, Iso.hom_inv_id_app,
      X.left.map_id, Category.id_comp]
  refine ⟨ε, hkan, ?_⟩
  intro P
  have he := congrArg (fun t ↦ t.app P) hε
  change ε.app (q.obj P) = _ at he
  simpa [α, j, Functor.mapHomotopyCategoryFactors] using he

end CategoryTheory
