/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackTransport
import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.RawAffineComplexSystemMapCoherence

/-! # Canonical cohomology diagram for a fixed derived coefficient -/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] upperStar rawAffineComplexPullback presentationDerivedMap
  presentationRepresentativeIso

/-- A cohomology diagram for the pullbacks of a fixed bounded-below complex. -/
structure FixedDerivedCohomologyDiagram {I : Type u} [SmallCategory I]
    (T : Scheme.{u}) (D : I ⥤ Scheme.{u}) (c : Cone D)
    (t : D ⟶ (Functor.const I).obj T) (p : c.pt ⟶ T)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) where
  H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}
  B : Cocone H
  e : ∀ i : I, H.obj (op i) ≅
    (cohomology AddCommGrpCat.{u + 1} (D.obj i) n).obj
      ((upperStar AddCommGrpCat.{u + 1} (t.app i)).mapDerivedCategory.obj K.obj)
  eY : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt n).obj
    ((upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategory.obj K.obj)
  hm : ∀ {i j : I} (f : i ⟶ j), H.map f.op = (e j).hom ≫
    presentationDerivedMap (D.map f) (t.app j) (t.app i)
      ((Category.comp_id (t.app i)).symm.trans (t.naturality f).symm) K.obj n ≫ (e i).inv
  hs : ∀ i : I, B.ι.app (op i) = (e i).hom ≫
    presentationDerivedMap (c.π.app i) (t.app i) p (hp i).symm K.obj n ≫ eY.inv

-- Construct the functor and cocone for the abstract complex families.
private theorem complexCohomologyDiagram {J : Type u} [SmallCategory J]
    (D : J ⥤ Scheme.{u}) (c : Cone D)
    (K : ∀ i : J, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (hK : ∀ i : J, CochainComplex.plus _ (K i))
    (ψ : ∀ {i j : J} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : J, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : J) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (G : (J)ᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : J, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : J) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : CochainComplex.plus _ L.pt) (p : ℤ) :
    ∃ (H : Jᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H)
      (e : ∀ i : J, H.obj (op i) ≅
        (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (K i)))
      (eY : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
        (DerivedCategory.Q.obj L.pt)),
      (∀ {i j : J} (f : j ⟶ i), H.map f.op = (e i).hom ≫
        rawAffineComplexPullback p (D.map f) (K i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (ψ f)) ≫ (e j).inv) ∧
      (∀ i : J, B.ι.app (op i) = (e i).hom ≫
        rawAffineComplexPullback p (c.π.app i) (K i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))) ≫ eY.inv) := by
  obtain ⟨hmid, hmcomp, hb⟩ := rawAffineComplex_system_map_coherence
    D c K hK ψ hidentity hcomposition G eG hG L hL p
  let H : Jᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun i ↦ (cohomology AddCommGrpCat.{u + 1} (D.obj i.unop) p).obj
        (DerivedCategory.Q.obj (K i.unop))
      map := fun f ↦ rawAffineComplexPullback p (D.map f.unop) (K _) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj _) p).map
          (DerivedCategory.Q.map (ψ f.unop))
      map_id := fun i ↦ hmid i.unop
      map_comp := fun f g ↦ hmcomp _ _ _ f.unop g.unop }
  let B : Cocone H :=
    { pt := (cohomology AddCommGrpCat.{u + 1} c.pt p).obj (DerivedCategory.Q.obj L.pt)
      ι :=
        { app := fun i ↦ rawAffineComplexPullback p (c.π.app i.unop) (K _) ≫
            (cohomology AddCommGrpCat.{u + 1} c.pt p).map
              (DerivedCategory.Q.map ((eG _).inv ≫ L.ι.app i))
          naturality := fun i j f ↦ by
            change (rawAffineComplexPullback p (D.map f.unop) (K _) ≫
              (cohomology AddCommGrpCat.{u + 1} (D.obj _) p).map
                (DerivedCategory.Q.map (ψ f.unop))) ≫
                (rawAffineComplexPullback p (c.π.app j.unop) (K _) ≫
                  (cohomology AddCommGrpCat.{u + 1} c.pt p).map
                    (DerivedCategory.Q.map ((eG _).inv ≫ L.ι.app j))) = _ ≫ 𝟙 _
            erw [Category.comp_id]
            exact hb _ _ f.unop } }
  exact ⟨H, B, (fun _ ↦ Iso.refl _), Iso.refl _,
    (fun _ ↦ by simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]; rfl),
    (fun _ ↦ by simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]; rfl)⟩

set_option maxRecDepth 2048 in
/-- The canonical cocone on the pulled-back bounded-below complex. -/
theorem exists_fixedDerivedCohomologyDiagram {I : Type u} [SmallCategory I]
    (T : Scheme.{u}) (D : I ⥤ Scheme.{u}) (c : Cone D)
    (t : D ⟶ (Functor.const I).obj T) (p : c.pt ⟶ T)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) : Nonempty (FixedDerivedCohomologyDiagram T D c t p hp K n) := by
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsGE a := ha
  obtain ⟨C, hC, ⟨q⟩⟩ := K.obj.exists_iso_Q_obj_of_isGE a
  let F := presentationFamily D t C
  let φ := fun {i j : I} (f : j ⟶ i) ↦ presentationTransition D t C f
  let CY := presentationPullback p C
  let G := (Functor.const Iᵒᵖ).obj CY
  let eG := presentationConeIso D c t p hp C
  let L : Cocone G := constCocone Iᵒᵖ CY
  obtain ⟨hid, hcomp, hG⟩ := presentation_pullback_coherence T D c t p hp C
  have hF (i : I) : CochainComplex.plus _ (F i) := by
    change CochainComplex.plus _ (presentationPullback (t.app i) C)
    refine ⟨a, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro r hr
    exact (upperStar AddCommGrpCat.{u + 1} (t.app i)).map_isZero
      (C.isZero_of_isStrictlyGE a r hr)
  have hCY : CochainComplex.plus _ CY := by
    refine ⟨a, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro r hr
    exact (upperStar AddCommGrpCat.{u + 1} p).map_isZero
      (C.isZero_of_isStrictlyGE a r hr)
  obtain ⟨H, B, eC, eCY, hmC, hsC⟩ := complexCohomologyDiagram
    D c F hF φ hid hcomp G eG hG L hCY n
  let e := fun i ↦ eC i ≪≫ (presentationRepresentativeIso (t.app i) q n).symm
  let eY := eCY ≪≫ (presentationRepresentativeIso p q n).symm
  refine ⟨⟨H, B, e, eY, ?_, ?_⟩⟩
  · intro i j f
    have key := presentation_pullback_transport (D.map f) (t.app j) (t.app i)
      ((Category.comp_id (t.app i)).symm.trans (t.naturality f).symm)
      K.obj n C q (fun {_ _} f A ↦ rawAffineComplexPullback n f A)
        (by intros; unfold rawAffineComplexPullback; rfl)
    rw [hmC]
    dsimp only [e, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
    have hkey := congrArg
      (fun z ↦ (presentationRepresentativeIso (t.app j) q n).inv ≫ z) key
    simp only [Iso.inv_hom_id_assoc] at hkey
    simpa only [F, φ, presentationFamily, presentationTransition, Category.assoc] using
      congrArg (fun z ↦ (eC j).hom ≫ z ≫ (eC i).inv) hkey.symm
  · intro i
    have key := presentation_pullback_transport (c.π.app i) (t.app i) p (hp i).symm
      K.obj n C q (fun {_ _} f A ↦ rawAffineComplexPullback n f A)
        (by intros; unfold rawAffineComplexPullback; rfl)
    rw [hsC]
    dsimp only [e, eY, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
    have hkey := congrArg
      (fun z ↦ (presentationRepresentativeIso (t.app i) q n).inv ≫ z) key
    simp only [Iso.inv_hom_id_assoc] at hkey
    simp only [F, eG, L, presentationFamily, presentationConeIso,
      constCocone, NatTrans.id_app]
    erw [Category.comp_id]
    exact congrArg (fun z ↦ (eC i).hom ≫ z ≫ eCY.inv) hkey.symm
end AlgebraicGeometry.Etale
