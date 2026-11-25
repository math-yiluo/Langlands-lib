/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackTransport
import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackCoherence

/-! # Complex presentation of canonical derived pullback cocones

Source: Stacks Project, Étale Cohomology, Tag 0GIT, proof (termwise pullbacks).
(blueprint: lem-weil-pbc-etale-complex-pullback-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true

/-- Algebraic data for applying complex continuity to the pullbacks of `C`.
The data record coherence and canonical maps, without any colimit assertion.
Source: Stacks Project, Tag 0GIT, proof, termwise colimit identification
(blueprint: lem-weil-pbc-etale-complex-pullback-presentation). -/
structure ComplexPullbackPresentation
    {I : Type u} [SmallCategory I] (T : Scheme.{u})
    (D : I ⥤ Scheme.{u}) (c : Cone D) (t : D ⟶ (Functor.const I).obj T)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (n : ℤ) (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H)
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y n).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X n).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (L : Cocone G) where
  F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ
  F_eq : ∀ i : I, F i =
    ((upperStar AddCommGrpCat.{u + 1} (t.app i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C
  φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j
  hidentity : ∀ i : I, φ (𝟙 i) = presentationIdentityMap D i (F i)
  hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g
  eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i)
  hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv
  eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) n).obj (DerivedCategory.Q.obj (F i))
  hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) n).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv
  eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt n).obj
      (DerivedCategory.Q.obj L.pt)
  hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt n).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))

/-- Present a canonical derived cohomology cocone using termwise pullbacks of a
complex representative. No limit universal property or qcqs/affineness hypothesis
is required here, and no cohomology colimit is asserted.
Source: Stacks Project, Étale Cohomology, Tag 0GIT, proof, lines 7869-7873;
canonical-map identification in the proof of Tag 0EZM
(blueprint: lem-weil-pbc-etale-complex-pullback-presentation).

Proof: set `F i` to the termwise inverse image of `C` along `t.app i`.
Take `φ f` to be the inverse of the complex comparison for composition of
inverse images. The unit and associativity laws for `upperStarComp` give
`hidentity` and `hcomposition`. On the site of `c.pt`, take `G` to be the
constant diagram with value the termwise inverse image of `C` along `p`.
The composition comparison and `hp` give `eG`; associativity and the cone
identity give `hG`. Take `L` to be its identity cocone. The given equation `hP` specifies
the canonical cohomology pullback map. For `eH`,
compose `e i` with the cohomology image of the derived pullback of `q` and
the exact-functor localization factorization `mapDerivedCategoryFactors`.
Define `eB` similarly, using `eY`, `q`, and the factorization at `p`.
Naturality of the adjunction unit, of the Leray comparison, and of the
localization factorization identifies the formula `hm` with `hH`.
The same naturality for each projection, followed by `hp`, identifies
`hs` with `hB`. The right-derived composition isomorphism appearing in
`hP` is exactly the one defining the Leray isomorphism in `hm` and `hs`.
These identities provide all fields without using cohomology continuity. -/
theorem nonempty_complexPullbackPresentation
    {I : Type u}
    [SmallCategory I]
    [IsCofiltered I]
    (T : Scheme.{u})
    (D : I ⥤ Scheme.{u})
    (c : Cone D)
    (t : D ⟶ (Functor.const I).obj T)
    (p : c.pt ⟶ T)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ)
    (F : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (e : ∀ i : I, F.obj (op i) ≅
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj i) n).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app i)).mapDerivedCategory.obj K))
    (hm : ∀ {i j : I} (f : i ⟶ j), F.map f.op =
      (e j).hom ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj j) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (D.map f)).unit.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app j)).mapDerivedCategory.obj
              K)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{u + 1} (D.map f)).hom.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (D.map f)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app j)).mapDerivedCategory.obj
                K))) ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj i) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (D.map f) (t.app j)
            (t.app i) ((Category.comp_id (t.app i)).symm.trans (t.naturality f).symm)) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{u + 1} (t.app j))
            (Etale.upperStar AddCommGrpCat.{u + 1} (D.map f))).symm).inv.app K) ≫
      (e i).inv)
    (s : Cocone F)
    (eY : s.pt ≅ (Etale.cohomology AddCommGrpCat.{u + 1} c.pt n).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategory.obj K))
    (hs : ∀ i : I, s.ι.app (op i) =
      (e i).hom ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (c.π.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app i)).mapDerivedCategory.obj
              K)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{u + 1} (c.π.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app i)).mapDerivedCategory.obj
                K))) ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} c.pt n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i) (t.app i) p
            (hp i).symm) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{u + 1} (t.app i))
            (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app i))).symm).inv.app K) ≫
      eY.inv)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (q : K ≅ DerivedCategory.Q.obj C)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y n).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X n).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K))) :
    Nonempty (ComplexPullbackPresentation T D c t C n F s
      ((Functor.const Iᵒᵖ).obj
        (((upperStar AddCommGrpCat.{u + 1} p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) P
      (constCocone Iᵒᵖ
        (((upperStar AddCommGrpCat.{u + 1} p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C))) := by
  let A := fun i : I =>
      ((upperStar AddCommGrpCat.{u + 1} (t.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C
  let φ := fun {i j : I} (f : j ⟶ i) =>
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (D.map f) (t.app i) (t.app j)
          ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm))
        (ComplexShape.up ℤ)).inv.app C
  let eG := fun i : I =>
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app i) (t.app i) p (hp i).symm)
        (ComplexShape.up ℤ)).app C
  let eH := fun i : I => e i ≪≫ presentationRepresentativeIso (t.app i) q n
  let eB := eY ≪≫ presentationRepresentativeIso p q n
  refine ⟨⟨A, (fun _ => rfl), φ,
    (presentation_pullback_coherence T D c t p hp C).1,
    (presentation_pullback_coherence T D c t p hp C).2.1,
    eG, (presentation_pullback_coherence T D c t p hp C).2.2,
    eH, ?_, eB, ?_⟩⟩
  · intro i j f
    have key := presentation_pullback_transport (D.map f) (t.app i) (t.app j)
      ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm) K n C q P hP
    change F.map f.op =
      (eH i).hom ≫ P (D.map f) (presentationPullback (t.app i) C) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) n).map
          (DerivedCategory.Q.map (presentationTransition D t C f)) ≫ (eH j).inv
    have hm' : F.map f.op = (e i).hom ≫
        presentationDerivedMap (D.map f) (t.app i) (t.app j)
          ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm) K n ≫
        (e j).inv := hm f
    rw [← cancel_mono (eH j).hom, hm']
    simpa only [eH, Iso.trans_hom, Iso.trans_inv, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
      presentationTransition] using congrArg (fun a => (e i).hom ≫ a) key
  · intro i
    have key := presentation_pullback_transport (X := c.pt) (Y := D.obj i)
      (T := T) (c.π.app i) (t.app i) p
      (hp i).symm K n C q P hP
    change s.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (presentationPullback (t.app i) C) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt n).map
          (DerivedCategory.Q.map
            ((presentationConeIso D c t p hp C i).inv ≫ 𝟙 _))
    have hs' : s.ι.app (op i) = (e i).hom ≫
        presentationDerivedMap (c.π.app i) (t.app i) p (hp i).symm K n ≫ eY.inv :=
      hs i
    rw [hs']
    simpa only [eB, eH, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Category.comp_id, presentationConeIso] using
      congrArg (fun a => (e i).hom ≫ a) key




end AlgebraicGeometry.Etale
