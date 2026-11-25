/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleComplexFiltrationPageData
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.CofilteredEtaleCohomologyContinuity
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Cohomology colimits of evaluated complex terms

Source: Stacks Project, Tags 09YQ and 0032.
(blueprint: lem-weil-pbc-complex-term-cohomology-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

-- Keep the pullback and cohomology constructions folded during component comparisons.
attribute [local irreducible] upperStar upperStarComp upperStarId
  Sheaf.H.map cohomologyMap

-- Reduce the mapped-complex wrappers without expanding the pullback constructions.
attribute [local implicit_reducible] NatTrans.mapHomologicalComplex NatIso.mapHomologicalComplex

set_option backward.isDefEq.respectTransparency true in
private theorem complexTermCohomologyMap_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L) (r : ℕ) (s : ℤ) :
    complexTermCohomologyMap f K L v r s =
      AddCommGrpCat.ofHom (cohomologyMap f (K.X s) r) ≫
      AddCommGrpCat.ofHom (Sheaf.H.map
        (F := (upperStar AddCommGrpCat.{u + 1} f).obj (K.X s))
        (G := L.X s) (v.f s) r) := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.dsimp.instances true in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
/-- Ordinary sheaf cohomology preserves the cocone of evaluated complex terms.
Source: Stacks Project, Theorem 59.51.3 (Tag 09YQ).

Proof: Evaluate G, its object isomorphisms eG, and its colimit cocone L at s.
Evaluation preserves complex colimits. Taking components at s of hidentity,
hcomposition, and hG gives the three scalar sheaf coherence equations. Apply
nonempty_isColimit_etale_cohomology_of_cofiltered_isLimit to this scalar system
in degree r. Expanding complexTermCohomologyMap gives cohomologyMap followed by
Sheaf.H.map, so hH and hB supply exactly its cohomology arrow and cocone-leg
conditions. The scalar theorem performs directed replacement (Stacks Tag 0032)
and applies ordinary directed continuity (Tag 09YQ), then transports the colimit
back through finality. No lower bound or spectral-sequence data enter this argument.
Edge cases: I is nonempty by cofilteredness. Degree zero and zero term sheaves are
included in 09YQ; the argument does not require torsion.
(blueprint: lem-weil-pbc-complex-term-cohomology-colimit). -/
theorem nonempty_isColimit_complex_term_cohomology
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (r : ℕ) (s : ℤ)
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op ≫ (eH j).hom =
      (eH i).hom ≫ complexTermCohomologyMap (D.map f) (F i) (F j) (φ f) r s)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ complexTermCohomologyMap (c.π.app i) (F i) L.pt
        ((eG i).inv ≫ L.ι.app (op i)) r s) :
    Nonempty (IsColimit B) := by
  classical
  let E := HomologicalComplex.eval
    (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ) s
  let F' := fun i : I ↦ (F i).X s
  let φ' {i j : I} (f : j ⟶ i) :
      (upperStar AddCommGrpCat.{u + 1} (D.map f)).obj (F' i) ⟶ F' j := (φ f).f s
  have hid : ∀ i : I, φ' (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i))).hom.app
        (F' i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj i)).hom.app (F' i) := by
    intro i
    simpa only [φ', F', HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f] using
      congrArg (fun v ↦ v.f s) (hidentity i)
  have hcomp : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j), φ' (g ≫ f) =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
        (D.map (g ≫ f)) (D.map_comp g f)).hom.app (F' i) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map g)).map (φ' f) ≫ φ' g := by
    intro i j k f g
    simpa only [φ', F', HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f] using
      congrArg (fun v ↦ v.f s) (hcomposition i j k f g)
  let G' := G ⋙ E
  let L' := E.mapCocone L
  have hL' : IsColimit L' := isColimitOfPreserves E hL
  let eG' := fun i : I ↦ HomologicalComplex.Hom.isoApp (eG i) s
  have hG' : ∀ (i j : I) (f : j ⟶ i), G'.map f.op = (eG' i).hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
        (c.π.app i) (c.w f).symm).hom.app (F' i) ≫
      (upperStar AddCommGrpCat.{u + 1} (c.π.app j)).map (φ' f) ≫ (eG' j).inv := by
    intro i j f
    simpa only [G', E, eG', F', φ', Functor.comp_map, Functor.comp_obj,
      HomologicalComplex.eval_obj,
      HomologicalComplex.eval_map, HomologicalComplex.comp_f,
      HomologicalComplex.Hom.isoApp_hom, HomologicalComplex.Hom.isoApp_inv,
      NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f] using
      congrArg (fun v ↦ v.f s) (hG i j f)
  have hcontinuity := nonempty_isColimit_etale_cohomology_of_cofiltered_isLimit
    D c hc F' @φ' hid hcomp G' eG' hG' L' hL' r H eH
  dsimp only [E, L', Functor.mapCocone, HomologicalComplex.eval,
    Functor.const_obj_obj] at hcontinuity
  apply hcontinuity ?_ B eB ?_
  · intro i j f
    simpa only [complexTermCohomologyMap_eq] using hH i j f
  · intro i
    have hh := hB i
    rw [complexTermCohomologyMap_eq] at hh
    dsimp only [eG', E, L', F', HomologicalComplex.Hom.isoApp, Functor.mapIso,
      Functor.mapCocone, HomologicalComplex.eval, HomologicalComplex.comp_f,
      Functor.const_obj_obj] at hh ⊢
    exact hh

end AlgebraicGeometry.Etale
