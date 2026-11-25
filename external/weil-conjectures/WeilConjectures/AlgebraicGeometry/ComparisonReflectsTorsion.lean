/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap

/-!
# Reflection of local torsion by the etale to pro-etale comparison

Source: Stacks Tags 099T and 03SA; proper-base-change proof, torsion descent.
(blueprint: lem-pe-comparison-reflects-local-torsion).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

private theorem coverLift {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {V : T.ProEt} (R : Sieve V) (hR : R ∈ Scheme.ProEt.topology T V)
    (v : Spec (.of Ω) ⟶ V.left) :
    ∃ (W : T.ProEt) (g : W ⟶ V) (_ : R g) (w : Spec (.of Ω) ⟶ W.left),
      w ≫ g.left = v := by
  obtain ⟨S, hS, hSR⟩ := Scheme.ProEt.mem_topology_iff.1 hR
  obtain ⟨ι, Z, f, rfl⟩ := S.exists_eq_ofArrows
  have hS' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage V.left := by
    simpa only [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, Scheme.ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst] using hS
  have hb := Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hS' v
    (fun i ↦ pullback.snd (f i).left v) (fun i ↦ pullback.fst (f i).left v)
    (fun i ↦ (IsPullback.of_hasPullback (f i).left v).flip)
  obtain ⟨i, z, hz⟩ :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hb)).1
      (IsLocalRing.closedPoint Ω)
  have : WeaklyEtale (f i).left :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hS')).2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd (f i).left v) z
  refine ⟨Z i, f i, hSR _ _ ⟨i⟩, σ ≫ pullback.fst (f i).left v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem stalkTorsion (T : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (hF : ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F).IsTorsion) :
    IsAddTorsion (Scheme.proEtaleGeometricFixedModuleStalk t A F) := by
  classical
  let D := Scheme.proEtaleGeometricStalkDiagram t F
  have : PreservesColimitsOfShape (Scheme.ProEtaleGeometricNeighbourhood t)ᵒᵖ
      (forget (ModuleCat.{u + 1} A)) :=
    Functor.Final.preservesColimitsOfShape_of_final
      (FinallySmall.fromFilteredFinalModel.{u + 1} _) _
  intro x
  obtain ⟨i, s, rfl⟩ := Concrete.colimit_exists_rep D x
  obtain ⟨S, hS, h⟩ := hF s
  obtain ⟨W, g, hg, w, hw⟩ := coverLift S hS i.unop.hom.left
  let Wp : Scheme.ProEtaleGeometricNeighbourhood t := StructuredArrow.mk (Y := W)
    (Over.homMk w (by
      change w ≫ W.hom = t
      rw [← MorphismProperty.Over.w g, ← Category.assoc, hw]
      exact Over.w i.unop.hom))
  let a : Wp ⟶ i.unop := StructuredArrow.homMk g (by
    apply Over.OverMorphism.ext
    exact hw)
  have he : colimit.ι D i s =
      colimit.ι D (Opposite.op Wp) (F.obj.map g.op s) :=
    (ConcreteCategory.congr_hom (colimit.w D a.op) s).symm
  rw [he]
  obtain ⟨n, hn, hz⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (h hg)
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n, hn, ?_⟩
  change n • (colimit.ι D (Opposite.op Wp)).hom (F.obj.map g.op s) = 0
  change n • (F.obj.map g.op).hom s = 0 at hz
  rw [← map_nsmul, hz, map_zero]

private noncomputable def torsionComparisonPoint
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) : (Scheme.ProEt.topology T).Point.{u + 1} where
  fiber := (Scheme.ProEt.forget T ⋙ coyoneda.obj (Opposite.op (Over.mk t))) ⋙
    uliftFunctor.{u + 1}
  isCofiltered := by
    have : IsCofiltered
        (Scheme.ProEt.forget T ⋙ coyoneda.obj (Opposite.op (Over.mk t))).Elements :=
      Functor.isCofiltered_elements _
    exact .of_equivalence
      (Functor.Elements.uliftEquivalence.{u + 1}
        (Scheme.ProEt.forget T ⋙ coyoneda.obj (Opposite.op (Over.mk t)))).symm
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR x := by
    obtain ⟨W, g, hg, w, hw⟩ := coverLift R hR x.down.left
    refine ⟨W, g, hg, ULift.up (Over.homMk w ?_), ?_⟩
    · change w ≫ W.hom = t
      rw [← MorphismProperty.Over.w g, ← Category.assoc, hw]
      exact Over.w x.down
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hw

private noncomputable def torsionComparisonPointElements
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    Scheme.ProEtaleGeometricNeighbourhood t ≌ (torsionComparisonPoint t).fiber.Elements where
  functor.obj n := Functor.elementsMk _ n.right (ULift.up n.hom)
  functor.map f := ⟨f.right, congrArg ULift.up f.w⟩
  inverse.obj n := StructuredArrow.mk n.2.down
  inverse.map f := StructuredArrow.homMk f.1 (congrArg ULift.down f.2)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

private theorem torsionComparison_coverPreserving (T : Scheme.{u}) :
    CoverPreserving T.smallEtaleTopology (Scheme.ProEt.topology T) (Scheme.toProEt T) := by
  rw [Scheme.ProEt.topology_eq_restrictedTopology]
  exact MorphismProperty.Over.coverPreserving_changeProp T etale_le_weaklyEtale
    etaleTopology_le_proetaleTopology

private noncomputable def torsionComparisonPointStalkIso
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] :
    sheafToPresheaf (Scheme.ProEt.topology T) A ⋙
      (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ A).obj
        (Scheme.proEtaleGeometricNeighbourhoodForget t).op ⋙ colim ≅
      (torsionComparisonPoint t).sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf (Scheme.ProEt.topology T) A)
    (Functor.isoWhiskerLeft
      ((Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π
        (torsionComparisonPoint t).fiber).op)
      (Functor.Final.colimIso (torsionComparisonPointElements t).functor.op))

set_option backward.isDefEq.respectTransparency false in
/-- The geometric stalk of the comparison inverse image is the etale stalk.
This is the isomorphism part of the canonical comparison of geometric stalks
(Stacks Project, Tags 0GLZ, 0993 and 05V1). -/
private theorem torsion_comparison_stalkIso
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] [HasColimitsOfSize.{u, u} A]
    [HasProducts.{u + 1} A]
    (L : Sheaf T.smallEtaleTopology A ⥤ Sheaf (Scheme.ProEt.topology T) A)
    (adj : L ⊣ (Scheme.toProEt T).sheafPushforwardContinuous A
      T.smallEtaleTopology (Scheme.ProEt.topology T)) :
    Nonempty (L ⋙ sheafToPresheaf (Scheme.ProEt.topology T) A ⋙
      (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ A).obj
        (Scheme.proEtaleGeometricNeighbourhoodForget t).op ⋙ colim ≅
      (Scheme.pointSmallEtale t).sheafFiber) := by
  let := adj.isRightAdjoint
  let Φ := torsionComparisonPoint t
  let hF := torsionComparison_coverPreserving T
  let a := (Scheme.toProEt T).sheafAdjunctionContinuous A T.smallEtaleTopology
    (Scheme.ProEt.topology T)
  let e := adj.leftAdjointUniq a
  have : InitiallySmall.{u + 1} ((Scheme.toProEt T) ⋙ Φ.fiber).Elements := by
    change InitiallySmall.{u + 1} ((Scheme.pointSmallEtale t).ulift.{u + 1}).fiber.Elements
    infer_instance
  let b := Φ.sheafFiberComapIso (Scheme.toProEt T) hF A
  let hb : (Φ.comap (Scheme.toProEt T) hF).sheafFiber ≅
      ((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber (A := A) := Iso.refl _
  exact ⟨Functor.isoWhiskerLeft L (torsionComparisonPointStalkIso t A) ≪≫
    Functor.isoWhiskerRight e Φ.sheafFiber ≪≫ b.symm ≪≫ hb ≪≫
      (Scheme.pointSmallEtale t).uliftSheafFiberIso.{u + 1} A⟩

/-- Exact fully faithful comparison inverse image reflects local integer torsion.
Source: Stacks Tags 099T and 03SA, and blueprint theorem-proper-base-change-classical-pro, opening
paragraph (blueprint: lem-pe-comparison-reflects-local-torsion).
Proof: every germ in the pro-etale geometric stalk is represented by a section on
 a pointed weakly etale neighbourhood. A covering on which that section is torsion
 has a member lifting the geometric point: base change to the algebraically closed
 field and split a nonempty weakly etale member. The restricted section is killed
 by a positive integer, so its germ is too. The canonical comparison-stalk
 isomorphism transfers torsion to the etale stalk. Forgetting scalars commutes with
 these filtered colimits. The conservative family of algebraically closed etale
 points then gives local torsion on the original module sheaf. No uniform integer
 annihilator or exactness of comparison direct image is assumed.
-/
theorem comparisonUpperStar_reflects_local_torsion (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F)).IsTorsion) :
    Scheme.IsTorsionModuleSheaf F := by
  rw [Scheme.isTorsionModuleSheaf_iff_isTorsion]
  apply Sheaf.IsTorsion.of_isAddTorsion_sheafFiber
    (Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale X)
  rintro ⟨-, ⟨x⟩⟩
  let t := X.algClosurePoint x
  obtain ⟨c⟩ := torsion_comparison_stalkIso t (ModuleCat.{u + 1} A) _
    (comparisonAdjunction (ModuleCat.{u + 1} A) X)
  have hm : IsAddTorsion
      (((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj F) :=
    IsAddTorsion.of_surjective (f := (c.hom.app F).hom.toAddMonoidHom)
      (ConcreteCategory.bijective_of_isIso (c.hom.app F)).2
      (stalkTorsion X _ t A _ hF)
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let e := ((Scheme.pointSmallEtale t).sheafFiberCompIso
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).app F
  have ha : IsAddTorsion (((Scheme.pointSmallEtale t).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F)) :=
    IsAddTorsion.of_surjective (f := e.inv.hom)
      (ConcreteCategory.bijective_of_isIso _).2 hm
  exact IsAddTorsion.of_surjective
    (f := ((((Scheme.pointSmallEtale t).uliftSheafFiberIso
      AddCommGrpCat.{u + 1}).app _).inv).hom)
    (ConcreteCategory.bijective_of_isIso _).2 ha

end AlgebraicGeometry.ProEtale
