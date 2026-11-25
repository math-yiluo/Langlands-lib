/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category
import WeilConjectures.Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.TypeValuedFlat

/-!
# Geometric stalks commute with pro-etale inverse image

The germ equation characterizes the canonical comparison: the germ of the adjunction
unit at the pulled-back pointed neighbourhood maps to the original germ. Naturality
and reflection of equality at image geometric points are stated in both coefficient cases.

## References

* Stacks Project, Tags 05V1, 0F4F, 0F6B, 0F6C and 0993
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem inverseImage_cover_lift
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {V : T.ProEt} (R : Sieve V) (hR : R ∈ ProEt.topology T V)
    (v : Spec (.of Ω) ⟶ V.left) :
    ∃ (W : T.ProEt) (g : W ⟶ V) (_ : R g) (w : Spec (.of Ω) ⟶ W.left),
      w ≫ g.left = v := by
  obtain ⟨S, hS, hSR⟩ := ProEt.mem_topology_iff.1 hR
  obtain ⟨ι, Z, f, rfl⟩ := S.exists_eq_ofArrows
  have hS' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage V.left := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst] using hS
  have hb := Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hS' v
    (fun i ↦ pullback.snd (f i).left v) (fun i ↦ pullback.fst (f i).left v)
    (fun i ↦ (IsPullback.of_hasPullback (f i).left v).flip)
  obtain ⟨i, z, _⟩ :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hb)).1
      (IsLocalRing.closedPoint Ω)
  have : WeaklyEtale (f i).left :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hS')).2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd (f i).left v) z
  refine ⟨Z i, f i, hSR _ _ ⟨i⟩, σ ≫ pullback.fst (f i).left v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

private noncomputable def inverseImagePoint
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) : (ProEt.topology T).Point.{u + 1} where
  fiber := (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))) ⋙ uliftFunctor.{u + 1}
  isCofiltered := by
    have : IsCofiltered (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))).Elements :=
      Functor.isCofiltered_elements _
    exact .of_equivalence
      (Functor.Elements.uliftEquivalence.{u + 1}
        (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t)))).symm
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR x := by
    obtain ⟨W, g, hg, w, hw⟩ := inverseImage_cover_lift R hR x.down.left
    refine ⟨W, g, hg, ULift.up (Over.homMk w ?_), ?_⟩
    · change w ≫ W.hom = t
      rw [← MorphismProperty.Over.w g, ← Category.assoc, hw]
      exact Over.w x.down
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hw

private noncomputable def inverseImagePointElements
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    ProEtaleGeometricNeighbourhood t ≌ (inverseImagePoint t).fiber.Elements where
  functor.obj n := Functor.elementsMk _ n.right (ULift.up n.hom)
  functor.map f := ⟨f.right, congrArg ULift.up f.w⟩
  inverse.obj n := StructuredArrow.mk n.2.down
  inverse.map f := StructuredArrow.homMk f.1 (congrArg ULift.down f.2)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

private noncomputable def inverseImagePointStalkIso
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] :
    sheafToPresheaf (ProEt.topology T) A ⋙
      (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ A).obj
        (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim ≅
      (inverseImagePoint t).sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf (ProEt.topology T) A)
    (Functor.isoWhiskerLeft
      ((Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π
        (inverseImagePoint t).fiber).op)
      (Functor.Final.colimIso (inverseImagePointElements t).functor.op))

@[reassoc]
private theorem inverseImagePointStalkIso_germ
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u + 1, u + 1} A]
    (H : Sheaf (ProEt.topology T) A) (U : T.ProEt)
    (x : Over.mk t ⟶ (ProEt.forget T).obj U) :
    colimit.ι (proEtaleGeometricStalkDiagram t H) (op (StructuredArrow.mk x)) ≫
        (inverseImagePointStalkIso t A).hom.app H =
      (inverseImagePoint t).toPresheafFiber U (ULift.up x) H.obj := by
  exact Functor.Final.ι_colimitIso_hom (inverseImagePointElements t).functor.op
    ((Functor.Elements.π (inverseImagePoint t).fiber).op ⋙ H.obj)
    (op (StructuredArrow.mk x))

private noncomputable def inverseImagePointFiberIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    proEtaleBaseChange f ⋙ (inverseImagePoint x).fiber ≅
      (inverseImagePoint (x ≫ f)).fiber :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (ProEt.forget Y)
      ((Adjunction.compCoyonedaIso (Over.mapPullbackAdj f)).app
        (op (Over.mk x))).symm) uliftFunctor

set_option backward.isDefEq.respectTransparency false in
private theorem inverseImage_stalk_generic
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (A : Type v) [Category.{u + 1} A] [HasColimitsOfSize.{u + 1, u + 1} A]
    [HasProducts.{u + 1} A] [HasWeakSheafify (ProEt.topology X) A] :
    ∃ c : ∀ F : Sheaf (ProEt.topology Y) A,
      proEtaleGeometricStalk x ((proEtaleSheafInverseImage f A).obj F) ≅
        proEtaleGeometricStalk (x ≫ f) F,
      (∀ (F : Sheaf (ProEt.topology Y) A)
        (N : ProEtaleGeometricNeighbourhood (x ≫ f))
        (a : Over.mk x ⟶ (ProEt.forget X).obj ((proEtaleBaseChange f).obj N.right)),
        a.left ≫ pullback.fst N.right.hom f = N.hom.left →
        ((proEtaleSheafAdjunction f A).unit.app F).hom.app (op N.right) ≫
          colimit.ι (proEtaleGeometricStalkDiagram x
            ((proEtaleSheafInverseImage f A).obj F))
              (op (StructuredArrow.mk a)) ≫ (c F).hom =
        colimit.ι (proEtaleGeometricStalkDiagram (x ≫ f) F) (op N)) ∧
      (∀ (F G : Sheaf (ProEt.topology Y) A) (h : F ⟶ G),
        colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
          ((proEtaleSheafInverseImage f A).map h).hom) ≫ (c G).hom =
        (c F).hom ≫ colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom)) ∧
      (∀ (F G : Sheaf (ProEt.topology Y) A) (h k : F ⟶ G),
        (proEtaleSheafInverseImage f A).map h =
          (proEtaleSheafInverseImage f A).map k →
        colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom) =
        colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op k.hom)) := by
  have : RepresentablyFlat (proEtaleBaseChange f) :=
    flat_of_preservesFiniteLimits _
  let Φ := inverseImagePoint x
  let hF := proEtaleBaseChangeCoverPreserving f
  let adj := proEtaleSheafAdjunction f A
  let := adj.isRightAdjoint
  let a := (proEtaleBaseChange f).sheafAdjunctionContinuous A
    (ProEt.topology Y) (ProEt.topology X)
  let e := adj.leftAdjointUniq a
  have : InitiallySmall.{u + 1} (proEtaleBaseChange f ⋙ Φ.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (NatIso.mapElements (inverseImagePointFiberIso f x).symm).functor
  let p : Φ.comap (proEtaleBaseChange f) hF ≅ inverseImagePoint (x ≫ f) :=
    GrothendieckTopology.Point.isoMk (inverseImagePointFiberIso f x)
  let b := Φ.sheafFiberComapIso (proEtaleBaseChange f) hF A
  let c := Functor.isoWhiskerLeft (proEtaleSheafInverseImage f A)
      (inverseImagePointStalkIso x A) ≪≫
    Functor.isoWhiskerRight e Φ.sheafFiber ≪≫ b.symm ≪≫
    GrothendieckTopology.Point.sheafFiberIso p ≪≫
    (inverseImagePointStalkIso (x ≫ f) A).symm
  have hc (F G : Sheaf (ProEt.topology Y) A) (h : F ⟶ G) :
      colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
        ((proEtaleSheafInverseImage f A).map h).hom) ≫ (c.app G).hom =
      (c.app F).hom ≫ colim.map
        (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom) :=
    c.hom.naturality h
  refine ⟨fun F ↦ c.app F, ?_, hc, ?_⟩
  · intro F N z hz
    have hu : (adj.unit.app F).hom.app (op N.right) ≫
        (e.hom.app F).hom.app (op ((proEtaleBaseChange f).obj N.right)) =
        (a.unit.app F).hom.app (op N.right) :=
      NatTrans.congr_app (Sheaf.hom_ext_iff.1
        (Adjunction.unit_leftAdjointUniq_hom_app adj a F)) (op N.right)
    have hg := Φ.toPresheafFiber_sheafFiberComapIso_hom_app
      (proEtaleBaseChange f) hF A F N.right (ULift.up z)
    have hg' : (a.unit.app F).hom.app (op N.right) ≫
        Φ.toPresheafFiber ((proEtaleBaseChange f).obj N.right) (ULift.up z)
          (((proEtaleBaseChange f).sheafPullback A
            (ProEt.topology Y) (ProEt.topology X)).obj F).obj ≫ b.inv.app F =
        (Φ.comap (proEtaleBaseChange f) hF).toPresheafFiber N.right (ULift.up z) F.obj := by
      rw [← Category.assoc, ← hg, Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _
    have hz' : (inverseImagePointFiberIso f x).hom.app N.right (ULift.up z) =
        ULift.up N.hom := by
      apply ULift.ext
      apply Over.OverMorphism.ext
      exact hz
    simp only [c, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [inverseImagePointStalkIso_germ_assoc]
    rw [show Φ.sheafFiber.map (e.hom.app F) =
      Φ.presheafFiber.map (e.hom.app F).hom from rfl]
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
    rw [← Category.assoc, hu]
    have ht : (Φ.comap (proEtaleBaseChange f) hF).toPresheafFiber N.right
        (ULift.up z) F.obj ≫
        (GrothendieckTopology.Point.sheafFiberIso p).hom.app F =
        (inverseImagePoint (x ≫ f)).toPresheafFiber N.right (ULift.up N.hom) F.obj := by
      have h := GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app
        p.symm F N.right (ULift.up z)
      change _ ≫ (GrothendieckTopology.Point.sheafFiberIso p).hom.app F =
        (inverseImagePoint (x ≫ f)).toPresheafFiber N.right
          ((inverseImagePointFiberIso f x).hom.app N.right (ULift.up z)) F.obj at h
      rw [hz'] at h
      exact h
    calc
      _ = (Φ.comap (proEtaleBaseChange f) hF).toPresheafFiber N.right
          (ULift.up z) F.obj ≫
          (GrothendieckTopology.Point.sheafFiberIso p).hom.app F ≫
          (inverseImagePointStalkIso (x ≫ f) A).inv.app F := by
        simpa only [Category.assoc] using congrArg
          (fun q ↦ q ≫ (GrothendieckTopology.Point.sheafFiberIso p).hom.app F ≫
            (inverseImagePointStalkIso (x ≫ f) A).inv.app F) hg'
      _ = _ := by
        rw [← Category.assoc, ht]
        rw [← inverseImagePointStalkIso_germ, Category.assoc, Iso.hom_inv_id_app]
        change colimit.ι (proEtaleGeometricStalkDiagram (x ≫ f) F) (op N) ≫ 𝟙 _ = _
        exact Category.comp_id _
  · intro F G h k hhk
    apply (cancel_epi (c.app F).hom).1
    rw [← hc F G h, ← hc F G k, hhk]

/-- Geometric stalks of abelian sheaves commute with inverse image along every scheme morphism.
The first clause fixes the canonical comparison by its value on unit germs; the
second is naturality in the sheaf; the third reflects equality of inverse-image maps
at the image geometric point. The comparison is additive since it is an isomorphism
in `AddCommGrpCat`.
-/
theorem proEtaleInverseImage_abelianStalk
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ c : ∀ F : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1},
      proEtaleGeometricStalk x ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj F) ≅
        proEtaleGeometricStalk (x ≫ f) F,
      (∀ (F : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1})
        (N : ProEtaleGeometricNeighbourhood (x ≫ f))
        (a : Over.mk x ⟶ (ProEt.forget X).obj ((proEtaleBaseChange f).obj N.right)),
        a.left ≫ pullback.fst N.right.hom f = N.hom.left →
        ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app F).hom.app (op N.right) ≫
          colimit.ι (proEtaleGeometricStalkDiagram x
            ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj F))
              (op (StructuredArrow.mk a)) ≫ (c F).hom =
        colimit.ι (proEtaleGeometricStalkDiagram (x ≫ f) F) (op N)) ∧
      (∀ (F G : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}) (h : F ⟶ G),
        colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
          ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map h).hom) ≫ (c G).hom =
        (c F).hom ≫ colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom)) ∧
      (∀ (F G : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}) (h k : F ⟶ G),
        (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map h =
          (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map k →
        colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom) =
        colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op k.hom)) := by
  exact inverseImage_stalk_generic f x AddCommGrpCat.{u + 1}

end AlgebraicGeometry.Scheme
