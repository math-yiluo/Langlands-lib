/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleInverseImageStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSheafificationGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability

/-!
# Coherence of pro-etale pullback stalk comparisons

## References

* Stacks Tags 0F4F and 0993
* Stacks Tags 0F6B and 0F4F
* Stacks Tags 05V1 and 09A5
* Stacks Tag 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable instance (priority := 10000) fixedAbelianStalkSite (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} _

/-- The stalk functor on cochain complexes, obtained term by term from the
finite-coefficient geometric stalk. -/
noncomputable def proEtaleFiniteCoefficientStalkComplexFunctor
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (u : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A] :
    CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ℤ :=
  (finiteCoefficientModuleStalkFunctor u A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual additive colimit coprojection, viewed in the stalk with constant scalars. -/
def proEtaleCoefficientModuleGerm {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)) :
    (finiteCoefficientModuleStalkFunctor x A).obj M :=
  (colimit.ι ((proEtaleGeometricNeighbourhoodForget x).op ⋙ M.val.presheaf) (op N)) a

/-- Both representative formulas defining the canonical comparison. The first quantifies
all comma representatives `(P, theta, a)`; the equality of lifts says that `N` is their
projected pointed neighbourhood. The second is the inverse formula on unit germs. -/
def ProEtalePullbackStalkGermNormalized (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (c : proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A) : Prop :=
  (∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (N : ProEtaleGeometricNeighbourhood (x ≫ t))
    (P : ProEtaleGeometricNeighbourhood x)
    (θ : P.right ⟶ (proEtaleBaseChange t).obj N.right)
    (a : M.val.obj (op N.right)),
    P.hom.left ≫ θ.left ≫ pullback.fst N.right.hom t = N.hom.left →
    c.hom.app M (proEtaleCoefficientModuleGerm x A
      ((proEtaleConstantRingPullback A t).obj M) P
      (((proEtaleConstantRingPullback A t).obj M).val.map θ.op
        (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a))) =
      proEtaleCoefficientModuleGerm (x ≫ t) A M N a) ∧
  (∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (N : ProEtaleGeometricNeighbourhood (x ≫ t))
    (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
    (a : M.val.obj (op N.right)),
    l.left ≫ pullback.fst N.right.hom t = N.hom.left →
    c.inv.app M (proEtaleCoefficientModuleGerm (x ≫ t) A M N a) =
      proEtaleCoefficientModuleGerm x A ((proEtaleConstantRingPullback A t).obj M)
        (StructuredArrow.mk l)
        (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a))

private theorem stalkOfUnitComparison {T S : Scheme.{u}} (t : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (F : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})
    (G : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1})
    (g : F ⟶ (proEtaleSheafDirectImage t AddCommGrpCat.{u + 1}).obj G)
    [IsIso (((proEtaleSheafAdjunction t AddCommGrpCat.{u + 1}).homEquiv F G).symm g)] :
    ∃ d : proEtaleGeometricStalk x G ≅ proEtaleGeometricStalk (x ≫ t) F,
      ∀ (N : ProEtaleGeometricNeighbourhood (x ≫ t))
        (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right)),
        l.left ≫ pullback.fst N.right.hom t = N.hom.left →
        g.hom.app (op N.right) ≫ colimit.ι (proEtaleGeometricStalkDiagram x G)
          (op (StructuredArrow.mk l)) ≫ d.hom =
            colimit.ι (proEtaleGeometricStalkDiagram (x ≫ t) F) (op N) := by
  let a := proEtaleSheafAdjunction t AddCommGrpCat.{u + 1}
  let b := (a.homEquiv F G).symm g
  let SX : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood x)ᵒᵖ T.ProEtᵒᵖ
        AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget x).op ⋙ colim
  obtain ⟨c, hc, _, _⟩ := proEtaleInverseImage_abelianStalk t x
  let d := SX.mapIso (asIso b).symm ≪≫ c F
  refine ⟨d, ?_⟩
  intro N l hl
  have hb := (a.homEquiv F G).apply_symm_apply g
  rw [Adjunction.homEquiv_unit] at hb
  have hu : g ≫ (proEtaleSheafDirectImage t AddCommGrpCat.{u + 1}).map (inv b) =
      a.unit.app F := by
    rw [← hb, Category.assoc, ← CategoryTheory.Functor.map_comp,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hu' := congrArg (fun q ↦ q.hom.app (op N.right)) hu
  change g.hom.app (op N.right) ≫
    (inv b).hom.app (op ((proEtaleBaseChange t).obj N.right)) = _ at hu'
  change g.hom.app (op N.right) ≫ colimit.ι (proEtaleGeometricStalkDiagram x G)
    (op (StructuredArrow.mk l)) ≫
    colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op (inv b).hom) ≫
    (c F).hom = _
  rw [colimit.ι_map_assoc]
  change g.hom.app (op N.right) ≫
    (inv b).hom.app (op ((proEtaleBaseChange t).obj N.right)) ≫
    colimit.ι (proEtaleGeometricStalkDiagram x
      ((proEtaleSheafInverseImage t AddCommGrpCat.{u + 1}).obj F))
      (op (StructuredArrow.mk l)) ≫ (c F).hom = _
  rw [← Category.assoc, hu']
  exact hc F N l hl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackStalkAdditive (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    ∃ d : ∀ M : proEtaleRingModules S (proEtaleConstantRing S A),
      AddCommGrpCat.of ((finiteCoefficientModuleStalkFunctor x A).obj
        ((proEtaleConstantRingPullback A t).obj M)) ≅
      AddCommGrpCat.of ((finiteCoefficientModuleStalkFunctor (x ≫ t) A).obj M),
      ∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
        (N : ProEtaleGeometricNeighbourhood (x ≫ t))
        (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
        (a : M.val.obj (op N.right)),
        l.left ≫ pullback.fst N.right.hom t = N.hom.left →
        (d M).hom (proEtaleCoefficientModuleGerm x A
          ((proEtaleConstantRingPullback A t).obj M) (StructuredArrow.mk l)
          (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a)) =
          proEtaleCoefficientModuleGerm (x ≫ t) A M N a := by
  let R : Sheaf (ProEt.topology S) RingCat.{u + 1} :=
    (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  let B : Sheaf (ProEt.topology T) RingCat.{u + 1} :=
    (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A)
  let P := SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} R
  let Q := SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} B
  let L := proEtaleConstantRingPullback A t
  let adj := proEtaleConstantRingAdjunction A t
  let a := proEtaleSheafAdjunction t AddCommGrpCat.{u + 1}
  let b (M : proEtaleRingModules S (proEtaleConstantRing S A)) :=
    (a.homEquiv (P.obj M) (Q.obj (L.obj M))).symm (P.map (adj.unit.app M))
  have (M : proEtaleRingModules S (proEtaleConstantRing S A)) : IsIso (b M) :=
    proEtaleConstantRingPullback_underlyingUnit_isIso A t M
  have h (M : proEtaleRingModules S (proEtaleConstantRing S A)) :=
    stalkOfUnitComparison t x (P.obj M) (Q.obj (L.obj M)) (P.map (adj.unit.app M))
  choose d hd using h
  refine ⟨d, ?_⟩
  intro M N l z hl
  exact ConcreteCategory.congr_hom (hd M N l hl) z

private def pairedLift {T S : Scheme.{u}} (t : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (N : ProEtaleGeometricNeighbourhood (x ≫ t)) :
    Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right) :=
  Over.homMk (pullback.lift N.hom.left x (Over.w N.hom)) (by exact pullback.lift_snd _ _ _)
private theorem pairedLift_fst {T S : Scheme.{u}} (t : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (N : ProEtaleGeometricNeighbourhood (x ≫ t)) :
    (pairedLift t x N).left ≫ pullback.fst N.right.hom t = N.hom.left := by
  exact pullback.lift_fst _ _ _
private theorem coefficientGerm_restriction {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    {P Q : ProEtaleGeometricNeighbourhood x} (f : P ⟶ Q)
    (z : M.val.obj (op Q.right)) :
    proEtaleCoefficientModuleGerm x A M P (M.val.map f.right.op z) =
      proEtaleCoefficientModuleGerm x A M Q z :=
  ConcreteCategory.congr_hom
    (colimit.w ((proEtaleGeometricNeighbourhoodForget x).op ⋙ M.val.presheaf) f.op) z
private theorem unitConstant_smul (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S)
    (M : proEtaleRingModules S (proEtaleConstantRing S A)) (V : S.ProEt)
    (r : ULift.{u + 1, u} A) (z : M.val.obj (op V)) :
    (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op V))
      (((toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op V)) r • z) =
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op ((proEtaleBaseChange t).obj V))) r •
        (show ((proEtaleConstantRingPullback A t).obj M).val.obj
          (op ((proEtaleBaseChange t).obj V)) from
            ((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op V) z) := by
  let C := CommRingCat.of (ULift.{u + 1, u} A)
  have hr : proEtaleRingDirectImageMap t (proEtaleConstantRing S A)
      (proEtaleConstantRing T A) (proEtaleConstantRingComparison t A) =
      proEtaleCoefficientDirectImageMap t A :=
    ((proEtaleSheafAdjunction t CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hη : toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj C) ≫
      (proEtaleCoefficientDirectImageMap t A).hom =
      Functor.whiskerLeft (proEtaleBaseChange t).op
        (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj C)) := by
    exact ((sheafificationAdjunction (ProEt.topology S) CommRingCat.{u + 1}).homEquiv
      _ _).apply_symm_apply _
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hη (op V)) r
  have hu := (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op V)).hom.map_smul
    (((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj C)).app (op V)) r) z
  change _ =
    ((proEtaleRingDirectImageMap t (proEtaleConstantRing S A) (proEtaleConstantRing T A)
      (proEtaleConstantRingComparison t A)).hom.app (op V))
        (((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj C)).app (op V)) r) •
      (show ((proEtaleConstantRingPullback A t).obj M).val.obj
        (op ((proEtaleBaseChange t).obj V)) from
          ((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op V) z) at hu
  change (proEtaleCoefficientDirectImageMap t A).hom.app (op V)
    (((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj C)).app (op V)) r) =
      ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj C)).app
        (op ((proEtaleBaseChange t).obj V))) r at h
  rw [hr] at hu
  erw [h] at hu
  exact hu

private theorem coefficientGerm_smul
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (r : ULift.{u + 1, u} A)
    (a : M.val.obj (op N.right)) :
    proEtaleCoefficientModuleGerm x A M N
      (((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op N.right)) r • a) =
      r • proEtaleCoefficientModuleGerm x A M N a := by
  let O := proEtaleConstantRing T A
  let R := proEtaleGeometricStalkRingDiagram x O
  let SM := (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget x)
    (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj M.val
  let f : N ⟶ proEtaleConstantGermNeighbourhood x :=
    StructuredArrow.homMk (MorphismProperty.Over.homMk N.right.hom) (by
      apply Over.OverMorphism.ext
      exact Over.w N.hom)
  let η := toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
  have hη : O.obj.map f.right.op (η.app (op (ProEt.mk (𝟙 T))) r) =
      η.app (op N.right) r := by
    have h := ConcreteCategory.congr_hom (η.naturality f.right.op) r
    exact h.symm
  have hr : proEtaleConstantRingGerm x A r =
      colimit.ι R (op N) (η.app (op N.right) r) := by
    have h := ConcreteCategory.congr_hom (colimit.w R f.op)
      (η.app (op (ProEt.mk (𝟙 T))) r)
    change colimit.ι R (op N)
      (O.obj.map f.right.op (η.app (op (ProEt.mk (𝟙 T))) r)) = _ at h
    rw [hη] at h
    exact h.symm
  have hsmul := (PresheafOfModules.ModuleColimit.smul_eq
    (colimit.isColimit R) (colimit.isColimit SM.presheaf)
      (U := op N) (η.app (op N.right) r) a).symm
  have hr' : PresheafOfModules.ModuleColimit.ιR (colimit.cocone R)
      (η.app (op N.right) r) = proEtaleConstantRingGerm x A r := hr.symm
  rw [hr'] at hsmul
  exact hsmul

private theorem pullbackStalkInverseLinear (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    ∃ e : ∀ M : proEtaleRingModules S (proEtaleConstantRing S A),
      (finiteCoefficientModuleStalkFunctor (x ≫ t) A).obj M ≅
        (finiteCoefficientModuleStalkFunctor x A).obj ((proEtaleConstantRingPullback A t).obj M),
      ∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
        (N : ProEtaleGeometricNeighbourhood (x ≫ t))
        (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
        (a : M.val.obj (op N.right)),
        l.left ≫ pullback.fst N.right.hom t = N.hom.left →
        (e M).hom (proEtaleCoefficientModuleGerm (x ≫ t) A M N a) =
          proEtaleCoefficientModuleGerm x A
            ((proEtaleConstantRingPullback A t).obj M) (StructuredArrow.mk l)
            (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a) := by
  obtain ⟨d, hd⟩ := pullbackStalkAdditive A t x
  have hi (M : proEtaleRingModules S (proEtaleConstantRing S A))
      (N : ProEtaleGeometricNeighbourhood (x ≫ t))
      (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
      (a : M.val.obj (op N.right))
      (hl : l.left ≫ pullback.fst N.right.hom t = N.hom.left) :
      (d M).inv (proEtaleCoefficientModuleGerm (x ≫ t) A M N a) =
        proEtaleCoefficientModuleGerm x A
          ((proEtaleConstantRingPullback A t).obj M) (StructuredArrow.mk l)
          (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a) := by
    apply (d M).addCommGroupIsoToAddEquiv.injective
    change (d M).hom ((d M).inv _) = (d M).hom _
    rw [Iso.inv_hom_id_apply, hd M N l a hl]
  let e (M : proEtaleRingModules S (proEtaleConstantRing S A)) :
      (finiteCoefficientModuleStalkFunctor (x ≫ t) A).obj M ≅
        (finiteCoefficientModuleStalkFunctor x A).obj ((proEtaleConstantRingPullback A t).obj M) :=
    LinearEquiv.toModuleIso
      (X₁ := (finiteCoefficientModuleStalkFunctor (x ≫ t) A).obj M)
      (X₂ := (finiteCoefficientModuleStalkFunctor x A).obj
        ((proEtaleConstantRingPullback A t).obj M))
      { __ := (d M).symm.addCommGroupIsoToAddEquiv
        map_smul' := by
          intro r z
          let R := proEtaleGeometricStalkRingDiagram (x ≫ t) (proEtaleConstantRing S A)
          let SM := (PresheafOfModules.pushforward₀
            (proEtaleGeometricNeighbourhoodForget (x ≫ t))
            ((proEtaleConstantRing S A).obj ⋙
              forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj M.val
          obtain ⟨N, a, rfl⟩ := PresheafOfModules.ModuleColimit.ιM_jointly_surjective
            (hcR := colimit.isColimit R) (hcM := colimit.isColimit SM.presheaf) z
          change (d M).inv (r • proEtaleCoefficientModuleGerm (x ≫ t) A M N.unop a) =
            r • (d M).inv (proEtaleCoefficientModuleGerm (x ≫ t) A M N.unop a)
          rw [← coefficientGerm_smul,
            hi M N.unop (pairedLift t x N.unop) _ (pairedLift_fst t x N.unop),
            hi M N.unop (pairedLift t x N.unop) _ (pairedLift_fst t x N.unop),
            unitConstant_smul]
          exact coefficientGerm_smul x A _ _ r _ }
  exact ⟨e, hi⟩

/-- The normalized comparison exists uniquely; this fixes its data before any coherence
assertion. -/
theorem proEtalePullbackStalkComparison_existsUnique (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    ∃! c : proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A,
      ProEtalePullbackStalkGermNormalized A t x c := by
  obtain ⟨e, he⟩ := pullbackStalkInverseLinear A t x
  let η : finiteCoefficientModuleStalkFunctor (x ≫ t) A ⟶
      proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A :=
    { app := fun M ↦ (e M).hom
      naturality := by
        intro M Q f
        apply (forget₂ (ModuleCat (ULift.{u + 1, u} A)) AddCommGrpCat).map_injective
        apply colimit.hom_ext
        intro N
        ext a
        have hf (y : Spec (.of Ω) ⟶ S) (P : ProEtaleGeometricNeighbourhood y)
            (a : M.val.obj (op P.right)) :
            (finiteCoefficientModuleStalkFunctor y A).map f
              (proEtaleCoefficientModuleGerm y A M P a) =
            proEtaleCoefficientModuleGerm y A Q P (f.val.app (op P.right) a) := by
          exact ConcreteCategory.congr_hom
            (colimit.ι_map (Functor.whiskerLeft
              (proEtaleGeometricNeighbourhoodForget y).op
              ((SheafOfModules.toSheaf _).map f).hom) (op P)) a
        change (e Q).hom ((finiteCoefficientModuleStalkFunctor (x ≫ t) A).map f
            (proEtaleCoefficientModuleGerm (x ≫ t) A M N.unop a)) =
          (finiteCoefficientModuleStalkFunctor x A).map
            ((proEtaleConstantRingPullback A t).map f)
            ((e M).hom (proEtaleCoefficientModuleGerm (x ≫ t) A M N.unop a))
        rw [hf, he Q N.unop (pairedLift t x N.unop) _ (pairedLift_fst t x N.unop),
          he M N.unop (pairedLift t x N.unop) _ (pairedLift_fst t x N.unop)]
        have hmap := ConcreteCategory.congr_hom
          (colimit.ι_map (Functor.whiskerLeft
            (proEtaleGeometricNeighbourhoodForget x).op
            ((SheafOfModules.toSheaf _).map ((proEtaleConstantRingPullback A t).map f)).hom)
            (op (StructuredArrow.mk (pairedLift t x N.unop))))
              (((proEtaleConstantRingAdjunction A t).unit.app M).val.app
                (op N.unop.right) a)
        rw [show (finiteCoefficientModuleStalkFunctor x A).map
            ((proEtaleConstantRingPullback A t).map f)
            (proEtaleCoefficientModuleGerm x A _ (StructuredArrow.mk (pairedLift t x N.unop))
              (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.unop.right) a)) =
            proEtaleCoefficientModuleGerm x A _ (StructuredArrow.mk (pairedLift t x N.unop))
              ((((proEtaleConstantRingPullback A t).map f).val.app
                (op ((proEtaleBaseChange t).obj N.unop.right)))
                (((proEtaleConstantRingAdjunction A t).unit.app M).val.app
                  (op N.unop.right) a)) from hmap]
        congr 1
        exact congrArg (fun q ↦ q.val.app (op N.unop.right) a)
          ((proEtaleConstantRingAdjunction A t).unit.naturality f) }
  have : IsIso η := NatIso.isIso_of_isIso_app η
  let c := (asIso η).symm
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro M N P θ a hθ
    let l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right) :=
      P.hom ≫ (ProEt.forget T).map θ
    have hl : l.left ≫ pullback.fst N.right.hom t = N.hom.left := hθ
    let q : P ⟶ StructuredArrow.mk l := StructuredArrow.homMk θ rfl
    have hr := coefficientGerm_restriction x A
      ((proEtaleConstantRingPullback A t).obj M) q
      (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a)
    change proEtaleCoefficientModuleGerm x A _ P
      (((proEtaleConstantRingPullback A t).obj M).val.map θ.op
        (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a)) =
        proEtaleCoefficientModuleGerm x A _ (StructuredArrow.mk l)
          (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a) at hr
    apply (ConcreteCategory.bijective_of_isIso (c.inv.app M)).1
    change (c.inv.app M) ((c.hom.app M) _) = (e M).hom _
    rw [← ModuleCat.comp_apply, c.hom_inv_id_app]
    exact hr.trans (he M N l a hl).symm
  · exact he
  · intro c' hc'
    apply Iso.ext_inv
    apply NatTrans.ext
    funext M
    apply (forget₂ (ModuleCat (ULift.{u + 1, u} A)) AddCommGrpCat).map_injective
    apply colimit.hom_ext
    intro N
    ext a
    exact (hc'.2 M N.unop (pairedLift t x N.unop) a (pairedLift_fst t x N.unop)).trans
      (he M N.unop (pairedLift t x N.unop) a (pairedLift_fst t x N.unop)).symm

/-- The unique comparison specified on all represented germs, not a choice of an
unnormalized isomorphism. -/
def proEtalePullbackStalkComparison (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A :=
  (proEtalePullbackStalkComparison_existsUnique A t x).exists.choose

private theorem identityCoefficientMap (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleCoefficientDirectImageMap (𝟙 T) A ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv
          CommRingCat.{u + 1} (ProEt.topology T) (ProEt.topology T)).app
            (proEtaleConstantRing T A) = 𝟙 _ := by
  let B := CommRingCat.of (ULift.{u + 1, u} A)
  apply ((sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    ((Functor.const T.ProEtᵒᵖ).obj B) _).injective
  rw [Adjunction.homEquiv_naturality_right]
  change (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv _ _
      (((sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv
        _ _).symm _) ≫ _ = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext V
  have h := (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj B)).naturality
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app V.unop).op
  change 𝟙 B ≫ _ = _ at h
  rw [Category.id_comp] at h
  exact h.symm

@[irreducible] private noncomputable def identityDirect (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingPushforward A (𝟙 T) ≅
      𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)) := by
  let R := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A)
  have hr : proEtaleRingDirectImageMap (𝟙 T) (proEtaleConstantRing T A)
      (proEtaleConstantRing T A) (proEtaleConstantRingComparison (𝟙 T) A) =
      proEtaleCoefficientDirectImageMap (𝟙 T) A :=
    ((proEtaleSheafAdjunction (𝟙 T) CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  let ρ : R ⟶ ((proEtaleBaseChange (𝟙 T)).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology T) (ProEt.topology T)).obj R :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap (𝟙 T) (proEtaleConstantRing T A)
      (proEtaleConstantRing T A) (proEtaleConstantRingComparison (𝟙 T) A)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have hρ : ρ ≫ (Functor.sheafPushforwardContinuousNatTrans
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv RingCat.{u + 1}
      (ProEt.topology T) (ProEt.topology T)).app R = 𝟙 R := by
    dsimp only [ρ]
    rw [hr]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact congrArg (fun q ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (q.hom.app V)) (identityCoefficientMap A T)
  let : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ T)).IsContinuous
      (ProEt.topology T) (ProEt.topology T) :=
    Functor.isContinuous_id _
  change SheafOfModules.pushforward ρ ≅ _
  letI hi : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ T)).IsContinuous
      (ProEt.topology T) (ProEt.topology T) := Functor.isContinuous_id _
  exact SheafOfModules.pushforwardNatIso ρ
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).symm ≪≫
    SheafOfModules.pushforwardCongr hρ ≪≫ SheafOfModules.pushforwardId R

private theorem identityDirect_hom (A : Type u) [CommRing A] (T : Scheme.{u})
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) (V : T.ProEt)
    (a : ((proEtaleConstantRingPushforward A (𝟙 T)).obj M).val.obj (op V)) :
    ((identityDirect A T).hom.app M).val.app (op V) a =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app V).op a := by
  unfold identityDirect
  rfl

/-- The identity-pullback comparison is uniquely fixed by its inverse, the unit
followed by restriction along the diagonal. -/
theorem proEtaleStalkIdentityPullback_existsUnique (A : Type u) [CommRing A]
    (T : Scheme.{u}) :
    ∃! e : proEtaleConstantRingPullback A (𝟙 T) ≅
      𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)),
      ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A)) (V : T.ProEt)
        (a : M.val.obj (op V)),
        (e.inv.app M).val.app (op V) a =
          ((proEtaleConstantRingPullback A (𝟙 T)).obj M).val.map
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app V).op
            (((proEtaleConstantRingAdjunction A (𝟙 T)).unit.app M).val.app (op V) a) := by
  let adj := (proEtaleConstantRingAdjunction A (𝟙 T)).ofNatIsoRight (identityDirect A T)
  let e := adj.leftAdjointUniq Adjunction.id
  have he (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
      e.inv.app M = adj.unit.app M := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app Adjunction.id adj M
    exact h
  refine ⟨e, ?_, ?_⟩
  · intro M V a
    rw [he]
    change ((identityDirect A T).hom.app _).val.app (op V)
      (((proEtaleConstantRingAdjunction A (𝟙 T)).unit.app M).val.app (op V) a) = _
    exact identityDirect_hom A T _ V _
  · intro e' he'
    apply Iso.ext_inv
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext a
    exact (he' M V.unop a).trans (by
      rw [he]
      exact (identityDirect_hom A T _ V.unop _).symm)

/-- The canonical identity-pullback isomorphism with its diagonal-unit normalization. -/
def proEtaleStalkIdentityPullback (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingPullback A (𝟙 T) ≅
      𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)) :=
  (proEtaleStalkIdentityPullback_existsUnique A T).exists.choose

/-- The canonical identity comparison descended termwise, including the localization
identity unitor. -/
def proEtaleStalkDerivedIdentityPullback (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingDerivedPullback A (𝟙 T) ≅ 𝟭 (proEtaleDerivedCategory T A) :=
  Functor.mapDerivedCategoryNatIso (proEtaleStalkIdentityPullback A T) ≪≫
    Functor.mapDerivedCategoryIdIso _

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleConstantRingComparison
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem cancel_mapped_iso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N : C} (e : M ≅ N) {P : D} {a b : F.obj N ⟶ P}
    (h : F.map e.hom ≫ a = F.map e.hom ≫ b) : a = b :=
  (cancel_epi (F.map e.hom)).mp h

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] finiteCoefficientModuleStalkFunctor
  geometricRingModuleStalkFunctor Functor.mapDerivedCategory
  proEtaleCanonicalPullbackComposition
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem descend_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G G' : D ⥤ E) (J J' : C ⥤ E)
    [F.Additive] [G.Additive] [G'.Additive] [J.Additive] [J'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (c : F ⋙ G ≅ J) (c' : F ⋙ G' ≅ J') (r : G ≅ G') (q : J ≅ J')
    (hc : ∀ M, c.hom.app M ≫ q.hom.app M = r.hom.app (F.obj M) ≫ c'.hom.app M)
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompNatIso c).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso q).hom.app K =
      (Functor.mapDerivedCategoryNatIso r).hom.app (F.mapDerivedCategory.obj K) ≫
        (Functor.mapDerivedCategoryCompNatIso c').hom.app K := by
  have hi : c ≪≫ q = Functor.isoWhiskerLeft F r ≪≫ c' := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    exact hc M
  have hd := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K) hi
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hd
  have hw := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F r) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hw
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app K)).mp
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom,
    NatTrans.comp_app, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [hd, ← hw]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end AlgebraicGeometry.Scheme
