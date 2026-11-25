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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteLocalConstancyPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-!
# Cartesian stratum restriction with canonical finite constant coefficients

Source: Stacks Project, Modules on Sites, Tags 03D2, 03D8 and 093R,
lemma-pullback-module, lemma-push-pull-composition-modules and
lemma-pullback-locally-constant
(blueprint: lem-sf-cartesian-stratum-module-restriction).

The underlying comparison is normalized by the actual tensor-unit adjunction,
then by the canonical inverse-image composition comparisons. All fibre products
are the chosen fibre products of the original schemes.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Forget the constant coefficient action to the underlying abelian sheaf.
Source: Stacks Project, Tag 03D2
(blueprint: lem-sf-cartesian-stratum-module-restriction). -/
noncomputable abbrev proEtaleConstantModuleToAbelianSheaf (X : Scheme.{u})
    (A : Type u) [CommRing A] :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf _

/-- The canonical comparison from abelian inverse image to underlying module
pullback. Transpose the underlying unit of the tensor-unit-normalized module
adjunction through the abelian inverse-image adjunction. Thus this uses the
actual map sending an inverse-image section to its tensor with one.
Source: Stacks Project, Tags 03D2 and 03D3
(blueprint: lem-sf-cartesian-stratum-module-restriction). -/
noncomputable def proEtaleConstantModuleUnderlyingComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        ((proEtaleConstantModuleToAbelianSheaf Y A).obj M) ⟶
      (proEtaleConstantModuleToAbelianSheaf X A).obj
        ((proEtaleConstantRingPullback A f).obj M) :=
  ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    ((proEtaleConstantModuleToAbelianSheaf Y A).map
      ((proEtaleConstantRingAdjunction A f).unit.app M))

/-- Apply the two tensor-unit comparisons successively.
Source: Stacks Project, Tag 03D8
(blueprint: lem-sf-cartesian-stratum-module-restriction). -/
noncomputable def proEtaleIteratedConstantModuleUnderlyingComparison
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    (proEtaleSheafInverseImage k AddCommGrpCat.{u + 1} ⋙
      proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        ((proEtaleConstantModuleToAbelianSheaf V A).obj M) ⟶
      (proEtaleConstantModuleToAbelianSheaf Z A).obj
        ((proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h).obj M) :=
  (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
      (proEtaleConstantModuleUnderlyingComparison k A M) ≫
    proEtaleConstantModuleUnderlyingComparison h A ((proEtaleConstantRingPullback A k).obj M)

/-- Equality transport, compatible with the canonical constant-section maps.
Source: Stacks Project, Tag 03D8
(blueprint: lem-sf-cartesian-stratum-module-restriction). -/
theorem proEtaleSheafTransport_existsUnique
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    ∃! e : proEtaleSheafInverseImage f D ≅ proEtaleSheafInverseImage g D,
      e = eqToIso (congrArg (fun f ↦ proEtaleSheafInverseImage f D) w) ∧
      ∀ B : D, e.hom.app ((constantSheaf (ProEt.topology Y) D).obj B) ≫
        proEtaleConstantInverseImageMap g D B = proEtaleConstantInverseImageMap f D B := by
  subst g
  refine ⟨Iso.refl _, ⟨rfl, ?_⟩, ?_⟩
  · intro B
    simp
  · intro e he
    exact he.1

/-- Equality transport with a named normalization API.
Source: Stacks Project, Tag 03D8
(blueprint: lem-sf-cartesian-stratum-module-restriction). -/
noncomputable def proEtaleSheafTransport
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    proEtaleSheafInverseImage f D ≅ proEtaleSheafInverseImage g D :=
  Classical.choose (proEtaleSheafTransport_existsUnique D w).exists

private theorem proEtaleSheafTransport_eq
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    proEtaleSheafTransport D w =
      eqToIso (congrArg (fun f ↦ proEtaleSheafInverseImage f D) w) :=
  (Classical.choose_spec (proEtaleSheafTransport_existsUnique D w).exists).1

private theorem isoFactorization_existsUnique
    {C : Type u} [Category C] {F G H I : C}
    (p : F ≅ G) (d : F ≅ H) (q : H ≅ I) :
    ∃! e : G ≅ I, p.hom ≫ e.hom = d.hom ≫ q.hom := by
  refine ⟨p.symm ≪≫ d ≪≫ q, ?_, ?_⟩
  · simp
  · intro e he
    apply Iso.ext
    apply (cancel_epi p.hom).mp
    simpa using he

private theorem isoFactorization_eq
    {C : Type u} [Category C] {F G H I : C}
    (p : F ≅ G) (d : F ≅ H) (q : H ≅ I) (e : G ≅ I)
    (he : p.hom ≫ e.hom = d.hom ≫ q.hom) :
    e = p.symm ≪≫ d ≪≫ q := by
  apply Iso.ext
  apply (cancel_epi p.hom).mp
  simpa using he

/-- Cancellation uniquely determines the square comparison.
Source: Stacks Project, Tag 03D8
(blueprint: lem-sf-cartesian-stratum-module-restriction). -/
theorem stratumSheafComparison_existsUnique
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) :
    ∃! e : proEtaleSheafInverseImage g D ⋙
        proEtaleSheafInverseImage (pullback.snd s g) D ≅
      proEtaleSheafInverseImage s D ⋙ proEtaleSheafInverseImage (pullback.fst s g) D,
      (ProEtale.supportSiteProEtaleComparisonComp D (pullback.snd s g) g).hom ≫ e.hom =
        (proEtaleSheafTransport D (pullback.condition (f := s) (g := g)).symm).hom ≫
        (ProEtale.supportSiteProEtaleComparisonComp D (pullback.fst s g) s).hom :=
  isoFactorization_existsUnique _ _ _

/-- The specified underlying square comparison, through the equal composites
of the actual fibre-product projections. The composition comparisons are the
mates of the canonical fibre-product associativity maps on direct images.
Source: Stacks Project, Tags 03D8 and 03CB
(blueprint: lem-sf-cartesian-stratum-module-restriction). -/
noncomputable def proEtaleCartesianStratumSheafComparison
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) :
    proEtaleSheafInverseImage g D ⋙ proEtaleSheafInverseImage (pullback.snd s g) D ≅
      proEtaleSheafInverseImage s D ⋙ proEtaleSheafInverseImage (pullback.fst s g) D :=
  Classical.choose (stratumSheafComparison_existsUnique D s g).exists

private theorem stratumSheafComparison_eq
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) :
    proEtaleCartesianStratumSheafComparison D s g =
      (ProEtale.supportSiteProEtaleComparisonComp D (pullback.snd s g) g).symm ≪≫
        proEtaleSheafTransport D (pullback.condition (f := s) (g := g)).symm ≪≫
        ProEtale.supportSiteProEtaleComparisonComp D (pullback.fst s g) s :=
  isoFactorization_eq _ _ _ _
    (Classical.choose_spec (stratumSheafComparison_existsUnique D s g).exists)

private theorem stratumSheafComparison_cancellation
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [∀ T : Scheme.{u}, HasWeakSheafify (ProEt.topology T) D]
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) (N : Sheaf (ProEt.topology X) D) :
    (ProEtale.supportSiteProEtaleComparisonComp D (pullback.snd s g) g).hom.app N ≫
        (proEtaleCartesianStratumSheafComparison D s g).hom.app N =
      (proEtaleSheafTransport D (pullback.condition (f := s) (g := g)).symm).hom.app N ≫
        (ProEtale.supportSiteProEtaleComparisonComp D (pullback.fst s g) s).hom.app N := by
  exact congrArg (fun z ↦ z.app N)
    (Classical.choose_spec (stratumSheafComparison_existsUnique D s g).exists)

section ProofHelpers

private instance comparisonSheafToPresheafIsRightAdjoint (X : Scheme.{u}) :
    (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).IsRightAdjoint :=
  sheafToPresheaf_isRightAdjoint (ProEt.topology X) AddCommGrpCat.{u + 1}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage proEtaleConstantModuleUnderlyingComparison
  proEtaleIteratedConstantModuleUnderlyingComparison

private theorem underlyingComparison_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    IsIso (proEtaleConstantModuleUnderlyingComparison f A M) := by
  unfold proEtaleConstantModuleUnderlyingComparison
  exact ringUnitComparison f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingAdjunction A f) M

private theorem iteratedComparison_isIso
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    IsIso (proEtaleIteratedConstantModuleUnderlyingComparison h k A M) := by
  let := underlyingComparison_isIso k A M
  let := underlyingComparison_isIso h A ((proEtaleConstantRingPullback A k).obj M)
  unfold proEtaleIteratedConstantModuleUnderlyingComparison
  infer_instance

private noncomputable def moduleComp
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A (h ≫ k) ≅
      proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h :=
  (conjugateIsoEquiv
    ((proEtaleConstantRingAdjunction A k).comp (proEtaleConstantRingAdjunction A h))
    (proEtaleConstantRingAdjunction A (h ≫ k))).symm (directComp k h A)

private theorem iteratedComparison_transpose
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    (((proEtaleSheafAdjunction k AddCommGrpCat.{u + 1}).comp
      (proEtaleSheafAdjunction h AddCommGrpCat.{u + 1})).homEquiv _ _)
      (proEtaleIteratedConstantModuleUnderlyingComparison h k A M) =
    (proEtaleConstantModuleToAbelianSheaf V A).map
      (((proEtaleConstantRingAdjunction A k).comp
        (proEtaleConstantRingAdjunction A h)).unit.app M) := by
  dsimp only [Functor.comp_obj]
  change (proEtaleSheafAdjunction k AddCommGrpCat.{u + 1}).homEquiv _ _
    ((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _
      (proEtaleIteratedConstantModuleUnderlyingComparison h k A M)) = _
  unfold proEtaleIteratedConstantModuleUnderlyingComparison
  rw [Adjunction.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  simp only [proEtaleConstantModuleUnderlyingComparison, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Equiv.apply_symm_apply]
  rw [Adjunction.comp_unit_app, CategoryTheory.Functor.map_comp]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

attribute [local irreducible] directComp moduleComp

private theorem forget_pushforward_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)} (t : M ⟶ N) :
    (proEtaleConstantModuleToAbelianSheaf Y A).map
        ((proEtaleConstantRingPushforward A f).map t) =
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
        ((proEtaleConstantModuleToAbelianSheaf X A).map t) := by
  rfl

private theorem directComp_underlying
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) (U : V.ProEtᵒᵖ) :
    ((proEtaleConstantModuleToAbelianSheaf V A).map
      ((directComp k h A).hom.app N)).hom.app U =
      N.val.presheaf.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U.unop).op := by
  unfold directComp
  rfl

private theorem compComparison_normalization
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    proEtaleConstantModuleUnderlyingComparison (h ≫ k) A M ≫
        (proEtaleConstantModuleToAbelianSheaf Z A).map ((moduleComp h k A).hom.app M) =
      (ProEtale.supportSiteProEtaleComparisonComp AddCommGrpCat.{u + 1} h k).hom.app
          ((proEtaleConstantModuleToAbelianSheaf V A).obj M) ≫
        proEtaleIteratedConstantModuleUnderlyingComparison h k A M := by
  let a := proEtaleSheafAdjunction (h ≫ k) AddCommGrpCat.{u + 1}
  let b := (proEtaleSheafAdjunction k AddCommGrpCat.{u + 1}).comp
    (proEtaleSheafAdjunction h AddCommGrpCat.{u + 1})
  let d := Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).symm
    AddCommGrpCat.{u + 1} (ProEt.topology V) (ProEt.topology W) (ProEt.topology Z)
  apply (a.homEquiv _ _).injective
  rw [a.homEquiv_naturality_right]
  have hs : a.homEquiv _ _ (proEtaleConstantModuleUnderlyingComparison (h ≫ k) A M) =
      (proEtaleConstantModuleToAbelianSheaf V A).map
        ((proEtaleConstantRingAdjunction A (h ≫ k)).unit.app M) :=
      by
    unfold proEtaleConstantModuleUnderlyingComparison
    exact (a.homEquiv _ _).apply_symm_apply _
  rw [hs]
  have hr := homEquiv_mate a b d
    (proEtaleIteratedConstantModuleUnderlyingComparison h k A M)
  change _ = a.homEquiv _ _
    (((conjugateIsoEquiv a b).symm d.symm).inv.app _ ≫ _)
  refine Eq.trans ?_ hr.symm
  erw [iteratedComparison_transpose]
  have hu := unit_conjugateEquiv_symm
    ((proEtaleConstantRingAdjunction A k).comp (proEtaleConstantRingAdjunction A h))
    (proEtaleConstantRingAdjunction A (h ≫ k)) (directComp k h A).hom M
  have ht := congrArg ((proEtaleConstantModuleToAbelianSheaf V A).map) hu
  simp only [CategoryTheory.Functor.map_comp] at ht
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rw [forget_pushforward_map] at ht
  have hU := congrArg (fun t ↦ t.hom.app U) ht.symm
  change _ ≫ _ = _ ≫ _ at hU
  rw [directComp_underlying] at hU
  unfold moduleComp
  exact hU

private theorem locallyConstant_iff (X : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    IsLocallyConstantProEtaleModuleSheafOfUniverses X A M ↔
      IsLocallyConstantProEtaleModuleSheaf X A M := by
  constructor
  · rintro ⟨I, U, f, hf, h⟩
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨N, _, e⟩ := h i
    exact ⟨N, e⟩
  · rintro ⟨I, U, f, hf, h⟩
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨N, e⟩ := h i
    exact ⟨N, trivial, e⟩

private theorem locallyConstant_of_iso {X : Scheme.{u}} (A : Type u) [CommRing A]
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)} (e : M ≅ N)
    (h : IsLocallyConstantProEtaleModuleSheafOfUniverses X A N) :
    IsLocallyConstantProEtaleModuleSheafOfUniverses X A M := by
  obtain ⟨I, U, f, hf, h⟩ := h
  refine ⟨I, U, f, hf, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨q⟩⟩ := h i
  exact ⟨P, hP, ⟨(SheafOfModules.overFunctor _ (U i)).mapIso e ≪≫ q⟩⟩

private theorem compComparison_inverse_normalization
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    proEtaleIteratedConstantModuleUnderlyingComparison h k A M ≫
        (proEtaleConstantModuleToAbelianSheaf Z A).map ((moduleComp h k A).inv.app M) =
      (ProEtale.supportSiteProEtaleComparisonComp AddCommGrpCat.{u + 1} h k).inv.app
          ((proEtaleConstantModuleToAbelianSheaf V A).obj M) ≫
        proEtaleConstantModuleUnderlyingComparison (h ≫ k) A M := by
  apply (cancel_epi ((ProEtale.supportSiteProEtaleComparisonComp
    AddCommGrpCat.{u + 1} h k).hom.app
      ((proEtaleConstantModuleToAbelianSheaf V A).obj M))).mp
  rw [← Category.assoc, ← compComparison_normalization]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  change proEtaleConstantModuleUnderlyingComparison (h ≫ k) A M ≫
    (proEtaleConstantModuleToAbelianSheaf Z A).map
      (𝟙 ((proEtaleConstantRingPullback A (h ≫ k)).obj M)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private noncomputable def sheafComp
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    proEtaleSheafInverseImage (h ≫ k) AddCommGrpCat.{u + 1} ≅
      proEtaleSheafInverseImage k AddCommGrpCat.{u + 1} ⋙
        proEtaleSheafInverseImage h AddCommGrpCat.{u + 1} :=
  ProEtale.supportSiteProEtaleComparisonComp AddCommGrpCat.{u + 1} h k

attribute [local irreducible] sheafComp

private noncomputable def moduleTransport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A f ≅ proEtaleConstantRingPullback A g :=
  eqToIso (congrArg (proEtaleConstantRingPullback A) w)

private noncomputable def sheafTransport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ≅
      proEtaleSheafInverseImage g AddCommGrpCat.{u + 1} :=
  proEtaleSheafTransport AddCommGrpCat.{u + 1} w

attribute [local irreducible] moduleTransport sheafTransport

private noncomputable def moduleSquareGeneric
    {Z W W' V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (h' : Z ⟶ W') (k' : W' ⟶ V) (w : h ≫ k = h' ≫ k')
    (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h ≅
      proEtaleConstantRingPullback A k' ⋙ proEtaleConstantRingPullback A h' :=
  (moduleComp h k A).symm ≪≫ moduleTransport w A ≪≫
    moduleComp h' k' A

private noncomputable def sheafSquareGeneric
    {Z W W' V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (h' : Z ⟶ W') (k' : W' ⟶ V) (w : h ≫ k = h' ≫ k') :
    proEtaleSheafInverseImage k AddCommGrpCat.{u + 1} ⋙
        proEtaleSheafInverseImage h AddCommGrpCat.{u + 1} ≅
      proEtaleSheafInverseImage k' AddCommGrpCat.{u + 1} ⋙
        proEtaleSheafInverseImage h' AddCommGrpCat.{u + 1} :=
  (sheafComp h k).symm ≪≫
    sheafTransport w ≪≫
    sheafComp h' k'

attribute [local irreducible] moduleSquareGeneric sheafSquareGeneric

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄

private theorem square_arrows
    {C : Type w₁} {D : Type w₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
    {X₁ X₀ X₀' X₂ : D} {A₁ A₀ A₀' A₂ : C}
    (c₁ : X₁ ⟶ F.obj A₁) (c₀ : X₀ ⟶ F.obj A₀)
    (c₀' : X₀' ⟶ F.obj A₀') (c₂ : X₂ ⟶ F.obj A₂)
    (a : A₁ ⟶ A₀) (e : A₀ ⟶ A₀') (b : A₀' ⟶ A₂)
    (p : X₁ ⟶ X₀) (d : X₀ ⟶ X₀') (q : X₀' ⟶ X₂)
    (h₁ : c₁ ≫ F.map a = p ≫ c₀) (h₂ : c₀ ≫ F.map e = d ≫ c₀')
    (h₃ : c₀' ≫ F.map b = q ≫ c₂) :
    c₁ ≫ F.map (a ≫ e ≫ b) = (p ≫ d ≫ q) ≫ c₂ := by
  simp only [F.map_comp, Category.assoc]
  rw [← Category.assoc c₁, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc c₀, h₂]
  simp only [Category.assoc]
  rw [h₃]

private theorem square_nat_isos
    {C : Type w₁} {D : Type w₂} {E : Type w₃} {B : Type w₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} B]
    (F : C ⥤ D) {A₁ A₀ A₀' A₂ : E ⥤ C} {X₁ X₀ X₀' X₂ : B ⥤ D}
    (M : E) (N : B)
    (a : A₁ ≅ A₀) (e : A₀ ≅ A₀') (b : A₀' ≅ A₂)
    (p : X₁ ≅ X₀) (d : X₀ ≅ X₀') (q : X₀' ≅ X₂)
    (c₁ : X₁.obj N ⟶ F.obj (A₁.obj M))
    (c₀ : X₀.obj N ⟶ F.obj (A₀.obj M))
    (c₀' : X₀'.obj N ⟶ F.obj (A₀'.obj M))
    (c₂ : X₂.obj N ⟶ F.obj (A₂.obj M))
    (h₁ : c₁ ≫ F.map (a.hom.app M) = p.hom.app N ≫ c₀)
    (h₂ : c₀ ≫ F.map (e.hom.app M) = d.hom.app N ≫ c₀')
    (h₃ : c₀' ≫ F.map (b.hom.app M) = q.hom.app N ≫ c₂) :
    c₁ ≫ F.map ((a ≪≫ e ≪≫ b).hom.app M) =
      (p ≪≫ d ≪≫ q).hom.app N ≫ c₂ := by
  simpa only [Iso.trans_hom, NatTrans.comp_app] using
    square_arrows F c₁ c₀ c₀' c₂ (a.hom.app M) (e.hom.app M) (b.hom.app M)
      (p.hom.app N) (d.hom.app N) (q.hom.app N) h₁ h₂ h₃

private theorem operation_inverse
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    proEtaleIteratedConstantModuleUnderlyingComparison h k A M ≫
        (proEtaleConstantModuleToAbelianSheaf Z A).map ((moduleComp h k A).inv.app M) =
      (sheafComp h k).inv.app
          ((proEtaleConstantModuleToAbelianSheaf V A).obj M) ≫
        proEtaleConstantModuleUnderlyingComparison (h ≫ k) A M := by
  unfold sheafComp
  exact compComparison_inverse_normalization h k A M

private theorem operation_forward
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    proEtaleConstantModuleUnderlyingComparison (h ≫ k) A M ≫
        (proEtaleConstantModuleToAbelianSheaf Z A).map ((moduleComp h k A).hom.app M) =
      (sheafComp h k).hom.app
          ((proEtaleConstantModuleToAbelianSheaf V A).obj M) ≫
        proEtaleIteratedConstantModuleUnderlyingComparison h k A M := by
  unfold sheafComp
  exact compComparison_normalization h k A M

private theorem operation_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) (A : Type u) [CommRing A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    proEtaleConstantModuleUnderlyingComparison f A M ≫
        (proEtaleConstantModuleToAbelianSheaf X A).map
          ((moduleTransport w A).hom.app M) =
      (sheafTransport w).hom.app
          ((proEtaleConstantModuleToAbelianSheaf Y A).obj M) ≫
        proEtaleConstantModuleUnderlyingComparison g A M := by
  subst g
  unfold moduleTransport sheafTransport
  rw [proEtaleSheafTransport_eq]
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback

private theorem moduleSquareGeneric_normalization
    {Z W W' V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (h' : Z ⟶ W') (k' : W' ⟶ V) (w : h ≫ k = h' ≫ k')
    (A : Type u) [CommRing A] (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
    proEtaleIteratedConstantModuleUnderlyingComparison h k A M ≫
        (proEtaleConstantModuleToAbelianSheaf Z A).map
          ((moduleSquareGeneric h k h' k' w A).hom.app M) =
      (sheafSquareGeneric h k h' k' w).hom.app
          ((proEtaleConstantModuleToAbelianSheaf V A).obj M) ≫
        proEtaleIteratedConstantModuleUnderlyingComparison h' k' A M := by
  unfold moduleSquareGeneric sheafSquareGeneric
  have he := @square_nat_isos
    (proEtaleRingModules Z (proEtaleConstantRing Z A))
    (Sheaf (ProEt.topology Z) AddCommGrpCat.{u + 1})
    (proEtaleRingModules V (proEtaleConstantRing V A))
    (Sheaf (ProEt.topology V) AddCommGrpCat.{u + 1}) _ _ _ _
    (proEtaleConstantModuleToAbelianSheaf Z A)
    (proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h)
    (proEtaleConstantRingPullback A (h ≫ k))
    (proEtaleConstantRingPullback A (h' ≫ k'))
    (proEtaleConstantRingPullback A k' ⋙ proEtaleConstantRingPullback A h')
    (proEtaleSheafInverseImage k AddCommGrpCat.{u + 1} ⋙
      proEtaleSheafInverseImage h AddCommGrpCat.{u + 1})
    (proEtaleSheafInverseImage (h ≫ k) AddCommGrpCat.{u + 1})
    (proEtaleSheafInverseImage (h' ≫ k') AddCommGrpCat.{u + 1})
    (proEtaleSheafInverseImage k' AddCommGrpCat.{u + 1} ⋙
      proEtaleSheafInverseImage h' AddCommGrpCat.{u + 1}) M
    ((proEtaleConstantModuleToAbelianSheaf V A).obj M)
    (moduleComp h k A).symm
    (moduleTransport w A)
    (moduleComp h' k' A)
    (sheafComp h k).symm
    (sheafTransport w)
    (sheafComp h' k')
    (proEtaleIteratedConstantModuleUnderlyingComparison h k A M)
    (proEtaleConstantModuleUnderlyingComparison (h ≫ k) A M)
    (proEtaleConstantModuleUnderlyingComparison (h' ≫ k') A M)
    (proEtaleIteratedConstantModuleUnderlyingComparison h' k' A M)
    (operation_inverse h k A M) (operation_congr w A M) (operation_forward h' k' A M)
  exact he

private instance comparisonSheafToPresheafAll :
    ∀ X : Scheme.{u},
      (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).IsRightAdjoint :=
  fun X ↦ comparisonSheafToPresheafIsRightAdjoint X

private theorem sheafSquare_special
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) :
    sheafSquareGeneric (pullback.snd s g) g (pullback.fst s g) s
        pullback.condition.symm =
      proEtaleCartesianStratumSheafComparison AddCommGrpCat.{u + 1} s g := by
  rw [stratumSheafComparison_eq]
  unfold sheafSquareGeneric sheafComp sheafTransport
  rfl

private theorem moduleSquare_normalization
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    IsIso (proEtaleIteratedConstantModuleUnderlyingComparison (pullback.snd s g) g A M) ∧
      IsIso (proEtaleIteratedConstantModuleUnderlyingComparison (pullback.fst s g) s A M) ∧
      proEtaleIteratedConstantModuleUnderlyingComparison (pullback.snd s g) g A M ≫
          (proEtaleConstantModuleToAbelianSheaf (pullback s g) A).map
            ((moduleSquareGeneric (pullback.snd s g) g (pullback.fst s g) s
              pullback.condition.symm A).hom.app M) =
        (proEtaleCartesianStratumSheafComparison AddCommGrpCat.{u + 1} s g).hom.app
            ((proEtaleConstantModuleToAbelianSheaf X A).obj M) ≫
          proEtaleIteratedConstantModuleUnderlyingComparison (pullback.fst s g) s A M := by
  refine ⟨iteratedComparison_isIso _ _ A M, iteratedComparison_isIso _ _ A M, ?_⟩
  have hi := moduleSquareGeneric_normalization (pullback.snd s g) g (pullback.fst s g) s
    pullback.condition.symm A M
  have hi' := hi.trans (congrArg (fun e ↦ e.hom.app
    ((proEtaleConstantModuleToAbelianSheaf X A).obj M) ≫
      proEtaleIteratedConstantModuleUnderlyingComparison (pullback.fst s g) s A M)
    (sheafSquare_special s g))
  exact hi'

private theorem normalizedSquare_exists
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X) (A : Type u) [CommRing A] :
    ∃ e : proEtaleConstantRingPullback A g ⋙
        proEtaleConstantRingPullback A (pullback.snd s g) ≅
      proEtaleConstantRingPullback A s ⋙
        proEtaleConstantRingPullback A (pullback.fst s g),
      ∀ M : proEtaleRingModules X (proEtaleConstantRing X A),
      IsIso (proEtaleIteratedConstantModuleUnderlyingComparison (pullback.snd s g) g A M) ∧
      IsIso (proEtaleIteratedConstantModuleUnderlyingComparison (pullback.fst s g) s A M) ∧
      proEtaleIteratedConstantModuleUnderlyingComparison (pullback.snd s g) g A M ≫
        (proEtaleConstantModuleToAbelianSheaf (pullback s g) A).map (e.hom.app M) =
      (proEtaleCartesianStratumSheafComparison AddCommGrpCat.{u + 1} s g).hom.app
        ((proEtaleConstantModuleToAbelianSheaf X A).obj M) ≫
        proEtaleIteratedConstantModuleUnderlyingComparison (pullback.fst s g) s A M := by
  exact ⟨moduleSquareGeneric (pullback.snd s g) g (pullback.fst s g) s
    pullback.condition.symm A, moduleSquare_normalization s g A⟩

private theorem moduleSquare_finite
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    ∀ M : proEtaleRingModules X (proEtaleConstantRing X A),
        (IsLocallyConstantProEtaleModuleSheafOfUniverses S A
            (proEtaleConstantModulePullback s A M) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S),
            Finite ((geometricRingModuleStalkFunctor y (proEtaleConstantRing S A)).obj
              (proEtaleConstantModulePullback s A M))) →
        IsLocallyConstantProEtaleModuleSheafOfUniverses (pullback s g) A
            (proEtaleConstantModulePullback (pullback.snd s g) A
              (proEtaleConstantModulePullback g A M)) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (y : Spec (.of Ω) ⟶ pullback s g),
            Finite ((geometricRingModuleStalkFunctor y
              (proEtaleConstantRing (pullback s g) A)).obj
                (proEtaleConstantModulePullback (pullback.snd s g) A
                  (proEtaleConstantModulePullback g A M))) := by
  intro M hM
  have hm := proEtale_finiteLocalConstancy_pullback (pullback.fst s g) A
    (proEtaleConstantModulePullback s A M) ⟨(locallyConstant_iff S A _).mp hM.1, hM.2⟩
  refine ⟨locallyConstant_of_iso A (((moduleSquareGeneric (pullback.snd s g) g (pullback.fst s g) s
      pullback.condition.symm A).app M))
    ((locallyConstant_iff (pullback s g) A _).mpr hm.1), ?_⟩
  intro Ω _ _ y
  let : Finite ((geometricRingModuleStalkFunctor y
      (proEtaleConstantRing (pullback s g) A)).obj
        ((proEtaleConstantRingPullback A s ⋙
          proEtaleConstantRingPullback A (pullback.fst s g)).obj M)) := hm.2 Ω y
  let e := (geometricRingModuleStalkFunctor y (proEtaleConstantRing (pullback s g) A)).mapIso
    (((moduleSquareGeneric (pullback.snd s g) g (pullback.fst s g) s
      pullback.condition.symm A).app M))
  exact Finite.of_equiv _
    (Equiv.ofBijective e.inv (ConcreteCategory.bijective_of_isIso e.inv))

end ProofHelpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coefficientTransport_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) (A : Type u) [CommRing A] :
    (proEtaleSheafTransport CommRingCat.{u + 1} w).hom.app (proEtaleConstantRing Y A) ≫
      proEtaleCoefficientInverseImageMap g A = proEtaleCoefficientInverseImageMap f A :=
  (Classical.choose_spec (proEtaleSheafTransport_existsUnique CommRingCat.{u + 1} w).exists).2
    (CommRingCat.of (ULift.{u + 1, u} A))

private theorem coefficientComposition_arrows
    {C : Type u} [Category C] {W X Y Z K : C}
    (p : W ⟶ X) (q : X ⟶ Y) (d : W ⟶ Z) (t : Z ⟶ Y)
    (a : Y ⟶ K) (b : Z ⟶ K) (c : W ⟶ K)
    (h₁ : p ≫ q = d ≫ t) (h₂ : t ≫ a = b) (h₃ : d ≫ b = c) :
    p ≫ q ≫ a = c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, h₃]

private theorem coefficientSquare_cancelled
    {S Y X : Scheme.{u}} (s : S ⟶ X) (g : Y ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    (ProEtale.supportSiteProEtaleComparisonComp CommRingCat.{u + 1}
        (pullback.snd s g) g).hom.app (proEtaleConstantRing X A) ≫
      (proEtaleCartesianStratumSheafComparison CommRingCat.{u + 1} s g).hom.app
        (proEtaleConstantRing X A) ≫
      (proEtaleSheafInverseImage (pullback.fst s g) CommRingCat.{u + 1}).map
        (proEtaleCoefficientInverseImageMap s A) ≫
      proEtaleCoefficientInverseImageMap (pullback.fst s g) A =
        proEtaleCoefficientInverseImageMap (pullback.snd s g ≫ g) A := by
  exact coefficientComposition_arrows _ _ _ _ _ _ _
    (stratumSheafComparison_cancellation CommRingCat.{u + 1} s g
      (proEtaleConstantRing X A))
    (proEtaleCoefficientInverseImageMap_comp (pullback.fst s g) s A).symm
    (coefficientTransport_congr pullback.condition.symm A)

/-- Canonical coefficient-linear restriction to the actual cartesian stratum,
including preservation of local constancy and all finite geometric stalks.
Source: Stacks Project, Tags 03D2, 03D8 and 093R
(blueprint: lem-sf-cartesian-stratum-module-restriction).

Proof: (1) By prop-weil-pbc-proetale-constant-ring-map each specified coefficient
map is invertible. Cancel extension of scalars in the actual sheafified tensor:
the contraction sends a pure tensor to the action of the inverse coefficient
map, and its inverse tensors with one. This is precisely the comparison obtained
from the tensor-unit-normalized module adjunction used above.
(2) Apply lem-pur-proetale-constant-ring-composition to both projection paths.
Both coefficient maps agree with that of the common composite, including on
every constant section. (3) Under these identifications take the inverse of the
first inverse-image composition comparison followed by the second, transporting
through pullback.condition. Naturality on addition and scalar multiplication,
and finite-product preservation from lem-weil-pbc-left-exact-site-inverse-image-tensor,
show that this map is additive and coefficient-linear. Naturality in M gives
the displayed naturality equation, and the construction gives the underlying
normalization equation. (4) Apply lem-pur-proetale-finite-local-constancy-pullback
to g' and s_A^*M. Transfer local trivializations and geometric stalk finiteness
across theta. (5) Nothing changes the original schemes or assumes Noetherianity,
reducedness or invertibility. On the empty source the sheaves are zero and
there are no geometric points; for the zero coefficient ring all modules are zero. -/
theorem proEtale_cartesianStratum_moduleRestriction
    {S Y X : Scheme.{u}} (s : S ⟶ X) [IsImmersion s] (g : Y ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    ∃ theta : ∀ M : proEtaleRingModules X (proEtaleConstantRing X A),
        proEtaleConstantModulePullback (pullback.snd s g) A
            (proEtaleConstantModulePullback g A M) ≅
          proEtaleConstantModulePullback (pullback.fst s g) A
            (proEtaleConstantModulePullback s A M),
      (∀ (M N : proEtaleRingModules X (proEtaleConstantRing X A)) (a : M ⟶ N),
        proEtaleConstantModulePullbackMap (pullback.snd s g) A
            (proEtaleConstantModulePullbackMap g A a) ≫ (theta N).hom =
          (theta M).hom ≫ proEtaleConstantModulePullbackMap (pullback.fst s g) A
            (proEtaleConstantModulePullbackMap s A a)) ∧
      (∀ M : proEtaleRingModules X (proEtaleConstantRing X A),
        IsIso (proEtaleIteratedConstantModuleUnderlyingComparison (pullback.snd s g) g A M) ∧
        IsIso (proEtaleIteratedConstantModuleUnderlyingComparison (pullback.fst s g) s A M) ∧
        proEtaleIteratedConstantModuleUnderlyingComparison (pullback.snd s g) g A M ≫
            (proEtaleConstantModuleToAbelianSheaf (pullback s g) A).map (theta M).hom =
          (proEtaleCartesianStratumSheafComparison AddCommGrpCat.{u + 1} s g).hom.app
              ((proEtaleConstantModuleToAbelianSheaf X A).obj M) ≫
            proEtaleIteratedConstantModuleUnderlyingComparison (pullback.fst s g) s A M) ∧
      ((ProEtale.supportSiteProEtaleComparisonComp CommRingCat.{u + 1}
          (pullback.snd s g) g).hom.app (proEtaleConstantRing X A) ≫
        (proEtaleSheafInverseImage (pullback.snd s g) CommRingCat.{u + 1}).map
          (proEtaleCoefficientInverseImageMap g A) ≫
        proEtaleCoefficientInverseImageMap (pullback.snd s g) A =
          proEtaleCoefficientInverseImageMap (pullback.snd s g ≫ g) A) ∧
      ((ProEtale.supportSiteProEtaleComparisonComp CommRingCat.{u + 1}
          (pullback.snd s g) g).hom.app (proEtaleConstantRing X A) ≫
        (proEtaleCartesianStratumSheafComparison CommRingCat.{u + 1} s g).hom.app
          (proEtaleConstantRing X A) ≫
        (proEtaleSheafInverseImage (pullback.fst s g) CommRingCat.{u + 1}).map
          (proEtaleCoefficientInverseImageMap s A) ≫
        proEtaleCoefficientInverseImageMap (pullback.fst s g) A =
          proEtaleCoefficientInverseImageMap (pullback.snd s g ≫ g) A) ∧
      (∀ M : proEtaleRingModules X (proEtaleConstantRing X A),
        (IsLocallyConstantProEtaleModuleSheafOfUniverses S A
            (proEtaleConstantModulePullback s A M) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S),
            Finite ((geometricRingModuleStalkFunctor y (proEtaleConstantRing S A)).obj
              (proEtaleConstantModulePullback s A M))) →
        IsLocallyConstantProEtaleModuleSheafOfUniverses (pullback s g) A
            (proEtaleConstantModulePullback (pullback.snd s g) A
              (proEtaleConstantModulePullback g A M)) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (y : Spec (.of Ω) ⟶ pullback s g),
            Finite ((geometricRingModuleStalkFunctor y
              (proEtaleConstantRing (pullback s g) A)).obj
                (proEtaleConstantModulePullback (pullback.snd s g) A
                  (proEtaleConstantModulePullback g A M)))) := by
  obtain ⟨e, he⟩ := normalizedSquare_exists s g A
  refine ⟨fun M ↦ e.app M, ?_, he, ?_, ?_, ?_⟩
  · intro M N a
    exact e.hom.naturality a
  · exact (proEtaleCoefficientInverseImageMap_comp (pullback.snd s g) g A).symm
  · exact coefficientSquare_cancelled s g A
  · exact moduleSquare_finite s g A

end AlgebraicGeometry.Scheme
