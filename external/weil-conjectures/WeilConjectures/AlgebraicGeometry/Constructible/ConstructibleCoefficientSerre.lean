/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
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
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Exact closure of constructible sheaves in the site coefficient universe
Source: Stacks Tags 09B5 and 093U, with finite global partitions.
(blueprint: lem-weil-constructible-coefficient-serre). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

namespace CoefficientSerre

variable (T : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

/-- The canonical constant-section map, forgetting commutativity. -/
private noncomputable def proEtaleModuleScalarUnit :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of B) ⟶
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (adicLisseConstantRing T B)).obj :=
  Functor.whiskerRight (toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- Restriction to constant scalars preserves the underlying additive sheaf exactly. -/
private noncomputable def proEtaleModuleRestriction :
    pbcModules T (adicLisseConstantRing T B) ⥤
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} B) where
  obj M := by
    let P := (_root_.PresheafOfModules.restrictScalars (proEtaleModuleScalarUnit T B)).obj M.val
    let F : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} B :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology T) F
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((_root_.PresheafOfModules.restrictScalars
      (proEtaleModuleScalarUnit T B)).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

private noncomputable def constantModulePresheaf :
    (T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} B) ⥤
      _root_.PresheafOfModules.{u + 1}
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B)) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map φ :=
    { app := φ.app
      naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }

private noncomputable def constantModuleFullyFaithful :
    (constantModulePresheaf T B).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private noncomputable instance : (constantModulePresheaf T B).Full :=
  (constantModuleFullyFaithful T B).full

private noncomputable instance : (constantModulePresheaf T B).Faithful :=
  (constantModuleFullyFaithful T B).faithful

private noncomputable def moduleEmbedding :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} B) ⋙
    constantModulePresheaf T B

private noncomputable instance : (moduleEmbedding T B).Full :=
  inferInstanceAs (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} B) ⋙ constantModulePresheaf T B).Full

private noncomputable instance : (moduleEmbedding T B).Faithful :=
  inferInstanceAs (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} B) ⋙ constantModulePresheaf T B).Faithful

private noncomputable instance scalarUnit_injective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (proEtaleModuleScalarUnit T B) :=
  adicLisseConstantUnit_locallyInjective T B

private noncomputable instance scalarUnit_surjective :
    Presheaf.IsLocallySurjective (ProEt.topology T) (proEtaleModuleScalarUnit T B) :=
  adicLisseConstantUnit_locallySurjective T B

private noncomputable instance restriction_full : (proEtaleModuleRestriction T B).Full := by
  exact Functor.Full.of_comp_faithful_iso
    (G := moduleEmbedding T B)
    (H := SheafOfModules.forget _ ⋙
      _root_.PresheafOfModules.restrictScalars (proEtaleModuleScalarUnit T B)) (Iso.refl _)

private noncomputable instance restriction_faithful :
    (proEtaleModuleRestriction T B).Faithful := by
  exact Functor.Faithful.of_comp_iso
    (G := moduleEmbedding T B)
    (H := SheafOfModules.forget _ ⋙
      _root_.PresheafOfModules.restrictScalars (proEtaleModuleScalarUnit T B)) (Iso.refl _)

private noncomputable instance restriction_essSurj :
    (proEtaleModuleRestriction T B).EssSurj where
  mem_essImage F := by
    let P := (moduleEmbedding T B).obj F
    let adj := _root_.PresheafOfModules.sheafificationAdjunction.{u + 1}
      (proEtaleModuleScalarUnit T B)
    have hη : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (_root_.PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (ProEt.topology T) P.presheaf)
      exact isIso_toSheafify (ProEt.topology T)
        ((sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} B)
            AddCommGrpCat.{u + 1})).obj F).property
    refine ⟨(_root_.PresheafOfModules.sheafification.{u + 1}
      (proEtaleModuleScalarUnit T B)).obj P, ⟨?_⟩⟩
    exact (Functor.FullyFaithful.ofFullyFaithful (moduleEmbedding T B)).preimageIso
      (asIso (adj.unit.app P)).symm

private noncomputable def encoding :
    pbcModules T (adicLisseConstantRing T B) ≌
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} B) := by
  have : (proEtaleModuleRestriction T B).IsEquivalence := {}
  exact (proEtaleModuleRestriction T B).asEquivalence

end CoefficientSerre

namespace CoefficientSerre
open CategoryTheory.Functor
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A]

private noncomputable def coefficientIso :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (adicLisseConstantRing Y A) ≅ adicLisseConstantRing X A :=
  haveI := proEtaleConstantComparison_isIso f (CommRingCat.of A)
  asIso ((proEtaleConstantComparison f).app (CommRingCat.of A))

private theorem coefficient_adjunct :
    proEtaleRingDirectImageMap f (adicLisseConstantRing Y A) (adicLisseConstantRing X A)
      (coefficientIso f A) = proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of A) := by
  exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of A))

private theorem constant_sections :
    toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)).hom =
    Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))) := by
  exact ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    _ _).apply_symm_apply _

private noncomputable def directImageComparison :
    proEtaleRingModuleDirectImage f (adicLisseConstantRing Y A) (adicLisseConstantRing X A)
        (coefficientIso f A) ⋙ proEtaleModuleRestriction Y A ≅
      proEtaleModuleRestriction X A ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} A) f := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := (((proEtaleRingModuleDirectImage f (adicLisseConstantRing Y A)
        (adicLisseConstantRing X A) (coefficientIso f A) ⋙
          proEtaleModuleRestriction Y A).obj M).obj.obj U)
    let Q := (((proEtaleModuleRestriction X A ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M).obj.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[A] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    change ((proEtaleRingDirectImageMap f (adicLisseConstantRing Y A)
        (adicLisseConstantRing X A) (coefficientIso f A)).hom.app U).hom
          (((proEtaleModuleScalarUnit Y A).app U).hom b) •
          (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m) =
      (((proEtaleModuleScalarUnit X A).app ((proEtaleBaseChange f).op.obj U)).hom b) •
          (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m)
    rw [coefficient_adjunct]
    exact congrArg (fun r ↦ r •
      (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m))
      (ConcreteCategory.congr_hom (congr_app (constant_sections f A) U) b)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

private noncomputable def pullbackComparison
    (M : pbcModules Y (adicLisseConstantRing Y A)) :
    (proEtaleModuleRestriction X A).obj
      ((proEtaleRingModulePullback f (adicLisseConstantRing Y A)
        (adicLisseConstantRing X A) (coefficientIso f A)).obj M) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj
        ((proEtaleModuleRestriction Y A).obj M) := by
  let EX := encoding X A
  let EY := encoding Y A
  let L := ProEtale.upperStar (ModuleCat.{u + 1} A) f
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} A) f
  let adj := EY.toAdjunction.comp
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp EX.symm.toAdjunction)
  let eR : EX.functor ⋙ R ⋙ EY.inverse ≅
      proEtaleRingModuleDirectImage f (adicLisseConstantRing Y A)
        (adicLisseConstantRing X A) (coefficientIso f A) :=
    (isoWhiskerRight (directImageComparison f A).symm EY.inverse) ≪≫
      isoWhiskerLeft _ EY.unitIso.symm
  let adj' := adj.ofNatIsoRight eR
  let e := (proEtaleRingModuleAdjunction f (adicLisseConstantRing Y A)
    (adicLisseConstantRing X A) (coefficientIso f A)).leftAdjointUniq adj'
  exact EX.functor.mapIso (e.app M) ≪≫
    EX.counitIso.app (L.obj (EY.functor.obj M))

private noncomputable def relativeRestriction :
    pbcModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (adicLisseConstantRing Y A)) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A) :=
  pbcRestrict (coefficientIso f A).inv ⋙ proEtaleModuleRestriction X A

private noncomputable def relativePullbackComparison
    (M : pbcModules Y (adicLisseConstantRing Y A)) :
    (relativeRestriction f A).obj
      ((proEtaleModuleInverseImage f (adicLisseConstantRing Y A)).obj M) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj
        ((proEtaleModuleRestriction Y A).obj M) := by
  let N := (proEtaleModuleInverseImage f (adicLisseConstantRing Y A)).obj M
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (coefficientIso f A)).choose
  exact (proEtaleModuleRestriction X A).mapIso (θ N).symm ≪≫ pullbackComparison f A M

private noncomputable def constantEncoding (T : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] (M : ModuleCat.{u + 1} B) :
    (proEtaleModuleRestriction T B).obj ((adicLisseConstantModules T B).obj M) ≅
      (constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} B)).obj M := by
  let α := proEtaleModuleScalarUnit T B
  have := ConstantScalarComparison.constantComparisonHom_isIso
    (ProEt.topology T) B _ α M
  exact (asIso (ConstantScalarComparison.constantComparisonHom
    (ProEt.topology T) B _ α M)).symm

private noncomputable def constantPullback (M : ModuleCat.{u + 1} A) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj
        ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M := by
  let D := ModuleCat.{u + 1} A
  let Z := ⊤_ Y.ProEt
  let hZ : IsTerminal Z := terminalIsTerminal
  let adj := ((constantSheafAdj (ProEt.topology Y) D hZ).comp
    (ProEtale.upperStarLowerStarAdjunction D f)).ofNatIsoRight
      ((proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso D
        (ProEt.topology Y) (ProEt.topology X) (Opposite.op Z))
  exact (adj.leftAdjointUniq (constantSheafAdj (ProEt.topology X) D
    (hZ.isTerminalObj (proEtaleBaseChange f) Z))).app M

private noncomputable def relativeConstantEncoding (M : ModuleCat.{u + 1} A) :
    (relativeRestriction f A).obj
      ((proEtaleModuleInverseImage f (adicLisseConstantRing Y A)).obj
        ((adicLisseConstantModules Y A).obj M)) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M :=
  relativePullbackComparison f A _ ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapIso (constantEncoding Y A M) ≪≫
      constantPullback f A M

private noncomputable def relativeScalarUnit :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶
      ((adicLisseForget X).obj
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
          (adicLisseConstantRing Y A))).obj :=
  proEtaleModuleScalarUnit X A ≫
    Functor.whiskerRight (coefficientIso f A).inv.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private instance relativeScalarUnit_surjective :
    Presheaf.IsLocallySurjective (ProEt.topology X) (relativeScalarUnit f A) := by
  dsimp [relativeScalarUnit]
  infer_instance

private noncomputable def relativeOverRestriction (U : X.ProEt) :=
  ConstantScalarComparison.restriction ((ProEt.topology X).over U) A
    (((adicLisseForget X).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (adicLisseConstantRing Y A))).over U)
    (Functor.whiskerLeft (Over.forget U).op (relativeScalarUnit f A))

end CoefficientSerre

namespace CoefficientSerre
open ProEtale
variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]

private def fixedFiniteSieve
    {X : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) (W : X.ProEt) : Sieve W where
  arrows V _ := ∃ M : ModuleCat.{u + 1} A, Finite M ∧
    Nonempty (F.over V ≅ ((constantSheaf (ProEt.topology X)
      (ModuleCat.{u + 1} A)).obj M).over V)
  downward_closed := by
    rintro V W f ⟨M, hM, ⟨e⟩⟩ g
    let G := (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M
    exact ⟨M, hM, ⟨(F.pushforwardOverMapIso g).symm ≪≫
      ((ProEt.topology X).overMapPullback (ModuleCat.{u + 1} A) g).mapIso e ≪≫
        G.pushforwardOverMapIso g⟩⟩

private theorem fixedFiniteSieve_iff
    {X : Scheme.{u}} (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :
    fixedFiniteSieve A F (⊤_ X.ProEt) ∈ ProEt.topology X (⊤_ X.ProEt) ↔
      IsFiniteLocallyConstant A F := by
  let e : ProEt.mk (𝟙 X) ≅ ⊤_ X.ProEt :=
    (ProEt.isTerminalMkId X).uniqueUpToIso terminalIsTerminal
  have hmem : fixedFiniteSieve A F (⊤_ X.ProEt) ∈ ProEt.topology X (⊤_ X.ProEt) ↔
      fixedFiniteSieve A F (ProEt.mk (𝟙 X)) ∈ ProEt.topology X (ProEt.mk (𝟙 X)) := by
    change _ ↔ (fixedFiniteSieve A F (⊤_ X.ProEt)).pullback e.hom ∈ _
    exact GrothendieckTopology.pullback_mem_iff_of_isIso.symm
  rw [hmem]
  constructor
  · intro h
    obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.mp h
    obtain ⟨I, U, f, rfl⟩ := P.exists_eq_ofArrows
    have hcov : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        proetalePrecoverage X := by
      rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
      change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
        proetalePrecoverage X at hP
      have hw (i : I) : (f i).left = (U i).hom := by
        have hw := MorphismProperty.Over.w (f i)
        change (f i).left ≫ 𝟙 X = (U i).hom at hw
        exact (Category.comp_id _).symm.trans hw
      simpa only [hw] using hP
    refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hcov, fun i ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hPS _ _ ⟨i⟩
    let D := ModuleCat.{u + 1} A
    have : (ProEt.sliceEquiv X (U i)).inverse.IsDenseSubsite
        (ProEt.topology (U i).left) ((ProEt.topology X).over (U i)) :=
      ProEt.sliceDense X (U i)
    let E := (ProEt.sliceEquiv X (U i)).sheafCongr
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) D
    let r : E.functor.obj (F.over (U i)) ≅
        (localizationRestriction D (U i).hom (U i).prop).obj F :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    let c := ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left)
      D (Over.mkIdTerminal (X := U i))).app M
    exact ⟨M, Module.Finite.of_finite,
      ⟨(upperStarIsoLocalizationRestriction D (U i).hom (U i).prop).app F ≪≫
        r.symm ≪≫ E.functor.mapIso (e ≪≫
          ((ProEt.topology X).overPullbackConstantSheafIso D (U i)).app M) ≪≫ c⟩⟩
  · intro h
    obtain ⟨I, U, f, hf, he⟩ := finiteModels_over A F (by
      obtain ⟨ι, W, g, hg, h⟩ := h
      refine ⟨ι, W, g, hg, fun i ↦ ?_⟩
      obtain ⟨M, hM, e⟩ := h i
      exact ⟨M, Module.finite_of_finite A, e⟩)
    apply (ProEt.topology X).superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (Precoverage.generate_mem_toGrothendieck hf)
    rintro V g ⟨i⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := he i
    exact ⟨M, hM, ⟨e ≪≫
      (((ProEt.topology X).overPullbackConstantSheafIso (ModuleCat.{u + 1} A) (U i)).app M).symm⟩⟩

private theorem relative_finite_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : pbcModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (adicLisseConstantRing Y A))) :
    IsRelativelyFiniteLisseModule f A F ↔
      IsFiniteLocallyConstant A ((relativeRestriction f A).obj F) := by
  rw [← fixedFiniteSieve_iff]
  constructor
  · rintro ⟨S, hS, h⟩
    apply (ProEt.topology X).superset_covering _ hS
    intro V a ha
    obtain ⟨M, hM, ⟨e⟩⟩ := h V a ha
    exact ⟨M, hM, ⟨(relativeOverRestriction f A V).mapIso e ≪≫
      ((ProEt.topology X).overPullback (ModuleCat.{u + 1} A) V).mapIso
        (relativeConstantEncoding f A M)⟩⟩
  · intro h
    refine ⟨fixedFiniteSieve A ((relativeRestriction f A).obj F) (⊤_ X.ProEt), h, ?_⟩
    rintro V a ⟨M, hM, ⟨e⟩⟩
    have : Presheaf.IsLocallySurjective ((ProEt.topology X).over V)
        (Functor.whiskerLeft (Over.forget V).op (relativeScalarUnit f A)) :=
      Presheaf.isLocallySurjective_whisker ((ProEt.topology X).over V)
        (ProEt.topology X) (Over.forget V) _
    exact ⟨M, hM, ⟨(ConstantScalarComparison.restrictionFullyFaithful
      ((ProEt.topology X).over V) A
      (((adicLisseForget X).obj ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (adicLisseConstantRing Y A))).over V)
      (Functor.whiskerLeft (Over.forget V).op (relativeScalarUnit f A))).preimageIso
        (e ≪≫ (((ProEt.topology X).overPullback (ModuleCat.{u + 1} A) V).mapIso
          (relativeConstantEncoding f A M)).symm)⟩⟩

private theorem coefficient_constructible_iff
    (F : pbcModules T (adicLisseConstantRing T A)) :
    IsConstructibleProEtaleCoefficientModuleSheaf T A F ↔
      IsConstructible A ((proEtaleModuleRestriction T A).obj F) := by
  constructor
  · rintro ⟨S, hn, hc, hS⟩
    refine ⟨S, fun i ↦ ?_⟩
    exact isFiniteLocallyConstant_of_iso (relativePullbackComparison (S.immersion i) A F)
      ((relative_finite_iff (S.immersion i) A _).mp (hS i))
  · intro h
    obtain ⟨S, hn, hS⟩ := positive_stratification T A _ h
    refine ⟨S, hn, S.isConstructible_stratum, fun i ↦ ?_⟩
    exact (relative_finite_iff (S.immersion i) A _).mpr
      (isFiniteLocallyConstant_of_iso (relativePullbackComparison (S.immersion i) A F).symm
        (hS i))

private noncomputable instance restriction_equivalence :
    (proEtaleModuleRestriction T A).IsEquivalence := {}

private instance restriction_additive : (proEtaleModuleRestriction T A).Additive where
  map_add := by intros; rfl

private theorem fixed_reflects_constructible
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hG : IsConstructible A ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj G)) :
    IsConstructibleSheaf G := by
  obtain ⟨H, hH, ⟨e⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A hG
  have := hH
  exact IsConstructibleSheaf.of_iso
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).preimageIso e)

private theorem fixed_kernel_cokernel
    (F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) (f : F ⟶ G)
    (hF : IsConstructible A F) (hG : IsConstructible A G) :
    IsConstructible A (kernel f) ∧ IsConstructible A (cokernel f) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A hF
  obtain ⟨H, hH, ⟨e'⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A hG
  have := hE
  have := hH
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) T
  obtain ⟨g, hg⟩ := L.map_surjective (e.hom ≫ f ≫ e'.inv)
  have hw : L.map g ≫ e'.hom = e.hom ≫ f := by simp [hg]
  have := IsConstructibleSheaf.kernel g
  have := IsConstructibleSheaf.cokernel g
  exact ⟨isConstructible_of_iso (PreservesKernel.iso L g ≪≫
      kernel.mapIso (L.map g) f e e' hw)
      (isConstructible_comparisonUpperStar_obj (kernel g)),
    isConstructible_of_iso (PreservesCokernel.iso L g ≪≫
      cokernel.mapIso (L.map g) f e e' hw)
      (isConstructible_comparisonUpperStar_obj (cokernel g))⟩

private theorem fixed_extension
    (S : ShortComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)))
    (hS : S.ShortExact) (h₁ : IsConstructible A S.X₁)
    (h₃ : IsConstructible A S.X₃) : IsConstructible A S.X₂ := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := comparisonLowerStar (ModuleCat.{u + 1} A) T
  let adj := comparisonAdjunction (ModuleCat.{u + 1} A) T
  obtain ⟨E₁, hE₁, ⟨e₁⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A h₁
  obtain ⟨E₃, hE₃, ⟨e₃⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A h₃
  have h₂ := etaleOrigin_of_shortExact hS ⟨E₁, ⟨e₁⟩⟩ ⟨E₃, ⟨e₃⟩⟩
  have hc₁ : IsIso (adj.counit.app S.X₁) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr ⟨E₁, ⟨e₁⟩⟩
  have hc₂ : IsIso (adj.counit.app S.X₂) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr h₂
  have hc₃ : IsIso (adj.counit.app S.X₃) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr ⟨E₃, ⟨e₃⟩⟩
  let e : (S.map R).map L ≅ S := ShortComplex.isoMk
    (asIso (adj.counit.app S.X₁)) (asIso (adj.counit.app S.X₂))
    (asIso (adj.counit.app S.X₃)) (adj.counit.naturality S.f).symm
    (adj.counit.naturality S.g).symm
  have he : ((S.map R).map L).ShortExact := (ShortComplex.shortExact_iff_of_iso e).mpr hS
  have hR := ShortExact.reflects_shortExact_of_faithful L he
  have hR₁ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} A ↦ M →ₗ[A] N)
      (CA := fun M : ModuleCat.{u + 1} A ↦ M) (R.obj S.X₁) := fixed_reflects_constructible T A _
    (isConstructible_of_iso (asIso (adj.counit.app S.X₁)).symm h₁)
  have hR₃ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} A ↦ M →ₗ[A] N)
      (CA := fun M : ModuleCat.{u + 1} A ↦ M) (R.obj S.X₃) := fixed_reflects_constructible T A _
    (isConstructible_of_iso (asIso (adj.counit.app S.X₃)).symm h₃)
  have hR₁' : IsConstructibleSheaf (S.map R).X₁ := hR₁
  have hR₃' : IsConstructibleSheaf (S.map R).X₃ := hR₃
  have hR₂ : IsConstructibleSheaf (R.obj S.X₂) := IsConstructibleSheaf.of_shortExact hR
  exact isConstructible_of_iso (asIso (adj.counit.app S.X₂))
    (isConstructible_comparisonUpperStar_obj (R.obj S.X₂))

private theorem closure :
    (∀ (F G : pbcModules T (adicLisseConstantRing T A)) (f : F ⟶ G),
      IsConstructibleProEtaleCoefficientModuleSheaf T A F →
      IsConstructibleProEtaleCoefficientModuleSheaf T A G →
      IsConstructibleProEtaleCoefficientModuleSheaf T A (kernel f) ∧
        IsConstructibleProEtaleCoefficientModuleSheaf T A (cokernel f)) ∧
    (∀ S : ShortComplex (pbcModules T (adicLisseConstantRing T A)),
      S.ShortExact → IsConstructibleProEtaleCoefficientModuleSheaf T A S.X₁ →
      IsConstructibleProEtaleCoefficientModuleSheaf T A S.X₃ →
      IsConstructibleProEtaleCoefficientModuleSheaf T A S.X₂) := by
  let F := proEtaleModuleRestriction T A
  constructor
  · intro M N f hM hN
    obtain ⟨hk, hc⟩ := fixed_kernel_cokernel T A (F.obj M) (F.obj N) (F.map f)
      ((coefficient_constructible_iff T A M).mp hM)
      ((coefficient_constructible_iff T A N).mp hN)
    exact ⟨(coefficient_constructible_iff T A _).mpr
        (isConstructible_of_iso (PreservesKernel.iso F f).symm hk),
      (coefficient_constructible_iff T A _).mpr
        (isConstructible_of_iso (PreservesCokernel.iso F f).symm hc)⟩
  · intro S hS h₁ h₃
    exact (coefficient_constructible_iff T A _).mpr
      (fixed_extension T A (S.map F) (hS.map_of_exact F)
        ((coefficient_constructible_iff T A _).mp h₁)
        ((coefficient_constructible_iff T A _).mp h₃))

end CoefficientSerre

/-- Intrinsically constructible coefficient-module sheaves are closed under kernels,
cokernels and extensions for the canonical constant-ring presentation.
Source: Stacks Tags 09B5 and 093U(3), with the global finite partitions of Tag 03RZ
(blueprint: lem-weil-constructible-coefficient-serre).
Proof: restriction to the canonical constant sections identifies modules over the
constant ring sheaf with sheaves of ordinary coefficient modules. The sheafification
adjunction gives full faithfulness and essential surjectivity. Uniqueness of left
adjoints identifies this encoding with inverse image, including on slices and on
constant modules. A terminal covering sieve of finite constant models is equivalent
to finite local constancy, hence the encoding preserves and reflects constructibility.
For kernels and cokernels choose constructible etale origins, lift the morphism by
full faithfulness, and apply etale constructible Serre closure; exact comparison
identifies their kernels and cokernels. For extensions, the existing origin theorem
makes the middle sheaf an etale comparison object. The comparison counit identifies
the whole short complex with the comparison of its direct image. Faithful exact
comparison reflects short exactness, so etale Serre closure applies to the middle
term. Transport these three closure assertions through the encoding equivalence.
Positive stratifications include the empty scheme, and zero coefficients are allowed. -/
theorem constructibleCoefficient_exactClosure
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    (∀ (F G : pbcModules T (adicLisseConstantRing T A)) (f : F ⟶ G),
      IsConstructibleProEtaleCoefficientModuleSheaf T A F →
      IsConstructibleProEtaleCoefficientModuleSheaf T A G →
      IsConstructibleProEtaleCoefficientModuleSheaf T A (kernel f) ∧
        IsConstructibleProEtaleCoefficientModuleSheaf T A (cokernel f)) ∧
    (∀ S : ShortComplex (pbcModules T (adicLisseConstantRing T A)),
      S.ShortExact → IsConstructibleProEtaleCoefficientModuleSheaf T A S.X₁ →
      IsConstructibleProEtaleCoefficientModuleSheaf T A S.X₃ →
      IsConstructibleProEtaleCoefficientModuleSheaf T A S.X₂) := by
  exact CoefficientSerre.closure T A

end AlgebraicGeometry.Scheme
