/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import all WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.CochainCompositeConstruction.CochainCompositeAlgebraic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.DerivedPullbackRepresentativeComputationSupplement
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Construction of open operation models -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryOpenExtension_exists {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology .ordinary X) CommRingCat.{u + 1}) :
    Nonempty (OpenExtension .ordinary j R) := by
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} U.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  let W : X.ProEt := ProEt.mk j
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let e := ProEt.sliceEquiv X W
  have : e.inverse.IsDenseSubsite (ProEt.topology U) ((ProEt.topology X).over W) :=
    ProEt.sliceDense X W
  let B := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing .ordinary j R)
  let c : B ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U) ((ProEt.topology X).over W)).obj (A.over W) := Iso.refl _
  obtain ⟨q, hq⟩ := ProEt.module_transport.{u} ((ProEt.topology X).over W)
    (ProEt.topology U) e (A.over W) B c
  let E : SheafOfModules.{u + 1} (A.over W) ⥤ SheafOfModules.{u + 1} A :=
    SheafOfModules.extensionByZeroPresheaf.{u + 1, u, u + 1, u + 1} A W ⋙
    PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} (𝟙 A.obj)
  let a₀ : E ⊣ overFunctor.{u + 1, u, u + 1, u + 1} A W :=
    SheafOfModules.extensionSheafAdjunction.{u} A W
  let L := q.inverse ⋙ E
  let a : L ⊣ restrict .ordinary j R :=
    (q.symm.toAdjunction.comp a₀).ofNatIsoRight (by
      apply Functor.fullyFaithfulCancelRight (forget B)
      change overFunctor.{u + 1, u, u + 1, u + 1} A W ⋙ q.functor ⋙ forget B ≅
        restrict .ordinary j R ⋙ forget B
      rw [hq]
      refine NatIso.ofComponents (fun M ↦ ?_) ?_
      · exact PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl)
      · intro M N f
        ext V x
        rfl)
  have hW (V : X.ProEt) : Subsingleton (V ⟶ W) := by
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).mp
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  have hE : PreservesFiniteLimits E := by
    have := extensionPresheaf_preservesFiniteLimits.{u} A W hW
    dsimp only [E]
    exact comp_preservesFiniteLimits _ _
  have hL : PreservesFiniteLimits L := by
    dsimp only [L]
    exact comp_preservesFiniteLimits _ _
  have : L.IsLeftAdjoint := a.isLeftAdjoint
  have : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
  have hAdd : L.Additive := a.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} L := a.leftAdjoint_preservesColimits
  have hunit (M : SheafOfModules.{u + 1} (A.over W)) :
      IsIso (a₀.unit.app M) := extensionSheafAdjunction_unit_isIso.{u} A W hW M
  have : IsIso a₀.unit := NatIso.isIso_of_isIso_app _
  let ff := a₀.fullyFaithfulLOfIsIsoUnit
  have : E.Full := ff.full
  have : E.Faithful := ff.faithful
  have : L.Full := by dsimp only [L]; infer_instance
  have : L.Faithful := by dsimp only [L]; infer_instance
  have hη (M : Mod (restrictRing .ordinary j R)) : IsIso (a.unit.app M) :=
    have := a.unit_isIso_of_L_fully_faithful
    inferInstance
  exact ⟨{
    ordinary := L
    adjunction := a
    sectionIso := fun M ↦ (asIso (a.unit.app M)).symm
    sectionUnit := fun M ↦ IsIso.hom_inv_id (a.unit.app M)
    additive := hAdd
    limits := hL
    colimits := PreservesColimitsOfSize.preservesFiniteColimits L
  }⟩

/- The adopted module-adjunction API equates the site hom universe and coefficient
universe. Here the site has objects in Type (u+1), homs in Type u, and coefficients
in Type (u+1). The following private helpers prove the same adjunction by its
sectionwise universal property at these universes; no public interface changes. -/
namespace GeneralizedRinged

open MonoidalCategory
open SheafOfModules.GeometricConstruction
open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option maxErrors 20

section
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : D ⥤ C) [F.IsContinuous K J]
  (L : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
  (adj : L ⊣ F.sheafPushforwardContinuous (Type (u + 1)) K J)

private def directPair {X Y : Sheaf J (Type (u + 1))} {T : Sheaf K (Type (u + 1))}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj Y) :
    T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj (X ⊗ Y) :=
  ⟨{ app U := ↾(fun t ↦ (x.hom.app U t, y.hom.app U t))
     naturality := by
       intro U V f
       ext t
       change (x.hom.app V (T.obj.map f t), y.hom.app V (T.obj.map f t)) =
         (X.obj.map (F.op.map f) (x.hom.app U t),
           Y.obj.map (F.op.map f) (y.hom.app U t))
       exact Prod.ext (CategoryTheory.congr_fun (x.hom.naturality f) t)
         (CategoryTheory.congr_fun (y.hom.naturality f) t) }⟩

private theorem transpose_pair {X Y : Sheaf J (Type (u + 1))} {T : Sheaf K (Type (u + 1))}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj Y) :
    (adj.homEquiv T (X ⊗ Y)).symm (directPair F x y) =
      CartesianMonoidalCategory.lift ((adj.homEquiv T X).symm x)
        ((adj.homEquiv T Y).symm y) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst, ← adj.homEquiv_naturality_right_symm]
    rfl
  · rw [CartesianMonoidalCategory.lift_snd, ← adj.homEquiv_naturality_right_symm]
    rfl

private theorem transpose_binary
    {X Y Z : Sheaf J (Type (u + 1))} {T : Sheaf K (Type (u + 1))} (op : X ⊗ Y ⟶ Z)
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj Y)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj Z)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U)
      (x.hom.app U t, y.hom.app U t)) :
    ∀ U t, ((adj.homEquiv T Z).symm z).hom.app U t =
      op.hom.app U (((adj.homEquiv T X).symm x).hom.app U t,
        ((adj.homEquiv T Y).symm y).hom.app U t) := by
  have he : z = directPair F x y ≫
      (F.sheafPushforwardContinuous (Type (u + 1)) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm, transpose_pair F L adj]
  intro U t
  rfl

private theorem transpose_constant
    {X : Sheaf J (Type (u + 1))} {T : Sheaf K (Type (u + 1))}
    (op : 𝟙_ (Sheaf J (Type (u + 1))) ⟶ X)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj X)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U) PUnit.unit) :
    ∀ U t, ((adj.homEquiv T X).symm z).hom.app U t = op.hom.app U PUnit.unit := by
  let w : T ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj (𝟙_ _) :=
    ⟨{ app U := ↾(fun _ ↦ PUnit.unit) }⟩
  have he : z = w ≫ (F.sheafPushforwardContinuous (Type (u + 1)) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm]
  intro U t
  change op.hom.app U _ = _
  congr 1

private theorem siteStructuralMap_exists
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R)
    (RI : Sheaf J CommRingCat.{u + 1}) (I : AlgebraicInverseImage L S RI) :
    ∃ c : RI ⟶ R, (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset S) (rset R)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ) := by
  let φs : rset S ⟶ (F.sheafPushforwardContinuous (Type (u + 1)) K J).obj (rset R) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ
  let g := (adj.homEquiv (rset S) (rset R)).symm φs
  refine SheafOfModules.CochainCompositeConstruction.structuralMap L S R RI I g ?_ ?_ ?_
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Add.add (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (SheafOfModules.GeometricConstruction.ringAdd R)
      (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') + (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') + (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_add _ _)
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Mul.mul (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (SheafOfModules.GeometricConstruction.ringMul R)
      (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') * (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') * (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_mul _ _)
  · intro T z hz U t
    change T ⟶ rset S at z
    change ((L.map z) ≫ g).hom.app U t = (1 : R.obj.obj U)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm]
    apply transpose_constant F L adj (ringOne R) (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 1
    have h : (show S.obj.obj V from z.hom.app V x) = 1 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_one

end
private noncomputable abbrev tensorFunctor
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :=
  CategoryTheory.CochainPullback.extensionFunctor (J := K) (A := A) (B := S) c

private noncomputable abbrev tensorAdjunction
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :=
  CategoryTheory.CochainPullback.extensionAdjunction (J := K) (A := A) (B := S) c

open SheafOfModules.GeometricConstruction
private theorem pushforward_operations
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (A : Sheaf J CommRingCat.{u + 1}) (B : Sheaf K CommRingCat.{u + 1})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj A)
    (H : Mod A) :
    let V := F.sheafPushforwardContinuous (Type (u + 1)) K J
    let P := SheafOfModules.pushforward.{u + 1} (F := F)
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
    let X := (mset A).obj H
    V.map (CategoryTheory.CochainPullback.moduleAddMap A H) =
      prodComparison V X X ≫ CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) := by
  dsimp only
  let V := F.sheafPushforwardContinuous (Type (u + 1)) K J
  let X := (mset A).obj H
  ext U p
  let : Add (X.obj.obj (F.op.obj U)) :=
    (inferInstance : Add (H.val.obj (F.op.obj U)))
  let : Add ((V.obj X).obj.obj U) :=
    (inferInstance : Add (H.val.obj (F.op.obj U)))
  have hf := congrArg (fun f ↦ f.hom.app U p) (prodComparison_fst V X X)
  have hs := congrArg (fun f ↦ f.hom.app U p) (prodComparison_snd V X X)
  change (prod.fst : X ⨯ X ⟶ X).hom.app (F.op.obj U) p +
      (prod.snd : X ⨯ X ⟶ X).hom.app (F.op.obj U) p =
    (prod.fst : V.obj X ⨯ V.obj X ⟶ V.obj X).hom.app U
      ((prodComparison V X X).hom.app U p) +
    (prod.snd : V.obj X ⨯ V.obj X ⟶ V.obj X).hom.app U
      ((prodComparison V X X).hom.app U p)
  exact congrArg₂ (fun x y ↦ x + y) hf.symm hs.symm

private theorem pushforward_action
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (A : Sheaf J CommRingCat.{u + 1}) (B : Sheaf K CommRingCat.{u + 1})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj A)
    (H : Mod A) :
    let V := F.sheafPushforwardContinuous (Type (u + 1)) K J
    let P := SheafOfModules.pushforward.{u + 1} (F := F)
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
    let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ
    let X := (mset A).obj H
    CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) =
      prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) X) ≫
        V.map (CategoryTheory.CochainPullback.moduleSMulMap A H) := by
  dsimp only
  let V := F.sheafPushforwardContinuous (Type (u + 1)) K J
  let X := (mset A).obj H
  let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ
  have : PreservesLimits V := by dsimp only [V]; infer_instance
  ext U p
  let q := (prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) X)).hom.app U p
  have hf := congrArg (fun f ↦ f.hom.app U p)
    (show prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) X) ≫
        V.map prod.fst = prod.fst ≫ φs by
      rw [inv_prodComparison_map_fst, prod.map_fst])
  have hs := congrArg (fun f ↦ f.hom.app U p)
    (show prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) X) ≫
        V.map prod.snd = prod.snd by
      rw [inv_prodComparison_map_snd, prod.map_snd, Category.comp_id])
  let smul : A.obj.obj (F.op.obj U) → H.val.obj (F.op.obj U) →
      H.val.obj (F.op.obj U) := fun a x ↦ a • x
  change smul ((φ.hom.app U).hom
      ((prod.fst : rset B ⨯ V.obj X ⟶ rset B).hom.app U p))
      ((prod.snd : rset B ⨯ V.obj X ⟶ V.obj X).hom.app U p) =
    smul ((prod.fst : rset A ⨯ X ⟶ rset A).hom.app (F.op.obj U) q)
      ((prod.snd : rset A ⨯ X ⟶ X).hom.app (F.op.obj U) q)
  exact congrArg₂ smul hf.symm hs.symm

-- Prove naturality before specializing to the concrete sheaf functors: unfolding
-- their underlying module constructions during categorical rewrites is expensive.
private theorem adjunctionOfLinearMates
    {C₀ D₀ E₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category E₀] [Category C₁] [Category D₁]
    (I : C₀ ⥤ D₀) (T : D₀ ⥤ E₀) (S : E₀ ⥤ D₀) (aT : T ⊣ S)
    (P : E₀ ⥤ C₀) (U : C₀ ⥤ C₁) [U.Faithful] (W : D₀ ⥤ D₁) (Z : E₀ ⥤ D₁)
    (L : C₁ ⥤ D₁) (V : D₁ ⥤ C₁) (adj : L ⊣ V)
    (i : I ⋙ W ≅ U ⋙ L) (s : S ⋙ W ≅ Z) (p : P ⋙ U ≅ Z ⋙ V)
    (E : ∀ M H, (I.obj M ⟶ S.obj H) ≃ (M ⟶ P.obj H))
    (hE : ∀ M H a, U.map (E M H a) ≫ p.hom.app H =
      adj.homEquiv _ _ (i.inv.app M ≫ W.map a ≫ s.hom.app H)) :
    Nonempty (I ⋙ T ⊣ P) := by
  have hBL {M N} (a : M ⟶ N) H b :
      E M H (I.map a ≫ b) = a ≫ E N H b := by
    apply U.map_injective
    apply (cancel_mono (p.hom.app H)).mp
    rw [U.map_comp, Category.assoc, hE, hE, ← adj.homEquiv_naturality_left]
    congr 1
    have hn : i.inv.app M ≫ W.map (I.map a) =
        L.map (U.map a) ≫ i.inv.app N := (i.inv.naturality a).symm
    simp only [W.map_comp, Category.assoc]
    rw [← Category.assoc (i.inv.app M), hn, Category.assoc]
  have hBR M {H H'} a (b : H ⟶ H') :
      E M H' (a ≫ S.map b) = E M H a ≫ P.map b := by
    apply U.map_injective
    apply (cancel_mono (p.hom.app H')).mp
    rw [U.map_comp, Category.assoc]
    have hp : U.map (P.map b) ≫ p.hom.app H' =
        p.hom.app H ≫ V.map (Z.map b) := p.hom.naturality b
    rw [hp, ← Category.assoc, hE, hE, ← adj.homEquiv_naturality_right]
    congr 1
    simp only [W.map_comp, Category.assoc]
    exact congrArg (fun f ↦ i.inv.app M ≫ W.map a ≫ f) (s.hom.naturality b)
  let E' : ∀ M H, ((I ⋙ T).obj M ⟶ H) ≃ (M ⟶ P.obj H) :=
    fun M H ↦ (aT.homEquiv (I.obj M) H).trans (E M H)
  have hEL {M N} (a : M ⟶ N) H (b : (I ⋙ T).obj N ⟶ H) :
      E' M H ((I ⋙ T).map a ≫ b) = a ≫ E' N H b :=
    (congrArg (E M H) (aT.homEquiv_naturality_left (I.map a) b)).trans
      (hBL a H (aT.homEquiv (I.obj N) H b))
  exact ⟨Adjunction.mkOfHomEquiv {
    homEquiv := E'
    homEquiv_naturality_left_symm := by
      intro M N H a b
      apply (E' M H).injective
      rw [Equiv.apply_symm_apply, hEL, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M H H' a b
      exact (congrArg (E M H') (aT.homEquiv_naturality_right a b)).trans
        (hBR M (aT.homEquiv (I.obj M) H a) b) }⟩

-- Elaborate the sectionwise adjunction and its transported coefficient identities.
-- Restricting the adjunction to linear maps elaborates several large sheaf diagrams.
private theorem supplied_adjunction
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (u + 1)) K J)
    [PreservesFiniteLimits L]
    (A : Sheaf J CommRingCat.{u + 1}) (B : Sheaf K CommRingCat.{u + 1})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj A)
    (RI : Sheaf J CommRingCat.{u + 1}) (I : AlgebraicInverseImage L B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset B) (rset A)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ)) :
    Nonempty (I.modules ⋙ tensorFunctor c ⊣
      SheafOfModules.pushforward.{u + 1} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)) := by
  let V := F.sheafPushforwardContinuous (Type (u + 1)) K J
  let P := SheafOfModules.pushforward.{u + 1} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
    ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
  let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ
  have : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let eI := I.moduleUnderlying
  obtain ⟨L₀, hobj₀, hmap₀, V₀, ⟨a₀⟩, hAdd₀⟩ :=
    CategoryTheory.CochainPullback.ringedPullbackPresentation_exists
      (R := B) (S := A) L V adj RI I c
  let p : CategoryTheory.CochainPullback.RingedPullback.{u + 1, u + 1, u, u + 1, u}
      (J := K) (K := J) B A := {
    uInv := L, uPush := V, adj := adj, finiteLimits := inferInstance,
    RI := RI, I := I, coefficient := c, L := L₀, hobj := hobj₀, hmap := hmap₀,
    V := V₀, moduleAdj := a₀, additive := hAdd₀ }
  have hp : CategoryTheory.CochainPullback.structureMap p =
      (adj.homEquiv _ _).symm φs := by
    change I.ringUnderlying.hom ≫ _ = _
    rw [hc]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  have hEquiv (M : Mod B) (H : Mod A) :
      ∃ E : (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)).obj H) ≃ (M ⟶ P.obj H),
        ∀ a, (mset B).map (E a) =
          adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    have ha : CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) ≫ (𝟙 _) =
        prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
          V.map (CategoryTheory.CochainPullback.moduleAddMap A H) := by
      simp only [Category.comp_id, prod.map_id_id, Category.id_comp]
      apply (cancel_epi (prodComparison V ((mset A).obj H) ((mset A).obj H))).mp
      simpa only [IsIso.hom_inv_id_assoc] using (pushforward_operations F A B φ H).symm
    have hs : CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) =
        prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) ((mset A).obj H)) ≫
          V.map (CategoryTheory.CochainPullback.moduleSMulMap A H) :=
      pushforward_action F A B φ H
    have hg : adj.homEquiv _ _ (CategoryTheory.CochainPullback.structureMap p) = φs := by
      rw [hp, Equiv.apply_symm_apply]
    rw [← hg] at hs
    obtain ⟨E, hE⟩ := CategoryTheory.CochainPullback.linearMate_exists p H (P.obj H)
      (Iso.refl _) ha (by
        simp only [Iso.refl_hom, Category.comp_id]
        convert hs using 1 <;> rfl) M
    exact ⟨E, fun a ↦ by simpa only [Iso.refl_hom, Category.comp_id] using hE a⟩
  choose B' hB using hEquiv
  apply adjunctionOfLinearMates I.modules (tensorFunctor c)
    (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)) (tensorAdjunction c)
    P (mset B) (mset RI) (mset A) L V adj eI
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) B'
  intro M H a
  change (mset B).map (B' M H a) ≫ 𝟙 _ =
    adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a ≫ 𝟙 _)
  rw [Category.comp_id, Category.comp_id]
  exact hB M H a

end GeneralizedRinged

open CategoryTheory.Functor MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictionInverse {m : Mode} {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    AlgebraicInverseImage
      ((openInclusion m j).sheafPushforwardContinuous (Type (u + 1))
        (topology m U) (topology m X)) R (restrictRing m j R) where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h V x ↦ h ((openInclusion m j).op.obj V) x
  ringMul := fun _ _ _ _ h V x ↦ h ((openInclusion m j).op.obj V) x
  ringZero := fun _ _ h V x ↦ h ((openInclusion m j).op.obj V) x
  ringOne := fun _ _ h V x ↦ h ((openInclusion m j).op.obj V) x
  modules := restrict m j R
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h V x ↦ h ((openInclusion m j).op.obj V) x
  moduleZero := fun _ _ _ h V x ↦ h ((openInclusion m j).op.obj V) x
  moduleSMul := fun _ _ _ _ _ h V x ↦ h ((openInclusion m j).op.obj V) x

set_option backward.isDefEq.respectTransparency false in
private noncomputable def openSiteAdjunction (m : Mode) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : openInclusion m j ⊣ baseChange m j := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  cases m with
  | ordinary => exact a
  | systems => exact systemAdjunction a

set_option backward.isDefEq.respectTransparency false in
private noncomputable def openRightCoefficient (m : Mode) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    R ⟶ ((baseChange m j).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m X) (topology m U)).obj (restrictRing m j R) :=
  ((openSiteAdjunction m j).sheafPushforwardContinuous
    (E := CommRingCat.{u + 1}) (topology m U) (topology m X)).unit.app R

set_option backward.isDefEq.respectTransparency false in
private noncomputable def openRestrictionAdjunction (m : Mode) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    restrict m j R ⊣ direct m j R (restrictRing m j R) (openRightCoefficient m j R) := by
  let a := openSiteAdjunction m j
  let A := (sheafCompose (topology m X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let ψ : A ⟶ ((baseChange m j).sheafPushforwardContinuous RingCat.{u + 1}
      (topology m X) (topology m U)).obj
      ((sheafCompose (topology m U)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing m j R)) :=
    ⟨Functor.whiskerRight (NatTrans.op a.counit) A.obj⟩
  exact SheafOfModules.pushforwardPushforwardAdj a (𝟙 _) ψ
    (by ext W : 2; exact (Category.comp_id _).symm)
    (by
      ext W : 2
      change A.obj.map (a.counit.app ((openInclusion m j).obj W.unop)).op ≫
        A.obj.map ((openInclusion m j).map (a.unit.app W.unop)).op = 𝟙 _
      rw [← A.obj.map_comp, ← op_comp]
      exact (congrArg (fun f ↦ A.obj.map f.op)
        (a.left_triangle_components W.unop)).trans (A.obj.map_id _))

namespace SystemPresentation
open WeilConjectures WeilConjectures.SemilinearSections

set_option backward.isDefEq.respectTransparency false

private def levels {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) CommRingCat.{u + 1}) :
    ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u + 1} where
  obj n :=
    letI : (Prod.sectR n.unop C).IsContinuous J (coefficientSequenceTopology J) :=
      evaluationContinuous.{u + 1, u, u + 1} J n.unop
    ((Prod.sectR n.unop C).sheafPushforwardContinuous
      CommRingCat.{u + 1} J (coefficientSequenceTopology J)).obj R
  map {n m} a := ⟨{
    app W := R.obj.map (Prod.mkHom a.unop (𝟙 W.unop)).op
    naturality := by
      intro V W b
      change R.obj.map _ ≫ R.obj.map _ = R.obj.map _ ≫ R.obj.map _
      rw [← R.obj.map_comp, ← R.obj.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      ext <;> simp
  }⟩
  map_id n := by
    ext W x
    change R.obj.map (𝟙 (op (n.unop, W.unop))) x = x
    rw [R.obj.map_id]
    rfl
  map_comp a b := by
    ext W x
    change R.obj.map _ x = (R.obj.map _ ≫ R.obj.map _) x
    rw [← R.obj.map_comp]
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext <;> simp

private theorem systemRing_presentation {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) CommRingCat.{u + 1}) :
    ∃ (B : ℕ → Sheaf J CommRingCat.{u + 1}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n),
      systemRing.{u + 1, u, u + 1} J B τ = R := by
  let B := fun n : ℕ ↦ (levels J R).obj (op n)
  let τ := fun n : ℕ ↦ (levels J R).map (homOfLE (Nat.le_succ n)).op
  let cmp : rings.{u + 1, u, u + 1} J B τ ⟶ levels J R :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [rings, Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp, Category.comp_id]
      rfl)
  refine ⟨B, τ, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro X Y f
  apply heq_of_eq
  have hh := cmp.naturality (f.unop.1).op
  simp only [cmp, NatTrans.ofOpSequence_app, Category.id_comp, Category.comp_id] at hh
  change (((rings J B τ).map (f.unop.1).op).hom.app (op X.unop.2) ≫
    R.obj.map (Prod.mkHom (𝟙 _) f.unop.2).op) = R.obj.map f
  rw [hh]
  change R.obj.map _ ≫ R.obj.map _ = R.obj.map f
  rw [← R.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext <;> simp

end SystemPresentation

namespace SystemPresentation
open WeilConjectures WeilConjectures.SemilinearSections

set_option backward.isDefEq.respectTransparency false

private theorem localizedUnit_isIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1}) (W : C)
    (hW : ∀ V : C, Subsingleton (V ⟶ W))
    (M : SheafOfModules.{u + 1}
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over W)) :
    IsIso ((localizedSystemAdjunction.{u + 1, u, 0} R W).unit.app M) := by
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let a₀ := SheafOfModules.extensionSheafAdjunction.{u} A W
  have hunit (N : SheafOfModules.{u + 1} (A.over W)) : IsIso (a₀.unit.app N) :=
    extensionSheafAdjunction_unit_isIso.{u} A W hW N
  have : IsIso a₀.unit := NatIso.isIso_of_isIso_app _
  let ff := a₀.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let a := localizedSystemAdjunction.{u + 1, u, 0} R W
  have : (localizedSystemExtension.{u + 1, u, 0} R W).Full := ff.full
  have : (localizedSystemExtension.{u + 1, u, 0} R W).Faithful := ff.faithful
  have := a.unit_isIso_of_L_fully_faithful
  infer_instance

end SystemPresentation

set_option backward.isDefEq.respectTransparency false in
private theorem moduleTransport
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.inverse.IsContinuous K J] [e.functor.IsContinuous J K]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R) :
    ∃ q : SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} S,
      q.functor ⋙ SheafOfModules.forget _ =
        SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward (F := e.inverse) c.hom.hom := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  refine ⟨SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem sequenceContinuous
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] :
    ((𝟭 ℕ).prod F).IsContinuous (WeilConjectures.coefficientSequenceTopology J)
      (WeilConjectures.coefficientSequenceTopology K) := by
  constructor
  intro G
  apply (verticalSheaf_iff C J _).2
  intro n
  have hG := (verticalSheaf_iff D K G.obj).1
    ((isSheaf_iff_isSheaf_of_type _ _).1 G.property) n
  exact F.op_comp_isSheaf_of_isSheaf_type J hG

namespace SystemPresentation
open WeilConjectures WeilConjectures.SemilinearSections
set_option backward.isDefEq.respectTransparency false

private theorem pushforward_section_isIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {R : Sheaf K RingCat.{u + 1}} {S : Sheaf J RingCat.{u + 1}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    {M N : SheafOfModules.{u + 1} R} (a : M ⟶ N)
    [IsIso ((SheafOfModules.pushforward.{u + 1} φ).map a)] (W : Cᵒᵖ) :
    IsIso (((PresheafOfModules.toPresheaf R.obj).map a.val).app (F.op.obj W)) := by
  let E := SheafOfModules.evaluation.{u + 1} S W ⋙
    forget₂ (ModuleCat (S.obj.obj W)) AddCommGrpCat
  have : IsIso (E.map ((SheafOfModules.pushforward.{u + 1} φ).map a)) := by
    infer_instance
  exact this

private theorem evaluation_reflects_isIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (B : ℕ → Sheaf J CommRingCat.{u + 1}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    {M N : Systems.{u + 1, u, u + 1} J B τ} (a : M ⟶ N)
    (h : ∀ n : ℕ,
      IsIso ((WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1} J B τ n).map a)) :
    IsIso a := by
  let A := ring.{u + 1, u, u + 1} (coefficientSequenceTopology J)
    (systemRing.{u + 1, u, u + 1} J B τ)
  let F := SheafOfModules.forget A ⋙ PresheafOfModules.toPresheaf A.obj
  have (W : (ℕ × C)ᵒᵖ) : IsIso ((F.map a).app W) := by
    let φ := eqToHom (evaluation_ring.{u + 1, u, u + 1} J B τ W.unop.1).symm
    have : IsIso ((SheafOfModules.pushforward.{u + 1}
        (F := Prod.sectR W.unop.1 C) φ).map a) := h W.unop.1
    exact pushforward_section_isIso (F := Prod.sectR W.unop.1 C)
      φ a (op W.unop.2)
  have : IsIso (F.map a) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso a F

private theorem systemUnit_isIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (B : ℕ → Sheaf J CommRingCat.{u + 1}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (W : C) (hW : ∀ V : C, Subsingleton (V ⟶ W))
    (o : OpenSystems.{u + 1, u, 0} J B τ W)
    (M : Systems.{u + 1, u, u + 1} (J.over W)
      (openRings.{u + 1, u, 0} J B W) (openTransitions.{u + 1, u, 0} J B τ W)) :
    IsIso (o.ordinaryAdjunction.unit.app M) := by
  apply evaluation_reflects_isIso (J.over W)
    (openRings.{u + 1, u, 0} J B W) (openTransitions.{u + 1, u, 0} J B τ W)
  intro n
  let E := WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1} (J.over W)
    (openRings.{u + 1, u, 0} J B W) (openTransitions.{u + 1, u, 0} J B τ W) n
  let b := (o.restrictionEvaluation n).hom.app (o.extension.obj M)
  let c := (localizedSystemRestriction.{u + 1, u, 0} (B n) W).map
    ((o.extensionEvaluation n).hom.app M)
  have : IsIso (E.map (o.ordinaryAdjunction.unit.app M) ≫ b ≫ c) := by
    change IsIso (_ ≫ (o.restrictionEvaluation n).hom.app _ ≫
      (localizedSystemRestriction.{u + 1, u, 0} (B n) W).map _)
    rw [o.unit_evaluation]
    exact localizedUnit_isIso (B n) W hW (E.obj M)
  exact IsIso.of_isIso_comp_right (E.map (o.ordinaryAdjunction.unit.app M)) (b ≫ c)

end SystemPresentation

private theorem pushforward_forget
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {R : Sheaf K RingCat.{u + 1}} {S : Sheaf J RingCat.{u + 1}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R) :
    SheafOfModules.pushforward.{u + 1} φ ⋙ forget S =
      forget R ⋙ PresheafOfModules.pushforward.{u + 1} φ.hom := rfl

private theorem pushedRingIso_cancel
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {A B : Sheaf K RingCat.{u + 1}} (c : A ≅ B)
    {S : Sheaf J RingCat.{u + 1}}
    (cS : S ≅ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj A) :
    (cS ≪≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).mapIso c).hom.hom ≫
      Functor.whiskerLeft F.op c.inv.hom = cS.hom.hom := by
  change (cS.hom.hom ≫ Functor.whiskerLeft F.op c.hom.hom) ≫
    Functor.whiskerLeft F.op c.inv.hom = cS.hom.hom
  rw [Category.assoc, ← Functor.whiskerLeft_comp]
  have hh : c.hom.hom ≫ c.inv.hom = 𝟙 A.obj :=
    congrArg (fun f : A ⟶ A ↦ f.hom) c.hom_inv_id
  rw [hh]
  exact Category.comp_id _

@[irreducible] private noncomputable def pushforwardCompOfEq
    {C D E : Type (u + 1)} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {R : Eᵒᵖ ⥤ RingCat.{u + 1}} {S : Dᵒᵖ ⥤ RingCat.{u + 1}}
    {T : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (φ : T ⟶ F.op ⋙ S) (ψ : S ⟶ G.op ⋙ R)
    (χ : T ⟶ (F ⋙ G).op ⋙ R) (h : φ ≫ Functor.whiskerLeft F.op ψ = χ) :
    PresheafOfModules.pushforward.{u + 1} ψ ⋙ PresheafOfModules.pushforward.{u + 1} φ ≅
      PresheafOfModules.pushforward.{u + 1} χ :=
  PresheafOfModules.pushforwardComp φ ψ ≪≫
    eqToIso (congrArg (fun f ↦ PresheafOfModules.pushforward.{u + 1} f) h)

open WeilConjectures WeilConjectures.SemilinearSections in
set_option backward.isDefEq.respectTransparency false in
-- Elaborate the sectionwise adjunction and its transported coefficient identities.
private theorem systemsOpenExtension_exists {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology .systems X) CommRingCat.{u + 1}) :
    Nonempty (OpenExtension .systems j R) := by
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} U.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
    essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} (ℕ × U.ProEt) :=
    essentiallySmallSelf.{0, u, u + 1} _
  let J := ProEt.topology X
  have hX : topology .systems X = coefficientSequenceTopology J := topology_systems_eq X
  have hU : topology .systems U = coefficientSequenceTopology (ProEt.topology U) :=
    topology_systems_eq U
  let Rv : Sheaf (coefficientSequenceTopology J) CommRingCat.{u + 1} :=
    ⟨R.obj, by rw [← hX]; exact R.property⟩
  obtain ⟨B, τ, hR⟩ := SystemPresentation.systemRing_presentation J Rv
  let R₀ := systemRing.{u + 1, u, u + 1} J B τ
  let Rc : Sheaf (topology .systems X) CommRingCat.{u + 1} :=
    ⟨R₀.obj, by rw [hX]; exact R₀.property⟩
  have hRc : Rc = R := by
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg (fun Q ↦ Q.obj) hR
  rw [← hRc]
  let C₀ := ring.{u + 1, u, u + 1} (coefficientSequenceTopology J) R₀
  let Cc := (sheafCompose (topology .systems X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Rc
  let i := CategoryTheory.Equivalence.refl (C := ℕ × X.ProEt)
  have : i.functor.IsContinuous (topology .systems X) (coefficientSequenceTopology J) := by
    rw [hX]
    exact Functor.isContinuous_id _
  have : i.inverse.IsContinuous (coefficientSequenceTopology J) (topology .systems X) := by
    rw [hX]
    exact Functor.isContinuous_id _
  obtain ⟨p, hp⟩ := moduleTransport (topology .systems X) (coefficientSequenceTopology J)
    i Cc C₀ (Iso.refl _)
  let W : X.ProEt := ProEt.mk j
  obtain ⟨sd⟩ := semilinearDerivedSections.{u + 1, u, 0} J B τ
  let o := sd.localization W
  let e₀ := ProEt.sliceEquiv X W
  have : e₀.inverse.IsDenseSubsite (ProEt.topology U) (J.over W) := ProEt.sliceDense X W
  let e := (CategoryTheory.Equivalence.refl (C := ℕ)).prod e₀
  have : e.inverse.IsContinuous (topology .systems U)
      (coefficientSequenceTopology (J.over W)) := by
    rw [hU]
    exact sequenceContinuous (ProEt.topology U) (J.over W) e₀.inverse
  have : e.functor.IsContinuous (coefficientSequenceTopology (J.over W))
      (topology .systems U) := by
    rw [hU]
    exact sequenceContinuous (J.over W) (ProEt.topology U) e₀.functor
  let A := ring.{u + 1, u, u + 1} (coefficientSequenceTopology (J.over W))
    (systemRing.{u + 1, u, u + 1} (J.over W)
      (openRings.{u + 1, u, 0} J B W) (openTransitions.{u + 1, u, 0} J B τ W))
  let Ac := ((openSite W).sheafPushforwardContinuous RingCat.{u + 1}
    (coefficientSequenceTopology (J.over W)) (coefficientSequenceTopology J)).obj C₀
  let c₀ : Ac ≅ A := eqToIso (openRing.{u + 1, u, 0} J B τ W)
  let S := (sheafCompose (topology .systems U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing .systems j Rc)
  let V := e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
    (topology .systems U) (coefficientSequenceTopology (J.over W))
  let cS : S ≅ V.obj Ac := Iso.refl _
  let c : S ≅ V.obj A := cS ≪≫ V.mapIso c₀
  obtain ⟨q, hq⟩ := moduleTransport (coefficientSequenceTopology (J.over W))
    (topology .systems U) e A S c
  let φ : A ⟶ Ac := c₀.inv
  have hφ : openRestriction.{u + 1, u, 0} J B τ W =
      SheafOfModules.pushforward.{u + 1} (F := openSite W)
        (J := coefficientSequenceTopology (J.over W))
        (K := coefficientSequenceTopology J) (R := C₀) φ := rfl
  have hc : c.hom.hom ≫ Functor.whiskerLeft e.inverse.op φ.hom = 𝟙 S.obj := by
    simpa only [c, φ, cS, V, Iso.refl_hom, ObjectProperty.FullSubcategory.id_hom] using
      pushedRingIso_cancel e.inverse c₀ cS
  let L := q.inverse ⋙ o.extension ⋙ p.inverse
  let a : L ⊣ restrict .systems j Rc :=
    ((q.symm.toAdjunction.comp o.ordinaryAdjunction).comp p.symm.toAdjunction).ofNatIsoRight
      (by
        apply Functor.fullyFaithfulCancelRight (forget S)
        simp only [Functor.assoc, CategoryTheory.Equivalence.symm_inverse]
        rw [hq, hφ]
        erw [← Functor.assoc
          (SheafOfModules.pushforward.{u + 1} (F := openSite W)
            (J := coefficientSequenceTopology (J.over W))
            (K := coefficientSequenceTopology J) (R := C₀) φ)
          (forget A), pushforward_forget φ]
        simp only [Functor.assoc]
        erw [← Functor.assoc p.functor (forget C₀), hp]
        refine isoWhiskerRight
          (isoWhiskerLeft (forget Cc) (PresheafOfModules.pushforwardId C₀.obj))
          (PresheafOfModules.pushforward φ.hom ⋙ PresheafOfModules.pushforward c.hom.hom) ≪≫ ?_
        refine isoWhiskerLeft (forget Cc)
          (pushforwardCompOfEq (F := e.inverse) (G := openSite W)
            (R := C₀.obj) (S := A.obj) (T := S.obj) c.hom.hom φ.hom (𝟙 S.obj) hc) ≪≫ ?_
        exact Iso.refl _)
  have hW (V : X.ProEt) : Subsingleton (V ⟶ W) := by
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).mp
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  have hu (M) : IsIso (o.ordinaryAdjunction.unit.app M) :=
    SystemPresentation.systemUnit_isIso J B τ W hW o M
  have : IsIso o.ordinaryAdjunction.unit := NatIso.isIso_of_isIso_app _
  let ff := o.ordinaryAdjunction.fullyFaithfulLOfIsIsoUnit
  have : o.extension.Full := ff.full
  have : o.extension.Faithful := ff.faithful
  have : L.Full := by dsimp only [L]; infer_instance
  have : L.Faithful := by dsimp only [L]; infer_instance
  have huL (M : Mod (restrictRing .systems j Rc)) : IsIso (a.unit.app M) :=
    have := a.unit_isIso_of_L_fully_faithful
    inferInstance
  have hL : PreservesFiniteLimits L := by
    dsimp only [L]
    exact comp_preservesFiniteLimits _ _
  have : (restrict .systems j Rc).Additive := (restriction_exact .systems j Rc).1
  have hAdd : L.Additive := a.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} L := a.leftAdjoint_preservesColimits
  exact ⟨{
    ordinary := L
    adjunction := a
    sectionIso := fun M ↦ (asIso (a.unit.app M)).symm
    sectionUnit := fun M ↦ IsIso.hom_inv_id (a.unit.app M)
    additive := hAdd
    limits := hL
    colimits := PreservesColimitsOfSize.preservesFiniteColimits L
  }⟩

open SheafOfModules.CanonicalTensorPullbackOfUniverses CategoryTheory.Functor

private theorem openInclusion_cocontinuous (m : Mode) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (openInclusion m j).IsCocontinuous (topology m U) (topology m X) := by
  have hc : (proEtaleOpenComposition j).IsCocontinuous
      (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  cases m with
  | ordinary => exact hc
  | systems => exact system_cocontinuous (proEtaleOpenComposition j)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_preserves_resolving {m : Mode} {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology m X) CommRingCat.{u + 1})
    (P : CochainComplex (Mod R) ℤ) (hP : resolving R P) :
    resolving (restrictRing m j R) ((restrict m j R).mapHomologicalComplex (.up ℤ) |>.obj P) := by
  let F := openInclusion m j
  have : F.IsCocontinuous (topology m U) (topology m X) := openInclusion_cocontinuous m j
  let L := F.sheafPushforwardContinuous (Type (u + 1)) (topology m U) (topology m X)
  let V := F.sheafPushforwardCocontinuous (Type (u + 1)) (topology m U) (topology m X)
  let a : L ⊣ V := F.sheafAdjunctionCocontinuous (Type (u + 1))
    (topology m U) (topology m X)
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  let I := restrictionInverse j R
  have : I.modules.Additive := (restriction_exact m j R).1
  refine ⟨isKFlat_inverseImage L V a I P hP.1 hP.2, ?_⟩
  intro n
  exact isFlat_algebraicInverseImageOfUniverses.{u + 1, u, u + 1, u, u + 1, u + 1} L V a
    (SheafOfModules.inverseImageOfUniverses I) (P.X n) (hP.2 n)

set_option backward.isDefEq.respectTransparency false in
private theorem resolvingSingleWhiskering
    {K : Type (u + 2)} [Category.{u + 1} K]
    {H : Type (u + 2)} [Category.{u + 1} H]
    {D : Type (u + 2)} [Category.{u + 2} D]
    (E : Type (u + 2)) [Category.{u + 2} E]
    (p : K ⥤ H) [p.Full] [p.EssSurj] (hsurj : Function.Surjective p.obj)
    (W : MorphismProperty H) [W.HasRightCalculusOfFractions]
    (q : H ⥤ D) [q.IsLocalization W]
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hp : ∀ X, P X ↔ S (p.obj X))
    (hres : ∀ X : H, ∃ (Y : S.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    Nonempty (((whiskeringLeft P.FullSubcategory D E).obj
      (P.ι ⋙ p ⋙ q)).FullyFaithful) := by
  let f := S.lift (P.ι ⋙ p) (fun X ↦ (hp X.obj).1 X.property)
  have : f.Full := ⟨by
    intro X Y g
    obtain ⟨g, hg⟩ := p.map_surjective g.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg⟩
  have : f.EssSurj := ⟨by
    intro X
    obtain ⟨Y, hy⟩ := hsurj X.obj
    refine ⟨⟨Y, (hp Y).2 (hy.symm ▸ X.property)⟩, ?_⟩
    exact ⟨ObjectProperty.isoMk S (eqToIso hy)⟩⟩
  have : (S.ι ⋙ q).IsLocalization (W.inverseImage S.ι) :=
    CategoryTheory.restriction_localization W q S hres
  let ff := Localization.fullyFaithfulWhiskeringLeft
    (S.ι ⋙ q) (W.inverseImage S.ι) E
  let fg := CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f E
  exact ⟨ff.comp fg⟩

namespace SiteRestriction
attribute [local irreducible] SheafOfModules.monoidalCategory
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : D ⥤ C) [F.IsContinuous K J] [F.IsCocontinuous K J]

private abbrev ring (R : Sheaf J CommRingCat.{u + 1}) :=
  (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R

private noncomputable def inverse (R : Sheaf J CommRingCat.{u + 1}) :
  AlgebraicInverseImage
      (F.sheafPushforwardContinuous (Type (u + 1)) K J) R
      ((F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R) where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h V x ↦ h (F.op.obj V) x
  ringMul := fun _ _ _ _ h V x ↦ h (F.op.obj V) x
  ringZero := fun _ _ h V x ↦ h (F.op.obj V) x
  ringOne := fun _ _ h V x ↦ h (F.op.obj V) x
  modules := SheafOfModules.pushforward.{u + 1} (F := F) (𝟙 _)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h V x ↦ h (F.op.obj V) x
  moduleZero := fun _ _ _ h V x ↦ h (F.op.obj V) x
  moduleSMul := fun _ _ _ _ _ h V x ↦ h (F.op.obj V) x

private noncomputable abbrev res (R : Sheaf J CommRingCat.{u + 1}) :=
  (inverse J K F R).modules

set_option backward.isDefEq.respectTransparency false in
private theorem tensorIso_exists (R : Sheaf J CommRingCat.{u + 1}) :
    ∃ μ : ∀ M N : Mod R,
        (res J K F R).obj (((tensor R).obj M).obj N) ≅
          ((tensor (ring J K F R)).obj ((res J K F R).obj M)).obj
            ((res J K F R).obj N),
      (∀ {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N'),
        (res J K F R).map (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
            (μ M' N').hom =
          (μ M N).hom ≫ ((tensor (ring J K F R)).map ((res J K F R).map f)).app
            ((res J K F R).obj N) ≫
              ((tensor (ring J K F R)).obj ((res J K F R).obj M')).map
                ((res J K F R).map g)) ∧
      ∀ (M N : Mod R) (W : Dᵒᵖ)
        (x : M.val.obj (F.op.obj W)) (y : N.val.obj (F.op.obj W)),
        (μ M N).hom.val.app W (pure R M N (F.op.obj W) x y) =
          pure (ring J K F R) ((res J K F R).obj M) ((res J K F R).obj N) W x y := by
  let L := F.sheafPushforwardContinuous (Type (u + 1)) K J
  let V := F.sheafPushforwardCocontinuous (Type (u + 1)) K J
  let a : L ⊣ V := F.sheafAdjunctionCocontinuous (Type (u + 1))
    K J
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  let I := inverse J K F R
  obtain ⟨μ, hn, hp⟩ := CochainInversePairing.exists_inverseImageTensorComparison
    R ((F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R) L I V a
  refine ⟨μ, ?_, ?_⟩
  · intro M M' N N' f g
    simpa only [I, inverse, res, AlgebraicGeometry.Scheme.ProjectionRestriction.tensor,
      curriedTensor_obj_obj, curriedTensor_obj_map, curriedTensor_map_app,
      MonoidalCategory.tensorHom_def, Category.assoc] using hn f g
  · intro M N W x y
    let Z : Sheaf J (Type (u + 1)) :=
      (CochainScalarConstruction.underlying R).obj M ⊗
        (CochainScalarConstruction.underlying R).obj N
    let z := CochainInversePairing.pureSheaf R M N
    have h := hp M N Z (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) z (fun _ _ ↦ rfl) W (x, y)
    exact h

end SiteRestriction

set_option backward.isDefEq.respectTransparency false in
private theorem resolvingHomotopy_resolutions
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1}) :
    ∀ X : HomotopyCategory (Mod R) (.up ℤ),
      ∃ (Y : ObjectProperty.FullSubcategory
        (fun X : HomotopyCategory (Mod R) (.up ℤ) ↦ resolving R X.as)) (f : Y.obj ⟶ X),
        HomotopyCategory.quasiIso (Mod R) (.up ℤ) f := by
  intro X
  obtain ⟨P, f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
  have hflat : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n) := by
    intro n
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
  refine ⟨⟨(HomotopyCategory.quotient (Mod R) (.up ℤ)).obj P, ⟨hp, hflat⟩⟩,
    (HomotopyCategory.quotient (Mod R) (.up ℤ)).map f, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq

set_option backward.isDefEq.respectTransparency false in
private noncomputable def resolvingQ_fullyFaithful
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1})
    (E : Type (u + 2)) [Category.{u + 2} E] :
    (((Functor.whiskeringLeft _ _ E).obj
      ((resolving R).ι ⋙ DerivedCategory.Q))).FullyFaithful := by
  let H : ObjectProperty (HomotopyCategory (Mod R) (.up ℤ)) := fun X ↦ resolving R X.as
  let ff := Classical.choice (resolvingSingleWhiskering E
    (HomotopyCategory.quotient (Mod R) (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso (Mod R) (.up ℤ)) DerivedCategory.Qh
    (resolving R) H (fun _ ↦ Iff.rfl) (resolvingHomotopy_resolutions R))
  exact ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (isoWhiskerLeft (resolving R).ι (DerivedCategory.quotientCompQhIso (Mod R))))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def resolvingQQ_fullyFaithful
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1})
    (E : Type (u + 2)) [Category.{u + 2} E] :
    (((Functor.whiskeringLeft _ _ E).obj
      (((resolving R).ι ⋙ DerivedCategory.Q).prod
        ((resolving R).ι ⋙ DerivedCategory.Q)))).FullyFaithful := by
  let H : ObjectProperty (HomotopyCategory (Mod R) (.up ℤ)) := fun X ↦ resolving R X.as
  let ff := Classical.choice (CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
    E (HomotopyCategory.quotient (Mod R) (.up ℤ))
    HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso (Mod R) (.up ℤ)) DerivedCategory.Qh
    (resolving R) H (fun _ ↦ Iff.rfl) (resolvingHomotopy_resolutions R))
  exact ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (NatIso.prod (isoWhiskerLeft (resolving R).ι
      (DerivedCategory.quotientCompQhIso (Mod R)))
      (isoWhiskerLeft (resolving R).ι (DerivedCategory.quotientCompQhIso (Mod R)))))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def complexComparisonNat
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    {V : Mod S ⥤ Mod R} (p : Pullback R S V) :
    DerivedCategory.Q ⋙ p.derived ⟶
      p.ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Mod R)).inv p.derived ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (Mod R) (.up ℤ)) p.epsilon ≫
    Functor.whiskerRight (p.ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (p.ordinary.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (Mod S)).hom

set_option backward.isDefEq.respectTransparency false in
private theorem derivedSquare_exists {m : Mode} (d : Input.{u} m) (t : SiteSquare d)
    (gp : Pullback d.R d.S (direct m d.g d.R d.S d.coefficient))
    (gu : Pullback (restrictRing m d.j d.R) (restrictRing m d.j' d.S)
      (direct m d.gU _ _ (cornerCoefficient t)))
    (e : gp.ordinary ⋙ restrict m d.j' d.S ≅ restrict m d.j d.R ⋙ gu.ordinary) :
    ∃ θ : gp.derived ⋙ (restrict m d.j' d.S).mapDerivedCategory ≅
        (restrict m d.j d.R).mapDerivedCategory ⋙ gu.derived,
      ∀ (P : CochainComplex (Mod d.R) ℤ), resolving d.R P →
        θ.hom.app (DerivedCategory.Q.obj P) ≫
          gu.derived.map ((restrict m d.j d.R).mapDerivedCategoryFactors.hom.app P) ≫
          derivedPullbackComplexComparison gu.ordinary gu.derived gu.epsilon
            (((restrict m d.j d.R).mapHomologicalComplex (.up ℤ)).obj P) =
        (restrict m d.j' d.S).mapDerivedCategory.map
          (derivedPullbackComplexComparison gp.ordinary gp.derived gp.epsilon P) ≫
          (restrict m d.j' d.S).mapDerivedCategoryFactors.hom.app
            ((gp.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  let L := restrict m d.j d.R
  let L' := restrict m d.j' d.S
  let F := gp.ordinary.mapHomologicalComplex (.up ℤ)
  let G := gu.ordinary.mapHomologicalComplex (.up ℤ)
  let A : DerivedCategory.Q ⋙ gp.derived ⋙ L'.mapDerivedCategory ⟶
      F ⋙ L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (complexComparisonNat gp) L'.mapDerivedCategory ≫
      Functor.whiskerLeft F L'.mapDerivedCategoryFactors.hom
  let B : DerivedCategory.Q ⋙ L.mapDerivedCategory ⋙ gu.derived ⟶
      L.mapHomologicalComplex (.up ℤ) ⋙ G ⋙ DerivedCategory.Q :=
    Functor.whiskerRight L.mapDerivedCategoryFactors.hom gu.derived ≫
      Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ)) (complexComparisonNat gu)
  let c := NatIso.mapHomologicalComplex e (.up ℤ)
  let eC : F ⋙ L'.mapHomologicalComplex (.up ℤ) ≅
      L.mapHomologicalComplex (.up ℤ) ⋙ G := c
  have hA (P : (resolving d.R).FullSubcategory) : IsIso (A.app P.obj) := by
    have := gp.flat P.obj P.property
    change IsIso (L'.mapDerivedCategory.map
      (derivedPullbackComplexComparison gp.ordinary gp.derived gp.epsilon P.obj) ≫ _)
    infer_instance
  have hB (P : (resolving d.R).FullSubcategory) : IsIso (B.app P.obj) := by
    have := gu.flat _ (restriction_preserves_resolving d.j d.R P.obj P.property)
    change IsIso (gu.derived.map (L.mapDerivedCategoryFactors.hom.app P.obj) ≫
      derivedPullbackComplexComparison gu.ordinary gu.derived gu.epsilon _)
    infer_instance
  let a := Functor.whiskerLeft (resolving d.R).ι A
  let b := Functor.whiskerLeft (resolving d.R).ι B
  have (P : (resolving d.R).FullSubcategory) : IsIso (a.app P) := hA P
  have : IsIso a := NatIso.isIso_of_isIso_app _
  have (P : (resolving d.R).FullSubcategory) : IsIso (b.app P) := hB P
  have : IsIso b := NatIso.isIso_of_isIso_app _
  let r := asIso a ≪≫
    isoWhiskerLeft (resolving d.R).ι (isoWhiskerRight eC DerivedCategory.Q) ≪≫
      (asIso b).symm
  let ff := resolvingQ_fullyFaithful d.R (Der (restrictRing m d.j' d.S))
  let θ : gp.derived ⋙ L'.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ gu.derived :=
    ff.preimageIso r
  refine ⟨θ, ?_⟩
  intro P hP
  have := hB ⟨P, hP⟩
  have hh := congrArg (fun f ↦ f.app ⟨P, hP⟩) (ff.map_preimage
    (X := gp.derived ⋙ L'.mapDerivedCategory)
    (Y := L.mapDerivedCategory ⋙ gu.derived) r.hom)
  change θ.hom.app (DerivedCategory.Q.obj P) = r.hom.app ⟨P, hP⟩ at hh
  simp only [r, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, asIso_hom,
    asIso_inv, NatIso.isIso_inv_app] at hh
  dsimp only [a, b, Functor.isoWhiskerLeft, Functor.isoWhiskerRight,
    CategoryTheory.Functor.mapIso, Functor.whiskeringLeft, Functor.whiskeringRight,
    Functor.whiskerLeft, Functor.whiskerRight, ObjectProperty.ι,
    CategoryTheory.inducedFunctor] at hh
  have := hB ⟨P, hP⟩
  have heq : θ.hom.app (DerivedCategory.Q.obj P) ≫ B.app P =
      A.app P ≫ DerivedCategory.Q.map (eC.hom.app P) := by
    rw [hh]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  simpa only [Functor.comp_obj, Functor.id_obj, A, B, L, L', F, G, eC, c, complexComparisonNat,
    derivedPullbackComplexComparison, NatIso.mapHomologicalComplex, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using heq

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

set_option backward.isDefEq.respectTransparency false in
private theorem tensorDescentNormalized
    {K : Type u₁} [Category.{v₁} K] {H : Type u₂} [Category.{v₂} H]
    {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]
    (q : K ⥤ D) (q' : H ⥤ E) (F : K ⥤ H) (LF : D ⥤ E)
    (eps : q ⋙ LF ⟶ F ⋙ q')
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hF : ∀ X, P X → S (F.obj X))
    (ff : ((whiskeringLeft (P.FullSubcategory × P.FullSubcategory) (D × D) E).obj
      ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    (t : K × K ⥤ K) (t' : H × H ⥤ H)
    (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : (F.prod F) ⋙ t' ≅ t ⋙ F)
    (he : ∀ X, P X → IsIso (eps.app X))
    (het : ∀ X Y, P X → P Y → IsIso (eps.app (t.obj (X, Y)))) :
    ∃ a : T ⋙ LF ≅ (LF.prod LF) ⋙ T',
      ∀ (X Y : K) (hx : P X) (hy : P Y),
        LF.map (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ a.hom.app (q.obj X, q.obj Y) ≫
          T'.map (Prod.mkHom (eps.app X) (eps.app Y)) ≫
          r'.inv.app (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩) ≫
          q'.map (b.hom.app (X, Y)) = eps.app (t.obj (X, Y)) := by
  obtain ⟨a, ha, _⟩ := tensorComparisonDescent q q' F LF eps P S hF ff
    t t' T T' r r' b.symm he het
  refine ⟨a, ?_⟩
  intro X Y hx hy
  have hh := congrArg (fun k ↦ k ≫
    r'.inv.app (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩) ≫
      q'.map (b.hom.app (X, Y))) (ha X Y hx hy)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.symm_hom] at hh
  have hi : q'.map (b.inv.app (X, Y)) ≫ q'.map (b.hom.app (X, Y)) = 𝟙 _ := by
    rw [← q'.map_comp, ← NatTrans.comp_app, b.inv_hom_id, NatTrans.id_app]
    exact q'.map_id _
  rw [← Category.assoc, hi] at hh
  simpa only [CategoryTheory.Functor.comp_obj, Category.comp_id, Category.assoc] using hh

open MonoidalCategory

/- Keep the signed total comparison as an abstract functor isomorphism. Its
component equation is the API used by representative descent. -/
set_option backward.isDefEq.respectTransparency false in
@[irreducible] private noncomputable def exactTensorTotalIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (μ : ∀ M N : A, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hn : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (adj : L ⊣ V) :
    ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor B).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ≅
      Functor.uncurry.obj ((curriedTensor A).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ L.mapHomologicalComplex (.up ℤ) := by
  have (P Q : CochainComplex A ℤ) : IsIso (tensorPullbackTotal L μ hn P Q) :=
    tensorPullbackTotal_isIso L μ hn V adj P Q
  exact NatIso.ofComponents (fun Z ↦ asIso (tensorPullbackTotal L μ hn Z.1 Z.2)) (by
    intro Z Z' f
    simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
      Functor.map₂HomologicalComplex, asIso_hom, tensorMap_factor]
    exact tensorPullbackTotal_naturality L μ hn f.1 f.2)

set_option backward.isDefEq.respectTransparency false in
private theorem exactTensorTotalIso_hom_app
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (μ : ∀ M N : A, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hn : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (adj : L ⊣ V) (P Q : CochainComplex A ℤ) :
    (exactTensorTotalIso L μ hn V adj).hom.app (P, Q) = tensorPullbackTotal L μ hn P Q := by
  unfold exactTensorTotalIso
  rfl

section
attribute [local irreducible] SheafOfModules.monoidalCategory

end

end SheafOfModules.OpenTensorNormalization
