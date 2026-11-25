/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryTensorPullbackData
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import Mathlib.CategoryTheory.Functor.Flat
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingTensorComparison
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
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
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.CochainCompositeConstruction.CochainCompositeAlgebraic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
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
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-! # Ordinary tensor generators and flat representatives for a ringed-site pullback

## References

* Stacks Project, Modules on Sites, Tag 03EL, and Cohomology on Sites, Tag 0G7E
* Stacks Project, Modules on Sites, Tag 03D7
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open SheafOfModules.GeometricConstruction (mset)
open CategoryTheory.MonoidalCategory

namespace WeilConjectures.SemilinearSections

open AlgebraicGeometry.ProEtale.VaryingRing

variable [UnivLE.{max c v, r}]


omit [UnivLE.{max c v, r}] in
private theorem additiveSheafification {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{r} := hasSheafifyEssentiallySmallSite J _

attribute [local instance 2000] additiveSheafification

omit [UnivLE.{max c v, r}] in
private theorem additiveWeakSheafification {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{r} := by
  infer_instance

attribute [local instance 2000] additiveWeakSheafification

omit [UnivLE.{max c v, r}] in
private theorem additiveLocallyBijective {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local instance 2000] additiveLocallyBijective

omit [UnivLE.{max c v, r}] in
private theorem setSheafification {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C) :
    HasSheafify J (Type r) := hasSheafifyEssentiallySmallSite J _

attribute [local instance 2000] setSheafification

omit [UnivLE.{max c v, r}] in
private theorem setSheafFiniteLimits {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C) :
    HasFiniteLimits (Sheaf J (Type r)) := by
  infer_instance

attribute [local instance 2000] setSheafFiniteLimits


omit [UnivLE.{max c v, r}] in
private theorem setSheafProducts {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C) :
    HasBinaryProducts (Sheaf J (Type r)) := by
  infer_instance

attribute [local instance 2000] setSheafProducts

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] SheafOfModules.monoidalCategory

private abbrev SiteMod {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

private abbrev siteTensor {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    (M N : SiteMod J R) := (SheafOfModules.monoidalCategory R).tensorObj M N

private abbrev siteTensorHom {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    {M M' N N' : SiteMod J R} (f : M ⟶ M') (g : N ⟶ N') :=
  (SheafOfModules.monoidalCategory R).tensorHom f g

private abbrev sitePure {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    (M N : SiteMod J R) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :=
  SheafOfModules.CochainScalarConstruction.pure R M N U x y

/-- Evaluate the inverse-image pure pairing before specializing its modules. -/
private theorem sitePureSheaf_apply
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    (M N : SiteMod J R) (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (SheafOfModules.CochainInversePairing.pureSheaf R M N).hom.app V (x, y) =
      sitePure J R M N V x y := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar multiplication on a pure tensor, with abstract module arguments. -/
private theorem sitePure_smul
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    (M N : SiteMod J R) (V : Cᵒᵖ) (a : R.obj.obj V)
    (x : M.val.obj V) (y : N.val.obj V) :
    a • sitePure J R M N V x y = sitePure J R M N V (a • x) y := by
  exact ((SheafOfModules.CochainScalarConstruction.pureBilin R M N V).map_smul₂ a x y).symm

private abbrev siteFlatTerms {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    (P : CochainComplex (SiteMod J R) ℤ) :=
  ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)

open SheafOfModules SheafOfModules.GeometricConstruction MonoidalCategory
section
variable {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : D ⥤ C) [F.IsContinuous K J]
  (L : Sheaf K (Type (r)) ⥤ Sheaf J (Type (r)))
  (adj : L ⊣ F.sheafPushforwardContinuous (Type (r)) K J)

private def directPair {X Y : Sheaf J (Type (r))} {T : Sheaf K (Type (r))}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj Y) :
    T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj (X ⊗ Y) :=
  ⟨{ app U := ↾(fun t ↦ (x.hom.app U t, y.hom.app U t))
     naturality := by
       intro U V f
       ext t
       change (x.hom.app V (T.obj.map f t), y.hom.app V (T.obj.map f t)) =
         (X.obj.map (F.op.map f) (x.hom.app U t),
           Y.obj.map (F.op.map f) (y.hom.app U t))
       exact Prod.ext (CategoryTheory.congr_fun (x.hom.naturality f) t)
         (CategoryTheory.congr_fun (y.hom.naturality f) t) }⟩

omit [EssentiallySmall.{r} C] [EssentiallySmall.{r} D] [UnivLE.{max c v, r}] in
private theorem transpose_pair {X Y : Sheaf J (Type (r))} {T : Sheaf K (Type (r))}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj Y) :
    (adj.homEquiv T (X ⊗ Y)).symm (directPair.{c, v, r} F x y) =
      CartesianMonoidalCategory.lift ((adj.homEquiv T X).symm x)
        ((adj.homEquiv T Y).symm y) := by
  apply CartesianMonoidalCategory.hom_ext
  · erw [CartesianMonoidalCategory.lift_fst, ← adj.homEquiv_naturality_right_symm]
    rfl
  · erw [CartesianMonoidalCategory.lift_snd, ← adj.homEquiv_naturality_right_symm]
    rfl

omit [EssentiallySmall.{r} C] [EssentiallySmall.{r} D] [UnivLE.{max c v, r}] in
private theorem transpose_binary
    {X Y Z : Sheaf J (Type (r))} {T : Sheaf K (Type (r))} (op : X ⊗ Y ⟶ Z)
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj Y)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj Z)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U)
      (x.hom.app U t, y.hom.app U t)) :
    ∀ U t, ((adj.homEquiv T Z).symm z).hom.app U t =
      op.hom.app U (((adj.homEquiv T X).symm x).hom.app U t,
        ((adj.homEquiv T Y).symm y).hom.app U t) := by
  have he : z = directPair.{c, v, r} F x y ≫
      (F.sheafPushforwardContinuous (Type (r)) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm, transpose_pair.{c, v, r} F L adj]
  intro U t
  rfl

omit [EssentiallySmall.{r} C] [EssentiallySmall.{r} D] [UnivLE.{max c v, r}] in
private theorem transpose_constant
    {X : Sheaf J (Type (r))} {T : Sheaf K (Type (r))}
    (op : 𝟙_ (Sheaf J (Type (r))) ⟶ X)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj X)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U) PUnit.unit) :
    ∀ U t, ((adj.homEquiv T X).symm z).hom.app U t = op.hom.app U PUnit.unit := by
  let w : T ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj (𝟙_ _) :=
    ⟨{ app U := ↾(fun _ ↦ PUnit.unit) }⟩
  have he : z = w ≫ (F.sheafPushforwardContinuous (Type (r)) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm]
  intro U t
  change op.hom.app U _ = _
  congr 1

omit [UnivLE.{max c v, r}] in
private theorem siteStructuralMap_exists
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} K J).obj R)
    (RI : Sheaf J CommRingCat.{r}) (I : AlgebraicInverseImage L S RI) :
    ∃ c : RI ⟶ R, (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset S) (rset R)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map φ) := by
  let φs : rset S ⟶ (F.sheafPushforwardContinuous (Type (r)) K J).obj (rset R) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map φ
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
    apply transpose_binary.{c, v, r} F L adj (ringAdd R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
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
    apply transpose_binary.{c, v, r} F L adj (ringMul R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
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
    apply transpose_constant.{c, v, r} F L adj (ringOne R) (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 1
    have h : (show S.obj.obj V from z.hom.app V x) = 1 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_one

end
private noncomputable abbrev tensorFunctor
    {D : Type c} [Category.{v} D] [EssentiallySmall.{r} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :=
  CategoryTheory.CochainPullback.extensionFunctor (J := K) (A := A) (B := S) c

private noncomputable abbrev tensorAdjunction
    {D : Type c} [Category.{v} D] [EssentiallySmall.{r} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :=
  CategoryTheory.CochainPullback.extensionAdjunction (J := K) (A := A) (B := S) c

open SheafOfModules.GeometricConstruction
private theorem pushforward_operations
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (A : Sheaf J CommRingCat.{r}) (B : Sheaf K CommRingCat.{r})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} K J).obj A)
    (H : SiteMod J A) :
    let V := F.sheafPushforwardContinuous (Type (r)) K J
    let P := SheafOfModules.pushforward.{r} (F := F)
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
    let X := (mset A).obj H
    V.map (CategoryTheory.CochainPullback.moduleAddMap A H) =
      prodComparison V X X ≫ CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) := by
  dsimp only
  let V := F.sheafPushforwardContinuous (Type (r)) K J
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Bound the generic scalar-action calculation.
private theorem pushforward_action
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (A : Sheaf J CommRingCat.{r}) (B : Sheaf K CommRingCat.{r})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} K J).obj A)
    (H : SiteMod J A) :
    let V := F.sheafPushforwardContinuous (Type (r)) K J
    let P := SheafOfModules.pushforward.{r} (F := F)
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
    let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map φ
    let X := (mset A).obj H
    CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) =
      prod.map φs (𝟙 (V.obj X)) ≫ inv (prodComparison V (rset A) X) ≫
        V.map (CategoryTheory.CochainPullback.moduleSMulMap A H) := by
  dsimp only [CategoryTheory.CochainPullback.moduleSMulMap]
  let V := F.sheafPushforwardContinuous (Type (r)) K J
  let X := (mset A).obj H
  let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map φ
  have : PreservesLimits V := by dsimp only [V]; infer_instance
  ext U p
  let q := (prod.map φs (𝟙 (V.obj X)) ≫ inv (prodComparison V (rset A) X)).hom.app U p
  have hf := congrArg (fun f ↦ f.hom.app U p)
    (show prod.map φs (𝟙 (V.obj X)) ≫ inv (prodComparison V (rset A) X) ≫
        V.map (prod.fst : rset A ⨯ X ⟶ rset A) =
          (prod.fst : rset B ⨯ V.obj X ⟶ rset B) ≫ φs by
      rw [inv_prodComparison_map_fst, prod.map_fst])
  have hs := congrArg (fun f ↦ f.hom.app U p)
    (show prod.map φs (𝟙 (V.obj X)) ≫ inv (prodComparison V (rset A) X) ≫
        V.map (prod.snd : rset A ⨯ X ⟶ X) =
          (prod.snd : rset B ⨯ V.obj X ⟶ V.obj X) by
      rw [inv_prodComparison_map_snd, prod.map_snd, Category.comp_id])
  let smul : A.obj.obj (F.op.obj U) → H.val.obj (F.op.obj U) →
      H.val.obj (F.op.obj U) := fun a x ↦ a • x
  change smul ((φ.hom.app U).hom
      ((prod.fst : rset B ⨯ V.obj X ⟶ rset B).hom.app U p))
      ((prod.snd : rset B ⨯ V.obj X ⟶ V.obj X).hom.app U p) =
    smul ((prod.fst : rset A ⨯ X ⟶ rset A).hom.app (F.op.obj U) q)
      ((prod.snd : rset A ⨯ X ⟶ X).hom.app (F.op.obj U) q)
  exact congrArg₂ smul hf.symm hs.symm

section NormalizedAdjunction
open SheafOfModules
open SheafOfModules.GeometricConstruction
open SheafOfModules.OpenTensorNormalization.GeneralizedRinged

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The linear adjunction to the supplied sectionwise pushforward, retaining the
underlying set-sheaf hom equivalence.
The scalar insertion is the image of `1 ⊗ m`. -/
private theorem normalizedAdjunction
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type (r)) ⥤ Sheaf J (Type (r)))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (r)) K J)
    [PreservesFiniteLimits L]
    (A : Sheaf J CommRingCat.{r}) (B : Sheaf K CommRingCat.{r})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} K J).obj A)
    (RI : Sheaf J CommRingCat.{r}) (I : AlgebraicInverseImage L B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset B) (rset A)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map φ)) :
    ∃ am : I.modules ⋙ SemilinearSections.tensorFunctor.{c, v, r} c ⊣
      SheafOfModules.pushforward.{r} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).map φ), ∀ M H a,
      (mset B).map (am.homEquiv M H a) =
        adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫
          SheafOfModules.CochainTensorComparison.scalarInsertion B A RI L I c
            (I.modules ⋙ SemilinearSections.tensorFunctor.{c, v, r} c) (fun _ ↦ rfl) M ≫
              (mset A).map a) := by
  let V := F.sheafPushforwardContinuous (Type (r)) K J
  let P := SheafOfModules.pushforward.{r} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
    ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
  let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map φ
  have : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let eI := I.moduleUnderlying
  obtain ⟨L₀, hobj₀, hmap₀, V₀, ⟨a₀⟩, hAdd₀⟩ :=
    CategoryTheory.CochainPullback.ringedPullbackPresentation_exists
      (R := B) (S := A) L V adj RI I c
  let p : CategoryTheory.CochainPullback.RingedPullback.{r, c, v, c, v}
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
  have hEquiv (M : SheafOfModules (base B)) (H : SheafOfModules (base A)) :
      ∃ E : (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{r} RingCat.{r})).map c)).obj H) ≃ (M ⟶ P.obj H),
        ∀ a, (mset B).map (E a) =
          adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    have ha : CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) ≫ (𝟙 _) =
        prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
          V.map (CategoryTheory.CochainPullback.moduleAddMap A H) := by
      simp only [Category.comp_id, prod.map_id_id, Category.id_comp]
      change _ = inv (prodComparison V ((mset A).obj H) ((mset A).obj H)) ≫ _
      apply (cancel_epi (prodComparison V ((mset A).obj H) ((mset A).obj H))).mp
      erw [IsIso.hom_inv_id_assoc]
      exact (pushforward_operations.{c, v, r} F A B φ H).symm
    have hs : CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) =
        prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) ((mset A).obj H)) ≫
          V.map (CategoryTheory.CochainPullback.moduleSMulMap A H) :=
      pushforward_action.{c, v, r} F A B φ H
    have hg : adj.homEquiv _ _ (CategoryTheory.CochainPullback.structureMap p) = φs := by
      rw [hp, Equiv.apply_symm_apply]
    rw [← hg] at hs
    obtain ⟨E, hE⟩ := CategoryTheory.CochainPullback.linearMate_exists p H (P.obj H)
      (Iso.refl _) ha (by
        simp only [Iso.refl_hom]
        convert hs using 1
        rfl) M
    refine ⟨E, fun a ↦ ?_⟩
    have h := hE a
    change (mset B).map (E a) ≫ (𝟙 _) =
      adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) at h
    simpa only [Category.comp_id] using h
  obtain ⟨B', hB⟩ : ∃ B' : ∀ (M : SheafOfModules (base B))
      (H : SheafOfModules (base A)),
      (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).map c)).obj H) ≃ (M ⟶ P.obj H),
      ∀ M H a, (mset B).map (B' M H a) =
        adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    exact ⟨fun M H ↦ (hEquiv M H).choose, fun M H ↦ (hEquiv M H).choose_spec⟩
  let restriction := restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).map c)
  let eP : P ⋙ mset B ≅ restriction ⋙ mset RI ⋙ V :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  obtain ⟨am, ham⟩ := restrictedAdjunction I.modules restriction
    (SemilinearSections.tensorFunctor.{c, v, r} c)
    (SemilinearSections.tensorAdjunction.{c, v, r} c) P (mset B) (mset RI) L V adj eI eP B' (by
      intro M H a
      change (mset B).map (B' M H a) ≫ (𝟙 _) = _
      exact (Category.comp_id _).trans (hB M H a))
  refine ⟨am, ?_⟩
  intro M H a
  have h := ham M H a
  change (mset B).map (am.homEquiv M H a) ≫ (𝟙 _) = _ at h
  simp only [Category.comp_id] at h
  have hq : CategoryTheory.CochainPullback.insertion c (I.modules.obj M) =
      SheafOfModules.CochainTensorComparison.scalarInsertion B A RI L I c
        (I.modules ⋙ SemilinearSections.tensorFunctor.{c, v, r} c) (fun _ ↦ rfl) M := by
    ext U x
    exact ((Classical.choose_spec
      (CategoryTheory.CochainPullback.extensionAdjunction_existsUnique c)).1
        (I.modules.obj M) U x)
  have hm := CategoryTheory.CochainPullback.extensionHomEquiv_formula c
    (I.modules.obj M) H a
  change (mset RI).map ((SemilinearSections.tensorAdjunction.{c, v, r} c).homEquiv _ _ a) =
    CategoryTheory.CochainPullback.insertion c (I.modules.obj M) ≫ (mset A).map a at hm
  rw [hq] at hm
  exact h.trans
    (congrArg (adj.homEquiv _ _) (congrArg (fun z ↦ eI.inv.app M ≫ z) hm))

end NormalizedAdjunction

section TensorTransport
section OrdinaryTransport
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

@[irreducible] private noncomputable def transportedOrdinary
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (F G : SiteMod J R ⥤
      SiteMod K S) (e : F ≅ G)
    (k : ∀ M N : SiteMod J R,
      F.obj (siteTensor J R M N) ≅
        siteTensor K S (F.obj M) (F.obj N))
    (M N : SiteMod J R) :
    G.obj (siteTensor J R M N) ≅
      siteTensor K S (G.obj M) (G.obj N) :=
  letI := SheafOfModules.monoidalCategory S
  (e.app _).symm ≪≫ k M N ≪≫ tensorIso (e.app M) (e.app N)

private theorem transportedOrdinary_natural
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (F G : SiteMod J R ⥤
      SiteMod K S) (e : F ≅ G)
    (k : ∀ M N : SiteMod J R,
      F.obj (siteTensor J R M N) ≅
        siteTensor K S (F.obj M) (F.obj N))
    (hk : ∀ {M M' N N' : SiteMod J R}
      (b : M ⟶ M') (d : N ⟶ N'),
      F.map (siteTensorHom J R b d) ≫ (k M' N').hom =
        (k M N).hom ≫ siteTensorHom K S (F.map b) (F.map d))
    {M M' N N' : SiteMod J R}
    (b : M ⟶ M') (d : N ⟶ N') :
    G.map (siteTensorHom J R b d) ≫
        (transportedOrdinary.{c, v, r} J K R S F G e k M' N').hom =
      (transportedOrdinary.{c, v, r} J K R S F G e k M N).hom ≫
        siteTensorHom K S (G.map b) (G.map d) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  unfold transportedOrdinary
  exact transportTensor_natural F G e k hk b d

private theorem transportedOrdinary_cancel
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (F G : SiteMod J R ⥤
      SiteMod K S) (e : F ≅ G)
    (k : ∀ M N : SiteMod J R,
      F.obj (siteTensor J R M N) ≅
        siteTensor K S (F.obj M) (F.obj N))
    (M N : SiteMod J R) :
    letI := SheafOfModules.monoidalCategory S
    e.hom.app (siteTensor J R M N) ≫
        (transportedOrdinary.{c, v, r} J K R S F G e k M N).hom =
      (k M N).hom ≫ (tensorIso (e.app M) (e.app N)).hom := by
  let := SheafOfModules.monoidalCategory S
  unfold transportedOrdinary
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  exact Iso.hom_inv_id_app_assoc e _ _

end OrdinaryTransport

end TensorTransport

section SiteComparison
open SheafOfModules.GeometricConstruction

private abbrev modulePush
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (g : C ⥤ D) [g.IsContinuous J K]
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (φ : R ⟶ (g.sheafPushforwardContinuous CommRingCat.{r} J K).obj S) :=
  SheafOfModules.pushforward.{r} (F := g) (J := J) (K := K)
    (R := base S) (S := base R)
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Transport the normalized pure pairing through the comparison of left adjoints.
The unit formula identifies its transpose with the specified lax tensor map. -/
private theorem ordinaryUnitPure
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (g : C ⥤ D) [g.IsContinuous J K]
    (RY : Sheaf J CommRingCat.{r}) (RX : Sheaf K CommRingCat.{r})
    (φ : RY ⟶ (g.sheafPushforwardContinuous CommRingCat.{r} J K).obj RX)
    (L : Sheaf J (Type (r)) ⥤ Sheaf K (Type (r)))
    (a : L ⊣ g.sheafPushforwardContinuous (Type (r)) J K)
    [PreservesFiniteLimits L]
    (F₀ F : SiteMod J RY ⥤
      SiteMod K RX)
    (adj : F ⊣ modulePush.{c, v, r} g RY RX φ) (e : F₀ ≅ F)
    (k : ∀ M N, F₀.obj (siteTensor J RY M N) ≅
      siteTensor K RX (F₀.obj M) (F₀.obj N))
    (ins : ∀ T, L.obj ((mset RY).obj T) ⟶ (mset RX).obj (F₀.obj T))
    (transpose : ∀ T H (b : F.obj T ⟶ H),
      (mset RY).map (adj.homEquiv T H b) =
        a.homEquiv _ _ (ins T ≫ (mset RX).map (e.hom.app T ≫ b)))
    (pure : ∀ M N U v,
      (L.map (SheafOfModules.CochainInversePairing.pureSheaf RY M N) ≫
        ins (siteTensor J RY M N) ≫
          (mset RX).map (k M N).hom).hom.app U v =
      sitePure K RX (F₀.obj M) (F₀.obj N) U
        ((L.map (CartesianMonoidalCategory.fst ((mset RY).obj M) ((mset RY).obj N)) ≫
          ins M).hom.app U v)
        ((L.map (CartesianMonoidalCategory.snd ((mset RY).obj M) ((mset RY).obj N)) ≫
          ins N).hom.app U v))
    : ∀ M N (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      (transportedOrdinary.{c, v, r} J K RY RX F₀ F e k M N).hom.val.app (g.op.obj U)
        ((adj.unit.app (siteTensor J RY M N)).val.app U
          (sitePure J RY M N U x y)) =
      sitePure K RX (F.obj M) (F.obj N) (g.op.obj U)
        ((adj.unit.app M).val.app U x) ((adj.unit.app N).val.app U y) := by
  intro M N U x y
  have un (T : SiteMod J RY) (z : T.val.obj U) :
      (adj.unit.app T).val.app U z =
        (e.hom.app T).val.app (g.op.obj U)
          ((ins T).hom.app (g.op.obj U)
            ((a.unit.app ((mset RY).obj T)).hom.app U z)) := by
    have h := transpose T (F.obj T) (𝟙 _)
    rw [adj.homEquiv_id, Category.comp_id, Adjunction.homEquiv_unit] at h
    exact congrArg (fun q ↦ q.hom.app U z) h
  have hu {A B : Sheaf J (Type (r))} (q : A ⟶ B) (z : A.obj.obj U) :
      (L.map q).hom.app (g.op.obj U) ((a.unit.app A).hom.app U z) =
        (a.unit.app B).hom.app U (q.hom.app U z) := by
    exact (congrArg (fun q ↦ q.hom.app U z) (a.unit.naturality q)).symm
  let Z := (mset RY).obj M ⊗ (mset RY).obj N
  have h := pure M N (g.op.obj U) ((a.unit.app Z).hom.app U (x, y))
  change (k M N).hom.val.app (g.op.obj U)
    ((ins (siteTensor J RY M N)).hom.app (g.op.obj U)
      ((L.map (SheafOfModules.CochainInversePairing.pureSheaf RY M N)).hom.app
        (g.op.obj U) ((a.unit.app Z).hom.app U (x, y)))) = _ at h
  erw [hu] at h
  change (k M N).hom.val.app (g.op.obj U)
    ((ins (siteTensor J RY M N)).hom.app (g.op.obj U)
      ((a.unit.app ((mset RY).obj (siteTensor J RY M N))).hom.app U
        (sitePure J RY M N U x y))) =
    sitePure K RX (F₀.obj M) (F₀.obj N) (g.op.obj U)
      ((ins M).hom.app (g.op.obj U)
        ((L.map (CartesianMonoidalCategory.fst ((mset RY).obj M) ((mset RY).obj N))).hom.app
          (g.op.obj U) ((a.unit.app Z).hom.app U (x, y))))
      ((ins N).hom.app (g.op.obj U)
        ((L.map (CartesianMonoidalCategory.snd ((mset RY).obj M) ((mset RY).obj N))).hom.app
          (g.op.obj U) ((a.unit.app Z).hom.app U (x, y)))) at h
  erw [hu, hu] at h
  have hcancel := congrArg (fun q ↦ q.val.app (g.op.obj U)
    ((ins (siteTensor J RY M N)).hom.app (g.op.obj U)
      ((a.unit.app ((mset RY).obj (siteTensor J RY M N))).hom.app U
        (sitePure J RY M N U x y))))
    (transportedOrdinary_cancel.{c, v, r} J K RY RX F₀ F e k M N)
  rw [un]
  change (transportedOrdinary.{c, v, r} J K RY RX F₀ F e k M N).hom.val.app _
    ((e.hom.app (siteTensor J RY M N)).val.app _ _) = _
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hcancel
  erw [hcancel]
  change (MonoidalCategory.tensorIso (e.app M) (e.app N)).hom.val.app _
    ((k M N).hom.val.app _ _) = _
  erw [h]
  rw [un M x, un N y]
  exact SheafOfModules.CochainScalarConstruction.pure_map RX
    (e.hom.app M) (e.hom.app N) (g.op.obj U) _ _

/-- Retain the object and map presentation, keeping its functor abstract in consumers.
This packages the normalized extension-of-scalars adjunction just constructed. -/
private theorem abstractNormalizedAdjunction
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type (r)) ⥤ Sheaf J (Type (r)))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (r)) K J)
    [PreservesFiniteLimits L]
    (A : Sheaf J CommRingCat.{r}) (B : Sheaf K CommRingCat.{r})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} K J).obj A)
    (RI : Sheaf J CommRingCat.{r}) (I : AlgebraicInverseImage L B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset B) (rset A)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map φ)) :
    ∃ F₀ : SiteMod K B ⥤ SiteMod J A,
      ∃ hobj : ∀ M, F₀.obj M = SheafOfModules.changeOfRings c (I.modules.obj M),
        (∀ {M N} (b : M ⟶ N), F₀.map b = eqToHom (hobj M) ≫
          SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map b) ≫
            eqToHom (hobj N).symm) ∧
        ∃ am : F₀ ⊣
          SheafOfModules.pushforward.{r} (F := F) (J := K) (K := J)
            (R := base A) (S := base B)
            ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).map φ), ∀ M H a,
          (mset B).map (am.homEquiv M H a) =
            adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫
              SheafOfModules.CochainTensorComparison.scalarInsertion B A RI L I c
                F₀ hobj M ≫ (mset A).map a) := by
  refine ⟨I.modules ⋙ SemilinearSections.tensorFunctor.{c, v, r} c, fun _ ↦ rfl, ?_, ?_⟩
  · intros
    rfl
  · exact normalizedAdjunction.{c, v, r} F L adj A B φ RI I c hc

private theorem ordinaryOnSites
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (g : C ⥤ D) [g.IsContinuous J K]
    (RY : Sheaf J CommRingCat.{r}) (RX : Sheaf K CommRingCat.{r})
    (φ : RY ⟶ (g.sheafPushforwardContinuous CommRingCat.{r} J K).obj RX)
    (L : Sheaf J (Type (r)) ⥤ Sheaf K (Type (r)))
    (a : L ⊣ g.sheafPushforwardContinuous (Type (r)) J K)
    [PreservesFiniteLimits L]
    (RI : Sheaf K CommRingCat.{r})
    (I : SheafOfModules.AlgebraicInverseImage L RY RI) (c : RI ⟶ RX)
    (hc : (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map c =
      I.ringUnderlying.inv ≫ (a.homEquiv (rset RY) (rset RX)).symm
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map φ))
    (F : SiteMod J RY ⥤
      SiteMod K RX)
    (adj : F ⊣ modulePush.{c, v, r} g RY RX φ)
    [F.Additive] :
    ∃ ordinary : ∀ M N : SiteMod J RY,
      F.obj (siteTensor J RY M N) ≅
        siteTensor K RX (F.obj M) (F.obj N),
      (∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
        F.map (siteTensorHom J RY a b) ≫ (ordinary M' N').hom =
          (ordinary M N).hom ≫ siteTensorHom K RX (F.map a) (F.map b)) ∧
      (∀ M N (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
        (ordinary M N).hom.val.app (g.op.obj U)
          ((adj.unit.app (siteTensor J RY M N)).val.app U
            (sitePure J RY M N U x y)) =
        sitePure K RX (F.obj M) (F.obj N) (g.op.obj U)
          ((adj.unit.app M).val.app U x) ((adj.unit.app N).val.app U y)) ∧
      ∀ P : CochainComplex (SiteMod J RY) ℤ,
        P.IsKFlatIndependentCoefficients → siteFlatTerms J RY P →
        CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := RX)
            ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
          siteFlatTerms K RX ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let V := g.sheafPushforwardContinuous (Type (r)) J K
  obtain ⟨F₀, hobj, hmap, a₀, ha₀⟩ :=
    abstractNormalizedAdjunction.{c, v, r} g L a RX RY φ RI I c hc
  let e : F₀ ≅ F := Adjunction.leftAdjointUniq a₀ adj
  have eTranspose (T : SiteMod J RY)
      (H : SiteMod K RX) (b : F.obj T ⟶ H) :
      a₀.homEquiv T H (e.hom.app T ≫ b) = adj.homEquiv T H b :=
    leftAdjointUniq_transpose a₀ adj T H b
  clear_value e
  have : F₀.Additive := Functor.additive_of_iso e.symm
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  obtain ⟨k, hkNatural, hkPure⟩ :=
    SheafOfModules.CochainTensorComparison.normalizedTensorator_exists
      RY RX RI L I c F₀ hobj V a hmap
  let := SheafOfModules.monoidalCategory RY
  let := SheafOfModules.monoidalCategory RX
  let ins := fun T : SiteMod J RY ↦
    I.moduleUnderlying.inv.app T ≫
      SheafOfModules.CochainTensorComparison.scalarInsertion RY RX RI L I c F₀ hobj T
  have hins (T : SiteMod J RY) : ins T =
      I.moduleUnderlying.inv.app T ≫
        SheafOfModules.CochainTensorComparison.scalarInsertion RY RX RI L I c F₀ hobj T :=
    rfl
  clear_value ins
  have transpose (T : SiteMod J RY)
      (H : SiteMod K RX) (b : F.obj T ⟶ H) :
      (mset RY).map (adj.homEquiv T H b) =
        a.homEquiv _ _ (ins T ≫ (mset RX).map (e.hom.app T ≫ b)) := by
    rw [← eTranspose T H b, hins]
    exact ha₀ T H (e.hom.app T ≫ b)
  have hpure M N U v :
      (L.map (SheafOfModules.CochainInversePairing.pureSheaf RY M N) ≫
        ins (siteTensor J RY M N) ≫
          (mset RX).map (k M N).hom).hom.app U v =
      sitePure K RX (F₀.obj M) (F₀.obj N) U
        ((L.map (CartesianMonoidalCategory.fst ((mset RY).obj M) ((mset RY).obj N)) ≫
          ins M).hom.app U v)
        ((L.map (CartesianMonoidalCategory.snd ((mset RY).obj M) ((mset RY).obj N)) ≫
          ins N).hom.app U v) := by
    simp only [hins]
    exact hkPure M N ((mset RY).obj M ⊗ (mset RY).obj N)
      (CartesianMonoidalCategory.fst ((mset RY).obj M) ((mset RY).obj N))
      (CartesianMonoidalCategory.snd ((mset RY).obj M) ((mset RY).obj N))
      (SheafOfModules.CochainInversePairing.pureSheaf RY M N)
      (fun W v ↦ sitePureSheaf_apply J RY M N W v.1 v.2) U v
  have hflat (P : CochainComplex (SiteMod J RY) ℤ)
      (hp : P.IsKFlatIndependentCoefficients) (hf : siteFlatTerms J RY P) :
      CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := RX)
          ((F₀.mapHomologicalComplex (.up ℤ)).obj P) ∧
        siteFlatTerms K RX ((F₀.mapHomologicalComplex (.up ℤ)).obj P) :=
    SheafOfModules.isKFlat_ringedToposPullback L V a I c F₀
      hobj hmap P hp hf
  clear hkPure ha₀ eTranspose a₀
  let ordinary := transportedOrdinary.{c, v, r} J K RY RX F₀ F e k
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  have ordinary_natural := @transportedOrdinary_natural.{c, v, r} _ _ _ _ _ _ _
    J K RY RX F₀ F e k hkNatural
  refine ⟨ordinary, ordinary_natural, ?_, ?_⟩
  · exact ordinaryUnitPure.{c, v, r} J K g RY RX φ L a F₀ F adj e k ins transpose
      hpure
  · intro P hp hf
    obtain ⟨hk, hflat⟩ := hflat P hp hf
    let i : ((F₀.mapHomologicalComplex (.up ℤ)).obj P) ≅
        ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
      (NatIso.mapHomologicalComplex e (.up ℤ)).app P
    clear_value i
    refine ⟨SheafOfModules.kFlat_iso_independent RX i hk, ?_⟩
    intro n
    exact SheafOfModules.flatOnSite_of_iso RX (e.app (P.X n)) (hflat n)

/-- Compare the two names for the sheafification image of a pure tensor once,
with abstract modules, before specializing the module arguments to pullbacks. -/
private theorem sitePure_eq
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    (M N : SiteMod J R) (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    sitePure J R M N V x y = tensorSectionAtSize J R M N V x y := by
  unfold sitePure tensorSectionAtSize SheafOfModules.CochainScalarConstruction.pure
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_generator_pure
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (U : C ⥤ D) [U.IsContinuous J K]
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (φ : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)
    (F : SiteMod J R ⥤
      SiteMod K S)
    (adj : F ⊣ modulePush.{c, v, r} U R S φ)
    (e : ∀ M N : SiteMod J R,
      F.obj (siteTensor J R M N) ≅
        siteTensor K S (F.obj M) (F.obj N))
    (hunit : ∀ M N V x y,
      (e M N).hom.val.app (op (U.obj V))
        ((adj.unit.app (siteTensor J R M N)).val.app (op V)
          (sitePure J R M N (op V) x y)) =
      sitePure K S (F.obj M) (F.obj N) (op (U.obj V))
        ((adj.unit.app M).val.app (op V) x)
        ((adj.unit.app N).val.app (op V) y))
    (M N : SiteMod J R)
    (V : C) (W : D) (p : W ⟶ U.obj V)
    (x : M.val.obj (op V)) (y : N.val.obj (op V)) (r : S.obj.obj (op W)) :
    (e M N).hom.val.app (op W)
      (((F.obj (siteTensor J R M N)).val.obj (op W)).isModule.toSMul.smul r
        ((F.obj (siteTensor J R M N)).val.map p.op
        ((adj.unit.app (siteTensor J R M N)).val.app (op V)
          (sitePure J R M N (op V) x y)))) =
      sitePure K S (F.obj M) (F.obj N) (op W)
        (((F.obj M).val.obj (op W)).isModule.toSMul.smul r
          ((F.obj M).val.map p.op ((adj.unit.app M).val.app (op V) x)))
        (1 • (F.obj N).val.map p.op ((adj.unit.app N).val.app (op V) y)) := by
  erw [map_smul, PresheafOfModules.naturality_apply, hunit,
    SheafOfModules.CochainScalarConstruction.pure_restrict S, one_smul]
  exact sitePure_smul K S (F.obj M) (F.obj N) (op W) r _ _

/-- Keep the concrete geometric lift behind its ring and module presentation. -/
private theorem geometricPresentation
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U]
    (R : Sheaf J CommRingCat.{r}) :
    ∃ L : Sheaf J (Type r) ⥤ Sheaf K (Type r),
      ∃ _a : L ⊣ U.sheafPushforwardContinuous (Type r) J K,
        PreservesFiniteLimits L ∧ ∃ RI : Sheaf K CommRingCat.{r},
          Nonempty (SheafOfModules.AlgebraicInverseImage L R RI) := by
  classical
  let : HasFiniteLimits (Sheaf J (Type r)) := setSheafFiniteLimits J
  let : HasFiniteLimits (Sheaf K (Type r)) := setSheafFiniteLimits K
  have : UnivLE.{v, r} :=
    @UnivLE.trans.{v, max c v, r} inferInstance inferInstance
  have : AB5OfSize.{v, max c v} (Type (r)) :=
    AB5OfSize_of_univLE.{v, max c v, r, r} _
  let L := Functor.sheafPullbackConstruction.sheafPullback U (Type (r)) J K
  let V := U.sheafPushforwardContinuous (Type (r)) J K
  let a : L ⊣ V := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U (Type (r)) J K
  have : HasSheafify J (Type (r)) := hasSheafifyEssentiallySmallSite _ _
  have : HasSheafify K (Type (r)) := hasSheafifyEssentiallySmallSite _ _
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  let := BraidedCategory.ofCartesianMonoidalCategory (C := Sheaf J (Type (r)))
  let := BraidedCategory.ofCartesianMonoidalCategory (C := Sheaf K (Type (r)))
  let : L.Monoidal := Functor.Monoidal.ofChosenFiniteProducts L
  have : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let RI := SheafOfModules.CochainCompositeConstruction.ringImage L R
  let I : SheafOfModules.AlgebraicInverseImage L R RI :=
    SheafOfModules.CochainCompositeConstruction.algebraicImage L R
  clear_value I RI a L
  exact ⟨L, a, inferInstance, RI, ⟨I⟩⟩

attribute [-instance] setSheafProducts setSheafFiniteLimits
attribute [-instance] additiveSheafification
attribute [-instance] additiveWeakSheafification additiveLocallyBijective setSheafification

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary tensor comparison, uniquely normalized on scalar-extension generators. -/
theorem sitePullbackTensorGenerators
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U]
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (φ : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)
    (F : SemilinearSections.Mod.{c, v, r} J R ⥤
      SemilinearSections.Mod.{c, v, r} K S) [F.Additive]
    (adj : F ⊣ SheafOfModules.pushforward.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)) :
    ∃! _data : OrdinaryTensorPullbackData.{c, v, r} J K U R S φ F adj, True := by
  classical
  obtain ⟨L, a, hL, RI, ⟨I⟩⟩ := geometricPresentation J K U R
  have : PreservesFiniteLimits L := hL
  obtain ⟨c, hc⟩ := siteStructuralMap_exists.{c, v, r} U L a S R φ RI I
  obtain ⟨e, he, hu, hf⟩ := ordinaryOnSites.{c, v, r} J K U R S φ L a RI I c hc
    F adj
  have hn : OrdinaryTensorNormalized J K U R S φ F adj e := by
    refine ⟨?_, ?_⟩
    · intro M N V W p x y r
      simp only [← sitePure_eq]
      rw [map_smul, PresheafOfModules.naturality_apply]
      erw [hu M N (op V) x y]
      exact (congrArg
        (fun z : (siteTensor K S (F.obj M) (F.obj N)).val.obj (op W) ↦ r • z)
        (SheafOfModules.CochainScalarConstruction.pure_restrict S (F.obj M) (F.obj N)
          p.op ((adj.unit.app M).val.app (op V) x)
          ((adj.unit.app N).val.app (op V) y))).trans
        (sitePure_smul K S (F.obj M) (F.obj N) (op W) r _ _)
    · intro M M' N N' a b
      exact he a b
  let data : OrdinaryTensorPullbackData.{c, v, r} J K U R S φ F adj := ⟨e, hn, hf⟩
  refine ⟨data, trivial, ?_⟩
  intro other _
  have he : other.ordinary = e := by
    let e' := other.ordinary
    have he' := other.normalized
    funext M N
    apply Iso.ext
    apply (adj.homEquiv _ _).injective
    apply SheafOfModules.CochainScalarConstruction.pure_hom_ext R M N _
    intro V x y
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have ht' := he'.1 M N V.unop (U.obj V.unop) (𝟙 _) x y 1
    simp only [op_id, PresheafOfModules.map_id, one_smul, ← sitePure_eq] at ht'
    exact ht'.trans (hu M N V x y).symm
  cases other
  dsimp only at he
  cases he
  rfl

end SiteComparison
end WeilConjectures.SemilinearSections
