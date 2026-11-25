/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
public import WeilConjectures.AlgebraicGeometry.LatticeClassDescent
public import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
public import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
public import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
public import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
public import WeilConjectures.AlgebraicGeometry.LatticePairDescentData
public import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
public import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.LargeSetSheafification
public import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
public import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
public import WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
public import WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
public import Mathlib.Topology.Algebra.OpenSubgroup
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
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import Mathlib.Topology.CompactOpen
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification

/-!
# Constructible modules over continuous coefficient sheaves

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definitions 6.8.1 and 6.8.10
(blueprint: def-weil-pbc-continuous-constructible-module).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The constant-section map to continuous coefficients, before sheafification.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientConstants (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⟶
      (latticeCoefficientSheaf X A).obj where
  app V := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ContinuousMap.C : A →+* C(V.unop.left, A)).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- Extend constant sections through constant-ring sheafification.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientConstantMap (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ⟶ latticeCoefficientSheaf X A :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    _ _).symm (continuousCoefficientConstants X A)

/-- The actual sheafified tensor `A_X ⊗_A P`.
Source: Bhatt--Scholze, Definition 6.8.10
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientModule (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (P : ModuleCat.{u + 1} (ULift.{u + 1} A)) :
    SheafOfModules.{u + 1} (latticeModuleRing X A) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1}
    (continuousCoefficientConstantMap X A)
    ((Scheme.adicLisseConstantModules X (ULift.{u + 1} A)).obj P)

/-- The section map, precomposition with the base-change projection.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 09A5
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientDirectImageApp {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] (V : Y.ProEtᵒᵖ) :
    (latticeCoefficientSheaf Y A).obj.obj V ⟶
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (latticeCoefficientSheaf X A)).obj.obj V :=
  CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ A
        (pullback.fst V.unop.hom f).base.hom).toRingHom).comp
          ULift.ringEquiv.toRingHom))

/-- The section maps commute with restrictions.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 09A5
(blueprint: def-weil-pbc-continuous-constructible-module).
Proof: evaluate on a continuous function and a point. The two composites are
precomposition with the two sides of the naturality square of the first pullback
projection. The defining equation for the map between pullbacks identifies them.
Pointwise equality gives equality of continuous maps and ring homomorphisms. -/
theorem continuousCoefficientDirectImageApp_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A : Type u) [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {V W : Y.ProEtᵒᵖ} (g : V ⟶ W) :
    (latticeCoefficientSheaf Y A).obj.map g ≫ continuousCoefficientDirectImageApp f A W =
      continuousCoefficientDirectImageApp f A V ≫
        ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
          (latticeCoefficientSheaf X A)).obj.map g := by
  apply CommRingCat.hom_ext
  ext s : 1
  apply ULift.ext
  ext x
  change s.down ((pullback.fst W.unop.hom f ≫ g.unop.left).base x) =
    s.down ((((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left ≫
      pullback.fst V.unop.hom f).base x)
  rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  rfl

/-- Pull continuous functions back along the first projection of the base change.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 09A5
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    latticeCoefficientSheaf Y A ⟶
      (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (latticeCoefficientSheaf X A) :=
  ⟨{ app := continuousCoefficientDirectImageApp f A
     naturality := fun _ _ g ↦ continuousCoefficientDirectImageApp_naturality f A g }⟩

/-- The canonical adjoint coefficient map `f⁻¹ A_Y → A_X`.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 09A5
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientInverseImageMap {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf Y A) ⟶ latticeCoefficientSheaf X A :=
  ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
    (continuousCoefficientDirectImageMap f A)

/-- Ringed inverse image, using the canonical coefficient map and sheaf tensor.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.10; Stacks Tag 03D2
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousModulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (N : SheafOfModules.{u + 1} (latticeModuleRing Y A)) :
    SheafOfModules.{u + 1} (latticeModuleRing X A) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (continuousCoefficientInverseImageMap f A)
    ((Scheme.proEtaleModuleInverseImage f (latticeCoefficientSheaf Y A)).obj N)

/-- On a topologically noetherian scheme, a finite stratification on which the module is
pro-etale locally `A_X ⊗_A P`,
with `P` finitely presented. The cover and the module may vary with the stratum.
Source: Bhatt--Scholze, Definition 6.8.10 and Lemma 6.8.13
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def IsContinuousConstructible (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (N : SheafOfModules.{u + 1} (latticeModuleRing X A)) : Prop :=
  ∃ s : Scheme.Stratification X, ∀ k : Fin s.n,
    ∃ (I : Type (u + 1)) (V : I → (s.domain k).ProEt),
      (Scheme.ProEt.topology (s.domain k)).CoversTop V ∧
      ∀ i : I, ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A),
        Module.FinitePresentation (ULift.{u + 1} A) P ∧
        Nonempty ((continuousModulePullback (s.immersion k) A N).over (V i) ≅
          (continuousCoefficientModule (s.domain k) A P).over (V i))

end AlgebraicGeometry.ProEtale
