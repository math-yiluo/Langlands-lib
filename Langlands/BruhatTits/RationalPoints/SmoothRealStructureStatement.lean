import Langlands.GroupScheme.Rational.CenterSplitComponent
import Langlands.GroupScheme.Derived.Basic
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Local-point prerequisites for smooth real characters

These are proposition targets over the existing actual point groups. In particular,
the scheme-theoretic derived points are not identified with abstract commutators.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Compactness of the full scheme-center intersection with the actual common norm kernel,
in the canonical topology on the ambient rational points. -/
def CentralNormKernelCompactness
    (M : GroupScheme (Spec (CommRingCat.of F)))
    (hM : GroupScheme.IsConnectedReductive M) : Prop :=
  letI : IsAffineHom M.X.hom := hM.isAffineHom
  letI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  IsCompact ((GroupScheme.schemeCenterPoints M ⊓
    Plancherel.rationalCommonNormKernel M) : Set (GroupScheme.rationalPoints M))

/-- The norm kernel modulo its central points and the actual scheme-theoretic derived
points is compact in the inherited subgroup and quotient topologies. -/
def CentralDerivedNormKernelCocompactness
    (M : GroupScheme (Spec (CommRingCat.of F)))
    (hM : GroupScheme.IsConnectedReductive M) : Prop :=
  letI : IsAffineHom M.X.hom := hM.isAffineHom
  letI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  let K := Plancherel.rationalCommonNormKernel M
  let D := (GroupScheme.derivedSubgroup M).carrier (Over.mk (𝟙 _))
  CompactSpace (K ⧸ (((GroupScheme.schemeCenterPoints M ⊓ K) ⊔ D).subgroupOf K))

/-- Every ambient open-kernel real homomorphism kills the actual scheme-theoretic
derived points. This is a local-point theorem target, not abstract commutator equality. -/
def DerivedSmoothRealAnnihilation
    (M : GroupScheme (Spec (CommRingCat.of F)))
    (hM : GroupScheme.IsConnectedReductive M) : Prop :=
  letI : IsAffineHom M.X.hom := hM.isAffineHom
  letI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  ∀ f : GroupScheme.rationalPoints M →* Multiplicative ℝ,
    IsOpen (f.ker : Set (GroupScheme.rationalPoints M)) →
      (GroupScheme.derivedSubgroup M).carrier (Over.mk (𝟙 _)) ≤ f.ker

/-- The central compactness target for every connected reductive local-field group. -/
def CentralNormKernelCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : GroupScheme (Spec (CommRingCat.of F))) (hM : GroupScheme.IsConnectedReductive M),
    CentralNormKernelCompactness M hM

/-- The central-derived cocompactness target for every connected reductive local-field group. -/
def CentralDerivedNormKernelCocompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : GroupScheme (Spec (CommRingCat.of F))) (hM : GroupScheme.IsConnectedReductive M),
    CentralDerivedNormKernelCocompactness M hM

/-- The derived-point annihilation target for every connected reductive local-field group. -/
def DerivedSmoothRealAnnihilationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : GroupScheme (Spec (CommRingCat.of F))) (hM : GroupScheme.IsConnectedReductive M),
    DerivedSmoothRealAnnihilation M hM

/-- The three local-point prerequisites used by the smooth-real descent route. -/
def SmoothRealStructureStatement : Prop :=
  CentralNormKernelCompactnessStatement.{u} ∧
    CentralDerivedNormKernelCocompactnessStatement.{u} ∧
      DerivedSmoothRealAnnihilationStatement.{u}

end Langlands.BruhatTits.RationalPoints
