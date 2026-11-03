import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.CategoryTheory.RenardCategoryDecomposition
import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.Representation.CompactCoefficient.Classes

/-!
# Renard VI.3.3.1 on the actual rational-point categories

The two factors are the published all/no irreducible-subquotient inertia
properties. The conclusion uses the actual coproduct and off-diagonal Hom
conditions of Appendix A.IX. The compact-restriction intermediate target and
the target using all proper standard Jacquet modules are separate propositions.
Neither proposition is proved here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Factors

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- The first (`true`) factor is the fixed inertia block; the second (`false`)
factor is its irreducible-subquotient complement. -/
def rationalInertiaDecompositionProperties
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Bool → ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
  | true => rationalInertiaBlockProperty G π
  | false => rationalInertiaComplementProperty G π

@[simp]
theorem rationalInertiaDecompositionProperties_true
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    rationalInertiaDecompositionProperties G π true = rationalInertiaBlockProperty G π :=
  rfl

@[simp]
theorem rationalInertiaDecompositionProperties_false
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    rationalInertiaDecompositionProperties G π false =
      rationalInertiaComplementProperty G π :=
  rfl

/-- Renard's two-factor category decomposition: every actual smooth object is
the vertex of a coproduct cofan with components in the two full subcategories,
and all morphisms in both directions between distinct factors are zero. -/
def IsRationalInertiaCategoryDecomposition
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) : Prop :=
  Renard.IsCategoryDecomposition (rationalInertiaDecompositionProperties G π)

end Factors

/-- A compact-restriction intermediate form of VI.3.3.1. Compactness means all
coefficients against the entire smooth dual of the restricted action have
compact support. It is a representation premise, not a structural input. -/
def RationalCompactRestrictionInertiaDecompositionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)),
      π.IsIrreducible →
      HasCompactSmoothDualCoefficients
        (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) π).representation →
      IsRationalInertiaCategoryDecomposition G π

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- VI.3.3.1 for an irreducible representation with vanishing normalized
Jacquet modules along every proper actual standard parabolic. The structural
standard-family premises remain visible; the source's comparison with all
proper parabolics and VI.2.1 remain separate proof obligations. -/
def RationalCuspidalInertiaDecompositionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
        π.IsIrreducible →
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π →
        IsRationalInertiaCategoryDecomposition G π

end Langlands.CuspidalSupport
