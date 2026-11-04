import Langlands.Representation.Plancherel.LeviInflatedNormalization
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-! # Positive Levi normalization on actual standard rational-point subgroups -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open GroupScheme Aubert.General Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

universe u v

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  [ValuativeRel k] [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rationalLeviNormalizationPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (I : Finset (SimpleRoot i ν))

local notation "D" =>
  isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I

local notation "hU" =>
  standardUnipotent_isClosed_of_standardCocharacterStatement i ν hStandard hG hi hν I

/-- The positive Levi-half-modulus induction on the literal standard point
subgroups, conditional on the existing standard-cocharacter assertion. -/
abbrev standardLeviInflatedInductionFunctorOfStandardCocharacter :
    SmoothRep.{0, u, v} ℂ (levi i ν I) ⥤
      SmoothRep.{0, u, max u v} ℂ (RationalPoint k G.X) :=
  DynamicNormalization.leviTwistedInductionFunctor D hU

/-- The standard radical's proved compact containment supplies unimodularity;
no radical-unimodularity or normalization comparison is an input. -/
def standardNormalizedInductionLeviIsoOfStandardCocharacter :
    normalizedInductionFunctor.{u, v} D hU ≅
      standardLeviInflatedInductionFunctorOfStandardCocharacter
        i ν hStandard hG hi hν I :=
  DynamicNormalization.normalizedInductionLeviTwistIso D hU
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU)

/-- Full-parabolic covariance on the actual standard points is equivalent
to the literal positive Levi covariance from Waldspurger I.3. -/
theorem standardNormalized_covariant_iff_leviOfStandardCocharacter
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I))
    (f : RationalPoint k G.X → A) :
    (∀ (p : parabolic i ν I) (x : RationalPoint k G.X),
      f ((p : RationalPoint k G.X) * x) = inducingRepresentation D hU A p (f x)) ↔
        LeviNormalizedCovariant D hU A f :=
  normalized_covariant_iff_levi D hU
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU) A f

/-- The converse on actual functions: source covariance and a uniform open
right stabilizer construct an element of full-parabolic normalized induction. -/
def standardNormalizedFunctionOfStandardCocharacter
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I))
    (f : RationalPoint k G.X → A) (hf : LeviNormalizedCovariant D hU A f)
    (K : OpenSubgroup (RationalPoint k G.X))
    (hK : ∀ (a : K) (x : RationalPoint k G.X), f (x * (a : RationalPoint k G.X)) = f x) :
    (normalizedInductionFunctor D hU).obj A :=
  SmoothRep.hom
    ((standardNormalizedInductionLeviIsoOfStandardCocharacter
      i ν hStandard hG hi hν I).app A).inv
    (leviNormalizedFunctionOf D hU A f hf K hK)

end Langlands.Plancherel
