import Langlands.Representation.Aubert.General.RationalGeometricSurvivors
import Langlands.Representation.Aubert.General.ConjugationComposition

/-! # Actual geometric terms for arbitrary lifts of a surviving Weyl class -/

noncomputable section

universe uI uG uV u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Generic

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] {Index : Type uI}
  (P M U : Finset Index → Subgroup H)
  (hM : ∀ I, IsClosed (M I : Set H)) (hU : ∀ I, IsClosed (U I : Set H))

/-- An actual geometric term at an element of its Levi is the original object. -/
def geometricTermInnerIso (J : Finset Index) (m : H) (hm : m ∈ M J)
    (hs : GeometricSourceDecomposition P M U J J m)
    (ht : GeometricTargetDecomposition P M U J J m)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    (geometricTermFunctor P M U hM hU J J m hs ht).obj A ≅ A :=
  geometricTermFullLeviIso P M U hM hU J J m hs ht
    (conjugationMembership_inner ⟨m, hm⟩) A ≪≫ conjugationFunctorInnerIso ⟨m, hm⟩ A

/-- Multiplying a full-Levi representative on the right by a source-Levi
element changes its geometric term by an actual representation isomorphism. -/
def geometricTermRightInnerIso (I J : Finset Index) (n : H) (m : M J)
    (hs : GeometricSourceDecomposition P M U I J (n * (m : H)))
    (ht : GeometricTargetDecomposition P M U I J (n * (m : H)))
    (hConj : ∀ x : H, x ∈ M I ↔ n⁻¹ * x * n ∈ M J)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    (geometricTermFunctor P M U hM hU I J (n * (m : H)) hs ht).obj A ≅
      (conjugationFunctor n hConj).obj A :=
  geometricTermFullLeviIso P M U hM hU I J (n * (m : H)) hs ht
      (conjugationMembership_mul (m : H) n (conjugationMembership_inner m) hConj) A ≪≫
    (conjugationFunctorCompIsoApp (m : H) n
      (conjugationMembership_inner m) hConj A).symm ≪≫
    (conjugationFunctor n hConj).mapIso (conjugationFunctorInnerIso m A)

/-- The full-Levi term is independent, up to an actual isomorphism, of the
normalizer lift of its Weyl class when the source contains the full centralizer. -/
def geometricTermSameWeylClassIso (S : Subgroup H) (I J : Finset Index)
    (hZJ : Group.RelativeWeyl.centralizer S ≤ M J)
    (n r : Group.RelativeWeyl.normalizer S)
    (hnr : (QuotientGroup.mk n : Group.RelativeWeyl.Weyl S) = QuotientGroup.mk r)
    (hs : GeometricSourceDecomposition P M U I J (n : H))
    (ht : GeometricTargetDecomposition P M U I J (n : H))
    (hConj : ∀ x : H, x ∈ M I ↔ (r : H)⁻¹ * x * r ∈ M J)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    (geometricTermFunctor P M U hM hU I J (n : H) hs ht).obj A ≅
      (conjugationFunctor (r : H) hConj).obj A := by
  have hdZ : (r : H)⁻¹ * (n : H) ∈ Group.RelativeWeyl.centralizer S :=
    (QuotientGroup.eq.mp hnr.symm : r⁻¹ * n ∈ Group.RelativeWeyl.denominator S)
  let d : M J := ⟨(r : H)⁻¹ * (n : H), hZJ hdZ⟩
  have hd : (r : H) * (d : H) = (n : H) := by
    dsimp [d]
    simp only [mul_inv_cancel_left]
  have hs' : GeometricSourceDecomposition P M U I J ((r : H) * (d : H)) := by
    rw [hd]
    exact hs
  have ht' : GeometricTargetDecomposition P M U I J ((r : H) * (d : H)) := by
    rw [hd]
    exact ht
  simpa only [hd] using
    geometricTermRightInnerIso P M U hM hU I J (r : H) d hs' ht' hConj A

/-- Pullback by the inverse representative is pullback along the inverse
of the original actual conjugation equivalence. -/
def conjugationFunctorInversePullbackIso
    (I J : Finset Index) (n : H)
    (hConj : ∀ x : H, x ∈ M J ↔ n⁻¹ * x * n ∈ M I)
    (A : SmoothRep.{0, uG, uV} ℂ (M J)) :
    (conjugationFunctor n⁻¹ (conjugationMembership_inv n hConj)).obj A ≅
      (SmoothRep.pullbackFunctor (conjugationEquiv n hConj).symm).obj A := by
  refine SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) ?_)
  intro m
  ext v
  change A.representation _ v = A.representation _ v
  apply congrArg (fun x => A.representation x v)
  apply Subtype.ext
  change n⁻¹⁻¹ * (m : H) * n⁻¹ = n * (m : H) * n⁻¹
  rw [inv_inv]

/-- Any lift of an inverse reference class gives the inverse reference
pullback when the reference conjugates the full Levis. -/
def geometricTermSameInverseWeylClassIso (S : Subgroup H) (I J : Finset Index)
    (hZJ : Group.RelativeWeyl.centralizer S ≤ M J)
    (n r : Group.RelativeWeyl.normalizer S)
    (hrn : (QuotientGroup.mk r : Group.RelativeWeyl.Weyl S) = QuotientGroup.mk n⁻¹)
    (hs : GeometricSourceDecomposition P M U I J (r : H))
    (ht : GeometricTargetDecomposition P M U I J (r : H))
    (hConj : ∀ x : H, x ∈ M J ↔ (n : H)⁻¹ * x * n ∈ M I)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    (geometricTermFunctor P M U hM hU I J (r : H) hs ht).obj A ≅
      (SmoothRep.pullbackFunctor (conjugationEquiv (n : H) hConj).symm).obj A :=
  geometricTermSameWeylClassIso P M U hM hU S I J hZJ r n⁻¹ hrn hs ht
      (conjugationMembership_inv (n : H) hConj) A ≪≫
    conjugationFunctorInversePullbackIso M I J (n : H) hConj A

end Generic

namespace RationalPointFamily

open SmoothRep GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hZ : HasPointCentralizerComparison i)

include hZ in
/-- A lift of the identity full-centralizer quotient class lies in every
actual standard Levi. -/
theorem normalizerLift_mem_levi_of_mk_eq_one
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : (QuotientGroup.mk n : Weyl i) = 1) :
    (n : RationalPoint k G.X) ∈ levi i ν J := by
  have hnZ : n ∈ Group.RelativeWeyl.denominator (torusPoints i) :=
    (QuotientGroup.eq_one_iff n).mp hn
  exact centralizerPoints_le_levi i ν J (hZ.symm ▸ hnZ)

variable [TopologicalSpace k]

local instance rationalGeometricLiftComparisonPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- Every actual normalizer lift of Weyl class one gives the original object
as its actual normalized self geometric term. -/
def pointGeometricTermIdentityClassIso
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : (QuotientGroup.mk n : Weyl i) = 1)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J J (n : RationalPoint k G.X))
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J J (n : RationalPoint k G.X))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
    (geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J J n hs ht).obj σ ≅ σ :=
  geometricTermInnerIso.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J n
    (normalizerLift_mem_levi_of_mk_eq_one i ν hZ J n hn) hs ht σ

variable [Mono i.hom.hom.left]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})
  (hN : HasPointNormalizerComparison i)
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
  (hMin : minimalityLengthCriterion actual)

/-- An arbitrary inverse-longest class lift gives transport along the inverse
associated-Levi equivalence for any fixed chosen longest lift. -/
def pointGeometricTermInverseLongestClassIso
    (hAssoc : associatedSubsetLaws actual) (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep actual J)
    (r : Group.RelativeWeyl.normalizer (torusPoints i))
    (hr : QuotientGroup.mk r = (longestRep actual J)⁻¹)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
      (associatedSubset actual J) J (r : RationalPoint k G.X))
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
      (associatedSubset actual J) J (r : RationalPoint k G.X))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
    (geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
      (associatedSubset actual J) J r hs ht).obj σ ≅
      (SmoothRep.pullbackFunctor (associatedLeviConjugationEquiv i ν hG hi hν
        (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
        hN hZ actual hLength hSimple hMin hAssoc J n hn).symm).obj σ := by
  have hZJ : Group.RelativeWeyl.centralizer (torusPoints i) ≤ levi i ν J :=
    hZ ▸ centralizerPoints_le_levi i ν J
  have hrn : (QuotientGroup.mk r : Weyl i) = QuotientGroup.mk n⁻¹ := by
    rw [QuotientGroup.mk_inv, hn]
    exact hr
  have hConj := conjugationMembership_of_map_eq (n : RationalPoint k G.X)
    (associatedLeviConjugation_of_standard i ν hG hi hν
      (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
      hN hZ actual hLength hSimple hMin hAssoc J n hn)
  exact geometricTermSameInverseWeylClassIso.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
    (torusPoints i) (associatedSubset actual J) J hZJ n r hrn hs ht
    hConj σ

end RationalPointFamily

end Langlands.Aubert.General
