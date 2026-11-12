import Langlands.Representation.Aubert.General.RationalGeometricFiltrationCollapse

/-! # Ordered actual geometric filtrations for maximal standard source Levis -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

section Datum

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance maximalSourceFiltrationPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)

/-- An actual geometric filtration, with every minimal class once, and with
identity last for a self composite. This structure asserts no existence. -/
structure PointGeometricObjectFiltration (I J : Finset (SimpleRoot i ν))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) where
  tailLength : ℕ
  enumeration : Fin (tailLength + 1) ≃ {w : Weyl i // w ∈ minimalReps actual I J}
  lift : Fin (tailLength + 1) → Group.RelativeWeyl.normalizer (torusPoints i)
  lift_class : ∀ q, QuotientGroup.mk (lift q) = (enumeration q).val
  source : ∀ q, GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (lift q)
  target : ∀ q, GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (lift q)
  filtration : ObjectRepFiltration
    (pointInducedJacquetObject i ν hG hi hν hStandard hU I J σ).obj (tailLength + 1)
  grade : ∀ q, filtration.gradedRepresentation q ≅
    ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
      I J (lift q) (source q) (target q)).obj σ).obj
  identity_last : I = J → (enumeration (Fin.last tailLength)).val = 1

end Datum

/-- The actual geometric lemma for maximal standard sources, retaining the
closed identity orbit as the final grade of each self composite. No proof is
supplied; no cuspidality or self-association is assumed. -/
def RationalMaximalSourceGeometricFiltrationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (_hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      ∀ [Fintype (Weyl i)]
        (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
        (C : CoxeterMatrix (SimpleRoot i ν))
        (actual : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ actual →
        PositiveSimpleReflectionComparison i ν hN hZ actual →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) actual →
        minimalityLengthCriterion actual → associatedSubsetLaws actual →
        ∀ (J : Finset (SimpleRoot i ν)), IsMaximalStandard J →
          ∀ (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
            (I : Finset (SimpleRoot i ν)), I ≠ Finset.univ →
            Nonempty (PointGeometricObjectFiltration.{u, v}
              i ν hG hi hν hStandard hM hU actual I J σ)

end Langlands.Aubert.General.RationalPointFamily
