import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement
import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Levi points of an actual rational parabolic

For a represented parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P`, the rational
points `M(F)` with their own canonical topology are identified, as a topological group,
with the literal Levi image `pointImage (l ≫ p)` in `G(F)`. This transports the
published normalized induction and Jacquet functors of the represented-parabolic
interface to smooth representations of `M(F)` itself.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- The literal point image is the identity-test carrier of the range subgroup functor. -/
theorem pointImage_eq_range_carrier (j : M ⟶ G) :
    pointImage j = (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  ext x
  exact Iff.rfl

/-- Equal subgroups of a topological group are isomorphic as topological groups. -/
def subgroupCongrContinuous {X : Type*} [Group X] [TopologicalSpace X] {H K : Subgroup X}
    (h : H = K) : H ≃ₜ* K where
  toMulEquiv := MulEquiv.subgroupCongr h
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

variable [TopologicalSpace k] [IsAffineHom G.X.hom]

local instance leviAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

section Points

/-- The canonical topology on the rational points of the Levi. Connected reductivity of
the Levi supplies the affine structure morphism. -/
abbrev leviPointTopology (l : M ⟶ P) (hl : IsRationalLeviSubgroup l) :
    TopologicalSpace (rationalPoints M) :=
  haveI := hl.isConnectedReductive.isAffineHom
  RationalPointFamily.pointTopology

/-- `M(F)`, with its own canonical topology, is the literal Levi image in `G(F)` with the
subspace topology: the point map of the closed immersion `l ≫ p` is a topological-group
isomorphism onto its image. -/
def leviPointsEquiv (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) :
    letI := leviPointTopology l hl
    rationalPoints M ≃ₜ* pointImage (l ≫ p) := by
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hc := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have : IsClosedImmersion (l ≫ p).hom.hom.left := hc
  have : IsAffine M.X.left := isAffine_of_isAffineHom (l ≫ p).hom.hom.left
  letI : TopologicalSpace (rationalPoints M) := rationalPointTopology k M.X
  let e : rationalPoints M ≃ₜ*
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    rationalPointSubgroupHomeomorph k (SubgroupFunctor.range (l ≫ p)) (l ≫ p)
      hc.isRepresentedBy_range hc
  exact e.trans (subgroupCongrContinuous (pointImage_eq_range_carrier (l ≫ p)).symm)

/-- The isomorphism is the actual point map of `l ≫ p`. -/
@[simp] theorem leviPointsEquiv_apply_coe (p : P ⟶ G) (l : M ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (m : rationalPoints M) :
    (leviPointsEquiv p l hp hl m : rationalPoints G) = rationalPoints.map (l ≫ p) m :=
  rfl

/-- `M(F)` is locally compact when `G(F)` is and the field is Hausdorff. -/
theorem leviPoints_locallyCompactSpace [T2Space k] [LocallyCompactSpace (rationalPoints G)]
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    letI := leviPointTopology l hl
    LocallyCompactSpace (rationalPoints M) := by
  let := leviPointTopology l hl
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  exact (leviPointsEquiv p l hp hl).toHomeomorph.isClosedEmbedding.locallyCompactSpace

/-- `M(F)` is a nonarchimedean group when `G(F)` is: the isomorphism with the Levi image,
which inherits the subgroup structure, is an open embedding. -/
theorem leviPoints_nonarchimedeanGroup [NonarchimedeanGroup (rationalPoints G)]
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    letI := leviPointTopology l hl
    NonarchimedeanGroup (rationalPoints M) := by
  let := leviPointTopology l hl
  let e := leviPointsEquiv p l hp hl
  have : IsTopologicalGroup (rationalPoints M) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

end Points

section Functors

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Renard's normalized parabolic induction `i_P^G` on smooth representations of `M(F)`
itself: pull back along the inverse of `leviPointsEquiv`, then apply the published
induction from the literal Levi image. -/
def leviInductionFunctor (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤
      SmoothRep.{0, u, max u v} ℂ (rationalPoints G) :=
  letI := leviPointTopology l hl
  SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙
    inductionFunctor p l r hp hr hl hmul

/-- On objects, the transported induction is the published induction of the pulled-back
representation of the Levi image. -/
theorem leviInductionFunctor_obj (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    (leviInductionFunctor p l r hp hr hl hmul).obj σ =
      (inductionFunctor p l r hp hr hl hmul).obj
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ) :=
  rfl

/-- Renard's normalized Jacquet functor `r_P^G` with values in smooth representations of
`M(F)` itself: the published Jacquet functor to the literal Levi image, followed by
pullback along `leviPointsEquiv`. -/
def leviJacquetFunctor (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints G) ⥤ SmoothRep.{0, u, v} ℂ (rationalPoints M) :=
  letI := leviPointTopology l hl
  jacquetFunctor p l r hp hr hl hmul ⋙ SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl)

/-- A Levi point acts on the transported Jacquet module through its image in `G(F)`. -/
theorem leviJacquetFunctor_obj_representation (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (m : rationalPoints M) :
    letI := leviPointTopology l hl
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation m =
      ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
        (leviPointsEquiv p l hp hl m) :=
  rfl

end Functors


end Langlands.Aubert.General.RepresentedParabolic
