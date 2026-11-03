import Langlands.Representation.Exponents.SplitComponentWeights
import Langlands.GroupScheme.Rational.SplitComponentLeviPoints
import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Topology.Nonarchimedean.Subgroup

/-! # Normalized Jacquet exponents along the actual split component

Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026), VII.1.1,
printed p.220/PDF p.226. For the standard parabolic `P = M U` of the standard
rational-point family, a closed represented Levi `j : M ⟶ G` and its split component
`a : A ⟶ M`, the split-component weight subrepresentation of the normalized Jacquet
module `r^G_P(π)` is `generalizedWeightSpace` along `A(k) → M(k) → levi i ν I`.
A smooth character `χ` of `A(k)` is a normalized exponent when this subrepresentation
is nonzero. The normalized Jacquet module is `jacquetFunctor`, which twists the
`U`-coinvariants by `HaarModulus.closedInverseHalfCharacter`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))
  {M : GroupScheme (Spec (CommRingCat.of k))} (j : M ⟶ G)
  (hj : (standardLevi i ν (rootSet i ν I)).IsRepresentedBy j)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- The split-component points `A(k) → M(k) → levi i ν I` of the standard family. -/
abbrev splitComponentPointsMap (a : A.toGrp ⟶ M) : rationalPoints A.toGrp →* levi i ν I :=
  splitComponentLeviPointsMap i ν (rootSet i ν I) j hj a

/-- The split-component points are central in the standard Levi subgroup. -/
theorem splitComponentPointsMap_mem_center (ha : IsSplitComponent a) (t : rationalPoints A.toGrp) :
    splitComponentPointsMap i ν I j hj a t ∈ Subgroup.center (levi i ν I) :=
  ha.splitComponentLeviPointsMap_mem_center i ν (rootSet i ν I) j hj t

variable [TopologicalSpace k]

/-- The canonical point topology of `A(k)`; a split component is affine. -/
@[instance_reducible]
def splitComponentPointTopology (ha : IsSplitComponent a) :
    TopologicalSpace (rationalPoints A.toGrp) :=
  have := ha.isAffine
  rationalPointTopology k A.toGrp.X

local instance normalizedJacquetSplitComponentPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

/-- Continuity of the split-component points into `levi i ν I` with the subgroup topology
of the canonical topology of `G(k)`. -/
theorem continuous_splitComponentPointsMap (ha : IsSplitComponent a) :
    letI := splitComponentPointTopology ha
    Continuous (splitComponentPointsMap i ν I j hj a) := by
  have := ha.isAffine
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact continuous_splitComponentLeviPointsMap i ν (rootSet i ν I) j hj a

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (h : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))

/-- The action of a split-component point on a coinvariant class of the normalized
Jacquet module: `t · [v] = δ_P(t)^{-1/2} [π(t) v]`. -/
theorem jacquetFunctor_obj_splitComponentPointsMap_apply
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (t : rationalPoints A.toGrp) (x : π) :
    ((jacquetFunctor h hU).obj π).representation (splitComponentPointsMap i ν I j hj a t)
        (Jacquet.Localization.mk π.representation (unipotent i ν I) 1 x) =
      ((HaarModulus.closedInverseHalfCharacter (unipotent i ν I) hU (levi i ν I)
          h.levi_le_normalizer (splitComponentPointsMap i ν I j hj a t) : ℂˣ) : ℂ) •
        Jacquet.Localization.mk π.representation (unipotent i ν I) 1
          (π.representation (splitComponentPointsMap i ν I j hj a t) x) :=
  normalizedJacquetFunctor_obj_apply _ _ hU h.levi_le_normalizer π _ x

/-- Renard's `(r V)_χ` for `r = r^G_P(π)`, along the split-component points. -/
def normalizedJacquetWeightSpace (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    Subrepresentation ((jacquetFunctor h hU).obj π).representation :=
  generalizedWeightSpace ((jacquetFunctor h hU).obj π).representation
    (splitComponentPointsMap i ν I j hj a) χ (splitComponentPointsMap_mem_center i ν I j hj ha)

/-- Renard's normalized exponent: `χ` is smooth (open kernel in the canonical topology of
`A(k)`) and `(r V)_χ ≠ 0`. -/
def IsNormalizedJacquetExponent (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (χ : rationalPoints A.toGrp →* ℂˣ) : Prop :=
  letI := splitComponentPointTopology ha
  IsGeneralizedWeight ((jacquetFunctor h hU).obj π).representation
    (splitComponentPointsMap i ν I j hj a) χ (splitComponentPointsMap_mem_center i ν I j hj ha)

/-- Renard's `Exp(A, r V)`: the set of normalized exponents. -/
def normalizedJacquetExponents (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) : Set (rationalPoints A.toGrp →* ℂˣ) :=
  {χ | IsNormalizedJacquetExponent i ν I j hj h hU ha π χ}

theorem mem_normalizedJacquetExponents (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    χ ∈ normalizedJacquetExponents i ν I j hj h hU ha π ↔
      IsNormalizedJacquetExponent i ν I j hj h hU ha π χ :=
  Iff.rfl

/-- The defining unfolding: open kernel and nonzero weight subrepresentation. -/
theorem isNormalizedJacquetExponent_iff_isOpen_ker_and (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent i ν I j hj h hU ha π χ ↔
      @IsOpen _ (splitComponentPointTopology ha) (χ.ker : Set (rationalPoints A.toGrp)) ∧
        normalizedJacquetWeightSpace i ν I j hj h hU ha π χ ≠ ⊥ :=
  Iff.rfl

variable (hM : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
include hM

/-- Membership in `(r V)_χ`: one power `d` kills `r(t) - χ(t)` for every `t ∈ A(k)`.
The compact-open fixing condition is automatic for the smooth Jacquet module. -/
theorem mem_normalizedJacquetWeightSpace (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (χ : rationalPoints A.toGrp →* ℂˣ)
    (x : (jacquetFunctor h hU).obj π) :
    x ∈ normalizedJacquetWeightSpace i ν I j hj h hU ha π χ ↔
      ∃ d : ℕ, ∀ t : rationalPoints A.toGrp,
        ((((jacquetFunctor h hU).obj π).representation (splitComponentPointsMap i ν I j hj a t) -
          (χ t : ℂ) • 1) ^ d) x = 0 := by
  have := hM.locallyCompactSpace
  exact mem_generalizedWeightSpace_of_isSmooth _ χ _ ((jacquetFunctor h hU).obj π).isSmooth x

/-- Nontriviality of `(r V)_χ` is the generic generalized-eigencharacter predicate of the
restricted Jacquet action. -/
theorem normalizedJacquetWeightSpace_ne_bot_iff (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    normalizedJacquetWeightSpace i ν I j hj h hU ha π χ ≠ ⊥ ↔
      IsGeneralizedEigencharacter
        (((jacquetFunctor h hU).obj π).representation.comp
          (splitComponentPointsMap i ν I j hj a)) χ := by
  have := hM.locallyCompactSpace
  exact generalizedWeightSpace_ne_bot_iff _ χ _ ((jacquetFunctor h hU).obj π).isSmooth

/-- Normalized exponents are exactly the generic generalized eigencharacters of the
restricted Jacquet action; the open-kernel condition is automatic. -/
theorem isNormalizedJacquetExponent_iff (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent i ν I j hj h hU ha π χ ↔
      IsGeneralizedEigencharacter
        (((jacquetFunctor h hU).obj π).representation.comp
          (splitComponentPointsMap i ν I j hj a)) χ := by
  have := hM.locallyCompactSpace
  let := splitComponentPointTopology ha
  exact isGeneralizedWeight_iff _ ((jacquetFunctor h hU).obj π).isSmooth _
    (continuous_splitComponentPointsMap i ν I j hj ha)
    (splitComponentPointsMap_mem_center i ν I j hj ha) χ

end Langlands.Aubert.General.RationalPointFamily
