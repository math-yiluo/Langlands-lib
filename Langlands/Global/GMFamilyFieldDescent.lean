import Langlands.LinearAlgebra.GMFamilies
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Actual field-extension data for descent of `(G, M)`-families

The coarse space is the image of the real cocharacters of the actual split component of `M`
in that of `M₁` after base change. Compare the embedding of parameters against base change
and restriction of actual rational characters, not an arbitrary projection. The relative
weights used for chamber indices and for Arthur's special-subspace condition are the actual
adjoint weights, with their Lie weight multiplicities. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj RealInnerProductSpace ContDiff Classical

namespace Langlands.GMFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

section Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Arthur's center over the smaller field in the common Euclidean realization: the elements
of `b = 𝔞_M` on which every fine root is zero. It can be smaller than the fine center. -/
def coarseCenter (R : Finset E) (b : Submodule ℝ E) : Submodule ℝ E :=
  b ⊓ centralSpace R

/-- A smooth representative of a function defined by the `θ`-sum, on the domain where none
of the denominators of the defining expression vanish. -/
def IsSmoothThetaExtension (R : Finset E) (a : Submodule ℝ E)
    (f g : StrongDual ℝ a → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ Λ : StrongDual ℝ a,
    (∀ S ∈ parabolics R a, theta a S Λ ≠ 0) → f Λ = g Λ

/-- The field-descent formula in Euclidean coordinates, for a root arrangement in `E = 𝔞_{M₁}`
and `b = 𝔞_M`. The coordinates must be identified with the actual group data separately.
The supplementary functions in the identity are the smooth extensions, including at `0`. -/
def HasFieldDescentFormula (R : Finset E) (b : Submodule ℝ E) : Prop :=
  let a₁ : Submodule ℝ E := ⊤
  let z := coarseCenter R b
  ∀ c₁ : Finset E → StrongDual ℝ a₁ → ℂ, IsFamily R a₁ c₁ →
    (∀ S ∈ parabolics R b, ∃ S₁ ∈ parabolics R a₁, S ⊆ S₁) ∧
    (∀ S ∈ parabolics R b, ∀ S₁ ∈ parabolics R a₁, S ⊆ S₁ →
      ∀ Λ : StrongDual ℝ b,
        inducedFamily R b a₁ c₁ S Λ = c₁ S₁ (extendParam b a₁ Λ)) ∧
    IsFamily R b (inducedFamily R b a₁ c₁) ∧
    ∃ (c₀ : StrongDual ℝ b → ℂ) (cQ : Finset E → StrongDual ℝ a₁ → ℂ),
      IsSmoothThetaExtension R b c₀ (cM R b (inducedFamily R b a₁ c₁)) ∧
      (∀ Q ∈ faces R a₁,
        IsSmoothThetaExtension (leviRoots R Q) a₁ (cQ Q) (cQM R a₁ c₁ Q)) ∧
      ∀ ξ ∈ a₁ ⊓ bᗮ,
        (∀ L₁ ∈ leviSpaces R a₁, dDescent b z a₁ L₁ ≠ 0 →
          ∀ p : E, p ∈ L₁ ⊓ zᗮ → p - ξ ∈ b ⊓ zᗮ → IsRegular R L₁ p) →
        ∀ Λ : StrongDual ℝ b,
          c₀ Λ = ∑ L₁ ∈ leviSpaces R a₁, (dDescent b z a₁ L₁ : ℂ) *
            cQ (descentSection R b z ξ L₁) (extendParam b a₁ Λ)

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- The Riesz vector of an actual torus character, expressed in chosen Euclidean coordinates. -/
def rootVectorIn (e : V A ≃ₗ[ℝ] E) (χ : characterLattice A) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    (((eval A χ).comp e.symm.toLinearMap).toContinuousLinearMap)

/-- The nonzero adjoint root weights of an actual split torus, as their Riesz vectors. -/
def actualRootVectors (i : A.toGrp ⟶ G) (hA : IsSplitTorus A.toGrp) (e : V A ≃ₗ[ℝ] E) : Finset E :=
  (hA.finite_relativeRoots i).toFinset.image (rootVectorIn e)

/-- The weighted sums of fine roots over each nonzero restriction to `b` lie in `b`.
Here multiplicity is the dimension of the actual adjoint weight space. Enlarging `b` by
central directions gives the special-subspace condition of Arthur 1988, p.355. -/
def HasSpecialWeightSums (i : A.toGrp ⟶ G) (hA : IsSplitTorus A.toGrp)
    (e : V A ≃ₗ[ℝ] E) (b : Submodule ℝ E) : Prop :=
  ∀ β : b, β ≠ 0 →
    (∑ α ∈ (hA.finite_relativeRoots i).toFinset.filter
        (fun α => restrictedRoot b (rootVectorIn e α) = β),
        (Module.finrank k (weightSpace i α) : ℝ) • rootVectorIn e α) ∈ b

end Linear

section Actual

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}
  {M : GroupScheme (Spec (CommRingCat.of k))}
  {M₁ : GroupScheme (Spec (CommRingCat.of K))}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "bmap" => algebraBaseMap k K

/-- The actual inclusion of real cocharacters of the original split component via scalar
extension and the specified map into the larger split component. -/
def fieldCocharacterInclusion (j : (CommGroupScheme.baseChange bmap).obj A ⟶ A₁) :
    V A →ₗ[ℝ] V A₁ :=
  (cocharacterMapReal j).comp ((cocharacterLattice.baseChange bmap A).toIntLinearMap.baseChange ℝ)

/-- The parameter comparison on actual rational characters: first base change from `M` to
`M_K`, then restrict to `M₁` and its split component. In the chosen Euclidean coordinates this
must agree with the dual of the orthogonal projection onto the coarse cocharacter space. -/
def IsFieldParameterCompatible (m : M₁ ⟶ (GroupScheme.baseChange bmap).obj M)
    (a : A.toGrp ⟶ M) (a₁ : A₁.toGrp ⟶ M₁) (b : Submodule ℝ E)
    (e : V A ≃ₗ[ℝ] b) (e₁ : V A₁ ≃ₗ[ℝ] E) : Prop :=
  ∀ χ : rationalCharacters M, ∀ x : E,
    eval A₁ (characterRestrict a₁ (characterRestrict m (rationalCharacters.baseChange bmap χ)))
      (e₁.symm x) =
    eval A (characterRestrict a χ) (e.symm (b.orthogonalProjectionOnto x))

end Actual

section ActualComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}
  {M : GroupScheme (Spec (CommRingCat.of k))}
  {M₁ : GroupScheme (Spec (CommRingCat.of K))}

local notation "f" => algebraBaseMap k K
local notation "BC" => GroupScheme.baseChange f

/-- The actual data comparison and descent identity. This predicate asserts that the maps and
compatible Euclidean model exist; the descent statement specializes it to nested rational Levis. -/
def HasActualFieldDescent (l : M ⟶ G) (l₁ : M₁ ⟶ (BC).obj G) (m : M₁ ⟶ (BC).obj M)
    (a : A.toGrp ⟶ M) (hA : IsSplitComponent a) (a₁ : A₁.toGrp ⟶ M₁)
    (hA₁ : IsSplitComponent a₁) : Prop :=
  letI : IsAffineHom ((BC).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom f)
    infer_instance
  letI : LocallyOfFiniteType ((BC).obj G).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd G.X.hom f)
    infer_instance
  ∃ j : (CommGroupScheme.baseChange f).obj A ⟶ A₁,
    CommGroupScheme.groupHom j ≫ a₁ ≫ m = (BC).map a ∧
    let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ (V A₁)))
    ∃ (e₁ : V A₁ ≃ₗ[ℝ] E) (b : Submodule ℝ E) (e : V A ≃ₗ[ℝ] b),
      (∀ x : V A, (e x : E) = e₁ (fieldCocharacterInclusion j x)) ∧
      IsFieldParameterCompatible m a a₁ b e e₁ ∧
      let i₁ := a₁ ≫ l₁
      let hS₁ := hA₁.isCentralSplitTorus.isSplitSubtorus.1
      let R := actualRootVectors i₁ hS₁ e₁
      ((R.image (restrictedRoot b)).erase 0 =
        actualRootVectors (a ≫ l) hA.isCentralSplitTorus.isSplitSubtorus.1 e) ∧
      (∀ x : b, ((centralSpace R).orthogonalProjectionOnto (x : E) : E) ∈ b) ∧
      HasSpecialWeightSums i₁ hS₁ e₁ b ∧
      HasFieldDescentFormula R b

end ActualComparison

end Langlands.GMFamily
