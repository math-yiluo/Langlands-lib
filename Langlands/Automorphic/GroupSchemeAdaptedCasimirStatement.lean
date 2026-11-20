import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth
import Langlands.Global.InfinitePlaceLeviIwasawaBaseChange

/-! # A Casimir element adapted to a maximal compact subgroup of the infinite adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints

/-- For a connected reductive group `G` over a number field and a maximal compact subgroup
`Kinf` of `G(F ⊗ ℝ)`, the actual tangent Lie algebra at the identity (for the atlas of `hsmooth`)
is spanned by vectors `X i` such that every `X j` with `j ∈ J` is the velocity at `0` of a
smooth curve through `1` in `Kinf`, and such that
`∑ i, X i ^ 2 - 2 • ∑ j ∈ J, X j ^ 2` lies in the centre of the actual enveloping algebra.
For a Cartan decomposition `𝔨 ⊕ 𝔭` and an invariant form that is positive on `𝔭` and negative
on `𝔨`, an orthonormal basis of `𝔭` together with one of `𝔨` (indexed by `J`) has this
property: the element is the Casimir element `ω_𝔭 - ω_𝔨`. -/
def AdelicAdaptedCasimirStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    GroupScheme.IsConnectedReductive G → CompactIwasawa.IsMaximalCompact Kinf →
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    ∃ (n : ℕ) (X : Fin n → GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
      (J : Finset (Fin n)),
      Submodule.span ℝ (Set.range X) = ⊤ ∧
      (∀ j ∈ J, ∃ c : ℝ → InfiniteAdelicGroupPoints F G,
        ContMDiff 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) ∞ c ∧ c 0 = 1 ∧ (∀ t : ℝ, c t ∈ Kinf) ∧
          mfderiv 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) c 0 1 = X j) ∧
      ((∑ i, UniversalEnvelopingAlgebra.ι ℂ
            (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
            ((1 : ℂ) ⊗ₜ[ℝ] X i) ^ 2 -
          (2 : ℂ) • ∑ j ∈ J, UniversalEnvelopingAlgebra.ι ℂ
            (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
            ((1 : ℂ) ⊗ₜ[ℝ] X j) ^ 2 : AdelicEnvelopingAlgebra F G hsmooth) ∈
        Subalgebra.center ℂ (AdelicEnvelopingAlgebra F G hsmooth))

end Langlands.Automorphic.GroupSchemeFunctions
