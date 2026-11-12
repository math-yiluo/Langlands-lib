import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Reductive.Basic

/-! Renard VI.2.3–VI.2.4: the uniform admissibility theorem, its analogue for the
common norm kernel `⁰G`, and the uniform support of the level-`K` coefficients of
irreducible supercuspidal representations modulo the centre. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.CuspidalSupport

universe u v

open GroupScheme

/-- VI.2.3, Theorem (uniform admissibility): for every compact open subgroup `K` of
`G(F)` there is a bound `c` with `dim V^K ≤ c` for every irreducible smooth complex
representation `(π, V)` of `G(F)`. The dimension is the `ℂ`-rank of the actual
`K`-fixed subspace, so the bound also asserts its finiteness. -/
def RationalPointsUniformAdmissibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ K : OpenSubgroup (GroupScheme.rationalPoints G),
      IsCompact (K : Set (GroupScheme.rationalPoints G)) →
      ∃ c : ℕ, ∀ A : SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints G),
        A.IsIrreducible →
        Module.rank ℂ (fixedVectors A.representation K.toSubgroup) ≤ c

/-- VI.2.3, Remark: the same uniform bound for the irreducible smooth complex
representations of the common norm kernel `⁰G = rationalCommonNormKernel G`, with its
subspace topology, and every compact open subgroup `K` of `⁰G`. -/
def RationalNormKernelUniformAdmissibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ K : OpenSubgroup (Plancherel.rationalCommonNormKernel G),
      IsCompact (K : Set (Plancherel.rationalCommonNormKernel G)) →
      ∃ c : ℕ, ∀ A : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel G),
        A.IsIrreducible →
        Module.rank ℂ (fixedVectors A.representation K.toSubgroup) ≤ c

/-- VI.2.4, Proposition: for every compact open subgroup `K` of `G(F)` there is an open
subset `Ω`, compact modulo the centre, such that for every irreducible supercuspidal
smooth complex representation `(ρ, W)` and every `v ∈ W^K`, the function
`g ↦ ρ(a_{g,K}) v` is supported in `Ω`. Since `ρ(a_{g,K}) v = ρ(e_K) ρ(g) v` for
`v ∈ W^K`, this support is the union of the supports of the coefficients
`g ↦ ℓ(ρ(g) v)` over the `K`-invariant linear forms `ℓ`, which is how it is stated. -/
def SupercuspidalUniformCoefficientSupportStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) :=
      Aubert.General.RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (K : OpenSubgroup (rationalPoints G)),
      IsCompact (K : Set (rationalPoints G)) →
      ∃ Ω : Set (rationalPoints G), IsOpen Ω ∧
        (∃ C : Set (rationalPoints G), IsCompact C ∧
          Ω ⊆ C * (Subgroup.center (rationalPoints G) : Set (rationalPoints G))) ∧
        ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G), A.IsIrreducible →
          Aubert.General.RepresentedParabolic.IsSupercuspidal A →
          ∀ w ∈ fixedVectors A.representation K.toSubgroup,
          ∀ ℓ : Module.Dual ℂ A,
            (∀ x ∈ K, ∀ y : A, ℓ (A.representation x y) = ℓ y) →
            Function.support (fun g : rationalPoints G => ℓ (A.representation g w)) ⊆ Ω

/-- Renard VI.2.3–VI.2.4: the three statements above. -/
def UniformAdmissibilityStatements : Prop :=
  RationalPointsUniformAdmissibilityStatement.{u, v} ∧
    RationalNormKernelUniformAdmissibilityStatement.{u, v} ∧
    SupercuspidalUniformCoefficientSupportStatement.{u, v}

end Langlands.CuspidalSupport
