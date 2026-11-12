import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies
import Langlands.GroupScheme.Reductive.Basic

/-! # The group `T` of an irreducible representation (Renard VI.4.4, preliminaries and Remark)

For an irreducible smooth representation `π` of the rational points of a connected reductive
group, `T` is the intersection of the kernels of the unramified characters `ω` with
`π ⊗ ω ≃ π`. It contains `⁰G` and the centre, has finite index, and its annihilator in the
unramified characters is exactly the twist stabilizer `X(G)(π)`. The polynomial functions on
the torus `X(G)/X(G)(π)` form the group algebra `ℂ[T/⁰G]`, which is also the algebra of
`X(G)(π)`-invariants of `ℂ[G/⁰G]`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.4.4, the paragraph defining `T` and the Remark after it, for an irreducible smooth
representation `A` of `G(F)`. Write `X` for the unramified characters, `Stab` for the twist
stabilizer `{ω | A ⊗ ω ≅ A}` and `T = ⋂_{ω ∈ Stab} ker ω`. Then `⁰G ≤ T`, the centre of `G(F)`
lies in `T`, `T` has finite index, an unramified character lies in `Stab` exactly when it is
trivial on `T`, a finitely supported function on `G(F)/⁰G` is `Stab`-invariant exactly when it
is supported in `T/⁰G`, and an injective algebra map `ℂ[T/⁰G] → (X → ℂ)`, sending the class of
`t` to the evaluation at `t`, has range exactly the `Stab`-invariant elements of the published
algebra `unramifiedRegularFunctions` of polynomial functions on `X`. -/
def RationalTwistStabilizerKernelStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G), A.IsIrreducible →
      let X := unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)
      let T : Subgroup (GroupScheme.rationalPoints G) :=
        ⨅ (ω : X) (_ : Nonempty (rationalUnramifiedTwist G ω A ≅ A)),
          ω.val.toMonoidHom.ker
      rationalCommonNormKernel G ≤ T ∧
      Subgroup.center (GroupScheme.rationalPoints G) ≤ T ∧
      T.FiniteIndex ∧
      (∀ ω : X, Nonempty (rationalUnramifiedTwist G ω A ≅ A) ↔ T ≤ ω.val.toMonoidHom.ker) ∧
      (∀ f : GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G →₀ ℂ,
        (∀ ω : X, Nonempty (rationalUnramifiedTwist G ω A ≅ A) →
          ∀ g : GroupScheme.rationalPoints G,
            ((ω.val g : ℂˣ) : ℂ) * f (QuotientGroup.mk g) = f (QuotientGroup.mk g)) ↔
        ∀ g : GroupScheme.rationalPoints G, f (QuotientGroup.mk g) ≠ 0 → g ∈ T) ∧
      ∃ Θ : MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T) →ₐ[ℂ] (X → ℂ),
        Function.Injective Θ ∧
        Set.range Θ =
          {φ | φ ∈ unramifiedRegularFunctions (fun χ => (rationalNormCharacters G χ).toMul) ∧
            ∀ s : X, Nonempty (rationalUnramifiedTwist G s A ≅ A) → ∀ χ, φ (χ * s) = φ χ} ∧
        ∀ t : T, Θ (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)) =
          unramifiedEvaluation (fun χ => (rationalNormCharacters G χ).toMul)
            (t : GroupScheme.rationalPoints G)

end Langlands.CuspidalSupport
