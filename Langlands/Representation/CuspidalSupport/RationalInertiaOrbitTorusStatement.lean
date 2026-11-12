import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.Representation.Plancherel.RationalUnramifiedCoordinateAlgebra
import Langlands.GroupScheme.Reductive.Basic

/-! # Unramified orbits of irreducible representations are tori (Renard V.2.7, Corollary)

Let `π` be an irreducible smooth representation of `G(F)`, `X(G)` the unramified characters,
`F = ℂ[X(G)]` the published algebra of polynomial functions on `X(G)` and `S = X(G)(π)` the
stabilizer of `π`. The inertial class `D = X(G) · π` is identified with `X(G)/S`, its algebra
of polynomial functions is the invariant algebra `F^S`, and `F^S` is a Laurent polynomial
algebra in `rank Λ(G)` variables whose complex points are exactly the points of `D`: so `D`
is a complex algebraic torus of the dimension of `X(G)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard V.2.7, Corollary, with the identifications of the Notations paragraph that follows
it. For every connected reductive `G` over a nonarchimedean local field `F` and every
irreducible smooth representation `π` of `G(F)`, write `X(G)` for the published unramified
characters, `F = unramifiedRegularFunctions` for the algebra of polynomial functions on
`X(G)`, and `S = {s ∈ X(G) | π ⊗ s ≃ π}` for the stabilizer `X(G)(π)`. Then:

* (homogeneous space) `π ⊗ χ ≃ π ⊗ χ'` if and only if `χ⁻¹ χ' ∈ S`;
* (torus) there is an injective `ℂ`-algebra homomorphism `Φ` from the Laurent polynomial
  algebra `ℂ[ℤ^d]`, `d = rank Λ(G)`, to the functions on `X(G)` whose range is exactly the
  invariant algebra `F^S = {f ∈ F | f(χ s) = f(χ) for all s ∈ S}`;
* (points) every `ℂ`-algebra homomorphism `ℂ[ℤ^d] → ℂ` is evaluation of `Φ` at some
  `χ ∈ X(G)`;
* (orbit) `π ⊗ χ ≃ π ⊗ χ'` if and only if every element of `F^S` takes the same value at
  `χ` and `χ'`. -/
def RationalInertiaOrbitTorusStatement : Prop :=
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
      let S : Set (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) :=
        {s | Nonempty (rationalUnramifiedTwist G s A ≅ A)}
      let invariant : Set (unramifiedCharacters
          (fun chi => (rationalNormCharacters G chi).toMul) → ℂ) :=
        {f | f ∈ unramifiedRegularFunctions (fun chi => (rationalNormCharacters G chi).toMul) ∧
          ∀ s ∈ S, ∀ χ, f (χ * s) = f χ}
      (∀ χ χ' : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul),
        Nonempty (rationalUnramifiedTwist G χ A ≅ rationalUnramifiedTwist G χ' A) ↔
          χ⁻¹ * χ' ∈ S) ∧
      ∃ Φ : AddMonoidAlgebra ℂ (Fin (rationalImageRank G) → ℤ) →ₐ[ℂ]
          (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) → ℂ),
        Function.Injective Φ ∧
        Set.range Φ = invariant ∧
        (∀ φ : AddMonoidAlgebra ℂ (Fin (rationalImageRank G) → ℤ) →ₐ[ℂ] ℂ,
          ∃ χ, ∀ p, φ p = Φ p χ) ∧
        ∀ χ χ' : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul),
          Nonempty (rationalUnramifiedTwist G χ A ≅ rationalUnramifiedTwist G χ' A) ↔
            ∀ f ∈ invariant, f χ = f χ'

end Langlands.CuspidalSupport
