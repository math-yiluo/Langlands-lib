# Polynomials in the left action of a positive split component

Module `Langlands.Global.AdelicSplitComponentShifts`.

For a compatible standard family `𝓕 : StandardParabolicFamily F G` and a standard index `R`,
the positive split component `𝔄_R ⊆ P_R(𝔸)` acts on functions on `G(𝔸)` by
`(a · φ)(g) = φ(a g)` (`splitComponentRepresentation`, the unnormalized action of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), §6.3, (6.10)). This module extends that action to the complex group algebra of `𝔄_R`
and records how the resulting operators interact with the objects of
`Langlands.Global.AdelicLeadingCuspidalComponents` along the standard parabolics `Q ⊆ R`. These
are the difference operators used to separate generalized eigenspaces of `𝔄_R` in the proof of
the corollary of §6.4 of the source (`Langlands.Global.AdelicCuspidalExponentAscentReduction`).
The module contains definitions and proved theorems; it states no proposition.

## The operators

- `shiftAlgHom R : MonoidAlgebra ℂ 𝔄_R →ₐ[ℂ] Module.End ℂ (G(𝔸) → ℂ)` is
  `Representation.asAlgebraHom` of the unnormalized action; `shiftAlgHom_of` evaluates it on a
  point. The commutative group structure on `𝔄_R` is the local instance
  `positiveSplitComponentCommGroup` of `Langlands.Global.AdelicLeadingCuspidalPairing`, so the
  group algebra is commutative.
- `shiftAlgHom_mem`: a submodule stable under every point of `𝔄_R` is stable under every
  element of the group algebra. `shiftAlgHom_intertwine`: a map that is additive and homogeneous
  on such a submodule and commutes there with every point commutes with every element.
- `splitLift hQR a`: for `Q ⊆ R`, a chosen point of `𝔄_Q` with the same image in `G(𝔸)` as
  `a ∈ 𝔄_R` (it exists by `exists_positiveSplitComponent_lift_with_values` of
  `Langlands.Global.AdelicNestedSplitComponents`); `unnormalizedAction_splitLift` says that
  both act in the same way.

## Stability along `Q ⊆ R`

For `Q ⊆ R` and every element `D` of the group algebra of `𝔄_R`:

- `IsAutomorphicOn.shiftAlgHom`: `D` preserves automorphy on `U_Q(𝔸) M_Q(F) \ G(𝔸)`. For a
  single point this combines `IsAutomorphicFunctionOn.leftTranslate` (smoothness, finiteness
  under `Kinf` and the centre, moderate growth) with the invariance of
  `IsParabolicGeneratorInvariant.adelicLeftShift`; `isParabolicGeneratorInvariant_of_isLeftInvariantUnder`
  passes from invariance under `U_Q(𝔸) M_Q(F)` to invariance under its two generators.
- `HasPolynomialOrbit.shiftAlgHom` and `HasUnnormalizedExponent.shiftAlgHom`: `D` preserves
  polynomial orbits of a given degree for an exponent `λ` along `Q`, hence generalized
  exponents. `polynomialOrbitSubmodule` is the submodule of functions with polynomial orbits
  of degree at most `k`; a point `b ∈ 𝔄_Q` moves the base point of an orbit from `g` to `b g`.
- `shiftAlgHom_mem_cuspidalAnnihilator` and `shiftAlgHom_mem_leviIntegrableSubmodule`: `D`
  preserves the cuspidal annihilator along `Q` (`InCuspidalAnnihilator.adelicLeftShift`) and the
  absolute convergence of all Levi pairings along `Q` (`leviIntegrableSubmodule`). A point of
  `𝔄_Q` is central in the Levi, so on the pairing integrand it acts by a right translation
  (`leviPairingIntegrand_unnormalizedAction`).
- `constantTerm_shiftAlgHom`: on functions invariant under `U_R(𝔸)` with absolutely convergent
  constant terms along `Q` (`radicalIntegrableSubmodule Q R`), the constant term along `Q`
  commutes with `D` (`constantTerm_unnormalizedAction_of_radicalInvariant`).
  `mem_radicalIntegrableSubmodule_of_automorphicOn`: an automorphic function on
  `U_Q(𝔸) M_Q(F) \ G(𝔸)` with `Q ⊆ R` lies in that submodule for every `Q' ⊆ Q`.
- `IsCuspidalAlong.shiftAlgHom`: `D` preserves cuspidality along `Q` of automorphic functions
  along `Q`.
- `IsCuspidalProjection.shiftAlgHom`: if `hc` is a cuspidal projection of `h` along `Q`, then
  `D hc` is a cuspidal projection of `D h`. The proof writes the projection relation as
  `h - hc` in the cuspidal annihilator together with absolute convergence of the pairings of
  `hc`, both of which `D` preserves.
- `IsExponentDecomposition.shiftAlgHom`: `D` maps an exponent decomposition
  `ψ = ∑_{λ ∈ s} c λ` along `Q` to the decomposition `D ψ = ∑_{λ ∈ s} D (c λ)` with the same
  labels.

## Killing and injectivity

Fix `Q ⊆ R`, an exponent `λ` along `Q` and a function `φ` with polynomial orbits of degree at
most `k` for `λ`.

- `shiftAlgHom_factor`: the operator of `(a - z)^m` is the polynomial `(X - z)^m` in the shift
  by `a`; `shiftAlgHom_of_eq_leftFunctions` identifies that shift with the left translation by
  `splitLift hQR a`.
- `shiftAlgHom_factor_eq_zero`: `(a - a^λ)^{k+1}` kills `φ`, where `a^λ` is
  `parameterPower` of `λ` at `splitLift hQR a`. This is
  `isTranslationPolynomialSolution_pow_of_polynomialOrbit` of
  `Langlands.Global.AdelicExponentPolynomials`.
- `eq_zero_of_shiftAlgHom_factor_eq_zero`: if `z ≠ a^λ`, then `(a - z)^m φ = 0` implies `φ = 0`,
  because `(X - z)^m` and `(X - a^λ)^{k+1}` are coprime.
- `shiftAlgHom_prod_eq_zero` and `eq_zero_of_shiftAlgHom_prod_eq_zero`: for a finite product of
  such powers, one killing factor kills `φ`; if no root `Z i` equals `(A i)^λ`, the product is
  injective on functions with polynomial orbits for `λ` (induction on the finite index set,
  using that the product preserves polynomial orbits).

## Sources

Bernstein–Lapid (2024), §6.3, (6.10) (generalized eigenspaces for the unnormalized action of
`𝔄_P`), the difference-operator argument in the proof of the lemma of §6.4 (p. 204), and the
decomposition according to the action of `𝔄_{P_α}` in the proof of the corollary (p. 204). The
operators here replace that decomposition by explicit products of differences.
