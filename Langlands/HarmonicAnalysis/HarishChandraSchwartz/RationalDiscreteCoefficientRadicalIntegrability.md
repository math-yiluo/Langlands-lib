# Radical integrability of discrete-series coefficients through the III.7 cutoff

Let `A` be a smooth representation of `G(F)` that is square integrable modulo
the image `A_G(F)` of a split component. Let `U ≤ G¹` be a subgroup with a
measure, for example the unipotent radical of a proper standard parabolic.
This module proves that the coefficients of `A` are integrable over `U` along
every two-sided translate, under two premises:

- the structural data of Corollary III.1.2 at a compact subgroup `K0`;
- radical convergence for the Schwartz space `C(G)`: every Schwartz function
  (realized with one compact open `K` and one matrix representation `ρ`) is
  integrable over `U` along every two-sided translate.

Both premises are explicit hypotheses; this module proves neither of them.
Module `RationalDiscreteCoefficientConstantTerm` proves the vanishing of the
radical integrals of the coefficients, assuming exactly this integrability.
Combined with it, the present module places the coefficient space of `A` in
the integrable cuspidal kernel of every proper standard radical.

## Provenance

Waldspurger (2003), §III.7, printed p.273 (PDF p.39), says: let `(ω, E)` be
an admissible square-integrable representation of `G`, `f ∈ A(ω)` and
`ϕ ∈ C_c(G/G¹)`; by Corollary III.1.2 the product `fϕ` lies in `C(G)`.
Corollary III.1.2, printed p.263 (PDF p.29), is the rapid decay of the
coefficients of a square-integrable representation on `G¹`. The PDF page is
the printed page minus 234.

The Library already has both steps on actual rational points:

- `hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable` (module
  `RationalSquareIntegrableDecayProof`) is Corollary III.1.2 for one group.
  It needs a compact subgroup `K0` with `SimultaneousStandardBasisAt i ν K0`
  and `FiniteCartanCovering F i ν K0`, which the Library treats as external
  structural inputs.
- `mul_mem_rationalSchwartz` (module `RationalSquareIntegrableDecay`) is the
  III.7 sentence: from that decay, `g ↦ f(g) ϕ(g G¹)` lies in the Schwartz
  space for every coefficient `f` and every compactly supported `ϕ` on
  `G(F)/G¹`.

The step that uses them is an internal adapter, not a statement of
Waldspurger. Take `ϕ` to be the indicator of one `G¹`-coset `x y G¹`. Since
`U ≤ G¹` and `G¹` is normal, `x u y G¹ = x y G¹` for every `u ∈ U`. So `fϕ`
agrees with `f` on the whole translate `x U y`, and the integrability of the
Schwartz function `fϕ` over `x U y` is the integrability of `f` there.
Waldspurger gets the convergence of the radical integrals of Schwartz
functions from Proposition II.4.5 (applied in §III.6, printed p.272, PDF
p.38); here that convergence is a premise.

## Cutoffs on a quotient

Section `Cutoff`. `Γ` is a group and `N` a subgroup.

- `cosetIndicator N q` (definition): the indicator function of the single
  point `q` of `Γ ⧸ N`, with value `1 : ℂ` at `q` and `0` elsewhere.
  `cosetIndicator_self` evaluates it at `q`.
- `quotient_mk_mul_mul_of_mem`: for `N` normal and `u ∈ N`, the cosets of
  `x * u * y` and `x * y` agree. Indeed
  `(x u y)⁻¹ (x y) = y⁻¹ u⁻¹ y` lies in `N`.
- `hasCompactSupport_cosetIndicator`: in a topological group, if `N` is open
  then `Γ ⧸ N` is discrete, so the indicator of one coset has compact support.
- `mul_cosetIndicator_translate`: for `N` normal, `u ∈ N` and any
  `f : Γ → ℂ`, multiplying `f (x * u * y)` by the indicator of the coset of
  `x * y`, evaluated at the coset of `x * u * y`, gives back
  `f (x * u * y)`.

## Rational points

Section `Rational`. The setting and local instances are those of
`RationalSquareIntegrableDecay`: a nonarchimedean local field `F`, a
connected reductive `G` (`hG`) with maximal split torus `i` (`hi`) and a
generic cocharacter `ν` (`hν`). `G¹` is `rationalCommonNormKernel G`, which
is open (`isOpen_rationalCommonNormKernel`).

- `standardUnipotentPoints_le_rationalCommonNormKernel`: for every finite set
  `I` of simple roots, the radical `standardUnipotentPoints i ν (rootSet i ν
  I)` lies in `G¹`. It is a limit of compact subgroups
  (`standardUnipotentPoints_isLimitOfCompactSubgroups`, with the standard
  cocharacter of `rootSet i ν I`). Every such subgroup lies in `G¹`
  (`CuspidalSupport.limitOfCompactSubgroups_le_rationalCommonNormKernel`).

The next three theorems share these hypotheses:

- a compact subgroup `K0` (`hK0c`) with `SimultaneousStandardBasisAt i ν K0`
  (`hbasis`) and `FiniteCartanCovering F i ν K0` (`hcover`);
- a compact open subgroup `K` (`hKo`, `hKc`) with `G(F) = P₀(F) K` (`hPK`)
  and a matrix representation `ρ`, which together fix the Schwartz space
  `RationalSchwartzSpace hKc hPK ρ`;
- a split component `s` (`hs`), the Borel structure on `G(F) / A_G(F)` and a
  Haar measure `mu` on it;
- `A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)` square integrable modulo
  `A_G(F)`: `IsSquareIntegrableModCentralSubgroup … A.representation mu`.

The theorems:

- `integrable_coefficientTensorMap_translate`: let `U ≤ G¹` be a subgroup
  with a measure `muU`. Assume every `φ` in the Schwartz space has
  `v ↦ φ (x * v * y)` `muU`-integrable for all `x` and `y` (premise
  `hconv`). Then for every `t : CoefficientTensor A` and all `x`, `y`, the
  function `v ↦ coefficientTensorMap A t (x * v * y)` is `muU`-integrable.
  The proof follows the adapter above. Corollary III.1.2 gives the rapid
  decay. `mul_mem_rationalSchwartz` puts the product of the coefficient with
  the indicator of the coset of `x * y` in the Schwartz space.
  `mul_cosetIndicator_translate` shows that this product agrees with the
  coefficient on the translate.
- `integrable_coefficient`: under the same hypotheses, for every vector `v`
  and every smooth functional `ℓ`, the ordinary coefficient
  `u ↦ ℓ.val (A.representation u v)` is `muU`-integrable. This is the
  previous theorem for `t = v ⊗ ℓ` and `x = y = 1`.
- `coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule`: let `I`
  be proper (`rootSet i ν I ≠ simpleRelativeRoots i ν`) and `muU` a Haar
  measure on the radical `standardUnipotentPoints i ν (rootSet i ν I)`.
  Assume radical convergence `hconv` for this radical and the given Schwartz
  space. Then `coefficientFunctionSpace A ≤
  integrableUnipotentCuspidalSubmodule muU`. The radical lies in `G¹`, so
  `integrable_coefficient` supplies the integrability hypothesis of
  `DiscreteConstantTerm.coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule`
  (module `RationalDiscreteCoefficientConstantTerm`).

The last theorem, `coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule_of_convergence`,
replaces the local premise `hconv` by the published all-choice statement
`RationalSchwartzConstantTermConvergenceStatement` (module
`RationalCuspidalConvergenceStatements`), taken as a hypothesis. It then uses
one compact open subgroup `K : OpenSubgroup (rationalPoints G)` and one
closed matrix representation `ρ : MatrixRepresentation G (Fin N)`
(`IsClosedSubgroup ρ`), as that statement requires. Its conclusion is the
same inclusion for every proper `I` and every Haar measure on the radical.
The structural data `K0` are still hypotheses.
