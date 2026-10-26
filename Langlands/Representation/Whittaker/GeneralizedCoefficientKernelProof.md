# The generalized-coefficient kernel criterion

This module proves the complete published proposition
`Langlands.Whittaker.GeneralizedCoefficientKernelStatement.{uG,uV}` as
`Langlands.Whittaker.generalizedCoefficientKernel`. It is an internal
consequence of the published generalized-coefficient, separation, scalar-descent
and anti-pullback constructions. The proof below describes the implemented
argument; no additional literature theorem is transcribed.

## Setting

The closing theorem has exactly the published proposition as its type. The
group and representation carrier have independent universes. The group is
Hausdorff, locally compact and totally disconnected, with its Borel measurable
structure. The measure is a left Haar measure and is also right invariant and
inversion invariant. The complex representation is admissible and irreducible.
Its carrier has its algebraic additive group and module structures.

The homeomorphism `tau` is measure preserving, involutive and
anti-multiplicative. The submodule `W` is an actual submodule of the full
algebraic dual of the representation. A fixed nonzero algebraic functional
`eta` on the actual smooth dual is given. For every `ell` in `W`, the actual
distribution `generalizedCoefficient mu rho hSmooth ell.val eta` is invariant
under `Distribution.pushforward tau`. Neither algebraic functional has a
smoothness or continuity hypothesis.

Write `S_ell(f)` for full-transpose smoothing, `D_ell(f) = eta(S_ell(f))`,
`P(f) = f composed with tau`, and `f*g` for the published Hecke convolution.

## Convolution symmetry

`generalizedCoefficient_convolution_symmetry` evaluates the equality of
distributions on `f*g`. The pushforward convention yields
`D_ell(P(f*g)) = D_ell(f*g)`. The existing
`Hecke.TestFunction.pullback_convolution` identifies `P(f*g)` with
`P(g)*P(f)`. Consequently

```
D_ell(f*g) = D_ell(P(g)*P(f)).
```

The helper uses the group, measure, representation and anti-homeomorphism
assumptions above, together with invariance for this one coefficient. It does
not need admissibility, irreducibility or nonvanishing of either functional.

## Smoothing-kernel comparison

`smoothFunctional_ker_le_of_generalizedCoefficient_invariant` assumes
admissibility, irreducibility, nonzero `eta`, nonzero `ell_1`, and invariance of
the coefficients for `ell_1` and `ell_2`. It proves
`ker S_ell_1` is contained in `ker S_ell_2`.

If `ell_2 = 0`, linearity gives the inclusion immediately. Otherwise let
`S_ell_1(f) = 0`. The published left-annihilator equivalence gives
`D_ell_1(f*g) = 0` for every `g`. Convolution symmetry and surjectivity of the
pullback linear equivalence then give
`D_ell_1(q*P(f)) = 0` for every `q`.

The published right-annihilator equivalence identifies this last condition
with a condition involving only `eta` and `P(f)`, independent of the nonzero
first functional. Applying it for `ell_2` gives
`D_ell_2(q*P(f)) = 0` for every `q`. Set `q = P(g)` and apply convolution
symmetry again. Then `D_ell_2(f*g) = 0` for every `g`. The left-annihilator
equivalence gives `S_ell_2(f) = 0`.

The two helpers use bijectivity of pullback and thus require no separate
involutivity assumption. The closing theorem retains the target's explicit
involutivity premise.

## Scalar existence and uniqueness

The final proof applies this inclusion to the underlying functionals of
`ell_1, ell_2 : W`. The published
`existsUnique_smul_of_smoothFunctional_ker_le` gives a unique complex scalar
`c` with `ell_2.val = c • ell_1.val`. That theorem already constructs the
intertwining descent through the first smoothing map, applies admissible
Schur's lemma, and recovers equality of the original full-dual functionals
using Haar local units.

Subtype extensionality transfers existence into `W`. Applying the subtype
value map to any competing equality in `W` reduces uniqueness to the same
published scalar-descent theorem. This includes an arbitrary second
functional, including zero.

## Scope

The conclusion is unique complex-scalar proportionality inside `W` for each
nonzero first functional. The theorem uses no unitary structure, countability,
topology on the representation carrier, self-duality, Whittaker condition or
additional kernel premise. Distribution invariance and the given nonzero
`eta` remain hypotheses. The separate Whittaker application must construct its
functional and establish its distribution invariance.

Worker 557 authored this proof pair using the published prerequisite APIs.
Worker 16 supplied the substantive symmetry and kernel-comparison route in
the task context.
