# Range and separation for generalized coefficients

This internal construction provides the two separation facts used in the
planned generalized-coefficient kernel comparison. It uses the actual
`smoothFunctional` and `generalizedCoefficient` from
`Whittaker.GeneralizedCoefficient`. It does not prove a distribution-invariance
theorem, the scalar kernel criterion, or Whittaker multiplicity one.

## Objects and hypotheses

Write `S_ell(f) = smoothFunctional mu rho hSmooth ell f` and
`D_(ell,eta)(f) = eta(S_ell(f))`. The representation is complex linear on an
arbitrary algebraic carrier `V`, with its universe independent of the group
universe. Neither functional is assumed smooth, continuous, or nondegenerate.
There is no topology on `V` and no unitarity hypothesis.

`smoothFunctionalRange` is the subrepresentation of the actual
`smoothContragredient rho` whose underlying submodule is the linear range of
`S_ell`. Its membership equivalence says exactly that a smooth-dual vector is
`S_ell(f)` for some Schwartz–Bruhat test function `f`. This construction assumes
that `G` is a Hausdorff locally compact totally disconnected topological group
with its Borel measurable structure, that `mu` is finite on compact sets and
right invariant, and that `rho` is smooth. Its stability follows from the
published identity `S_ell(R_a f) = rhoDual(a) S_ell(f)`.

`smoothDualOrbitKernel rho eta` is the subrepresentation with underlying submodule

```
intersection over a in G of ker (eta composed with rhoDual(a)).
```

This construction only needs the topological group and complex representation
needed to form the actual smooth dual. It has no measure hypothesis. Its
membership law is `eta(rhoDual(a) phi) = 0` for every `a`. Stability follows by
replacing `a` with `a*b` after acting by `b`.

## Surjectivity and detection

`smoothFunctional_surjective` additionally assumes that `mu` is left invariant
and positive on nonempty open sets, that `rho` is admissible and irreducible,
and that `ell` is nonzero. It proves that `S_ell` is surjective onto the entire
actual smooth dual. Compact-open cofinality comes from the published
`Hecke.TestFunction.commonCompactOpenBiInvariance` applied to the empty family
of test functions. The published
`CompactSplitting.isIrreducible_smoothContragredient` then makes the range either
bottom or top. If it were bottom, smoothing would be the zero linear map, and
`smoothFunctional_eq_zero_iff`, proved using Haar local units, would force
`ell = 0`. Thus the range is top.

`smoothDualOrbitKernel_eq_bot` uses admissibility and irreducibility of `rho`,
the same group hypotheses for compact-open cofinality, and `eta != 0`. It proves
that the common orbit kernel is bottom. Irreducibility of the smooth dual makes
it bottom or top; in the top case, evaluation at the identity group element
would show `eta = 0`. No measure is needed for this result.

`smoothFunctional_pairing` identifies `S_(pairing(phi))(f)` with the actual
`Hecke.integratedTranspose mu rho hSmooth f phi`. It requires inversion
invariance of `mu` in addition to the smoothing construction's assumptions,
because that is a parameter of the published restricted-transpose construction.

`smoothFunctional_separates` assumes all of the measure hypotheses above,
including inversion invariance, together with admissibility, irreducibility and
`eta != 0`. For every smooth-dual vector `phi`, it proves

```
(for every f, eta(S_(pairing(phi))(f)) = 0) iff phi = 0.
```

For the forward direction, a Haar local unit `u` fixes `phi` under the smooth-dual
representation. With `e(x) = u(x^-1)`, the identity between integrated transpose
and the smooth-dual integrated action gives `S_(pairing(phi))(e) = phi`.
Right translation then gives
`S_(pairing(phi))(R_a e) = rhoDual(a) phi`. The hypothesis places `phi` in the
common orbit kernel, which is bottom. The reverse direction follows by
linearity. This argument does not use reflexivity of the smooth bidual.

## Convolution annihilators

The final two lemmas use the published convolution convention and identity

```
S_ell(f*g) = S_(pairing(S_ell(f)))(g).
```

`generalizedCoefficient_left_annihilator` states, for nonzero `eta`,

```
(for every g, D_(ell,eta)(f*g) = 0) iff S_ell(f) = 0.
```

It follows immediately from `smoothFunctional_separates`; `ell` need not be
nonzero. Its assumptions include inversion invariance of the measure.

`generalizedCoefficient_right_annihilator` states, for nonzero `ell`,

```
(for every f, D_(ell,eta)(f*g) = 0)
  iff (for every phi in SmoothDual rho, eta(S_(pairing(phi))(g)) = 0).
```

The right side is independent of `ell`. Surjectivity of `S_ell` proves the forward
direction, and substitution of `phi = S_ell(f)` proves the reverse direction.
This result does not require inversion invariance or nonvanishing of `eta`.
Both annihilator lemmas retain the admissible irreducible representation and
left/right invariant positive measure hypotheses of the relevant separation
result.

## Provenance

These are internal constructions and elementary consequences of the published
Library APIs named above, rather than a transcription of an external theorem.
The Markdown describes the implemented Lean proofs. No anti-homeomorphism,
distribution-invariance assumption, genericity, or multiplicity hypothesis is
used here. The later kernel comparison must separately exchange the two
annihilators and apply admissible Schur's lemma.
