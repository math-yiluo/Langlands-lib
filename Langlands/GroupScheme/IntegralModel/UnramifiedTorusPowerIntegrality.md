# Integrality of a point from a power, through an unramified split torus

This module proves two auxiliary facts for the maximality of the integral points
of a supplied model over a nonarchimedean local field: a power lemma for compact
subgroups, and a criterion that turns integrality of a power of a point into
integrality of the point, when the point lies on a closed split torus of the
model over the maximal unramified integers. All rings and schemes use one
arbitrary universe `u`.

## Compact subgroups and open subgroups

`exists_pow_mem_of_isCompact_of_isOpen` works in an arbitrary topological group
`X`. If `C` is a subgroup of `X` that is compact as a subset, `H` is a subgroup of
`X` that is open as a subset, and `g ∈ C`, then there is `n > 0` with
`g ^ n ∈ H`. The proof regards `H ∩ C` as an open subgroup of the compact group
`C`, so it has finite index (`Subgroup.quotient_finite_of_isOpen`), and an element
of a group has a positive power in any subgroup of finite index
(`Subgroup.exists_pow_mem_of_index_ne_zero`).

## Generic values of split tori and powers

Let `R` be a domain with specified fraction field `K` and `N : IntegralModel R K H`
a supplied model of a group scheme `H` over `Spec K`. For a finite type `I` and a
homomorphism `i` from the split torus `splitTorus (Spec R) I` to `N.group`, the
Library value `N.genericSplitTorusValue i t ∈ rationalPoints H` is the generic
point of the torus with coordinates `t : I → Kˣ`. `genericSplitTorusValue_pow`
states `N.genericSplitTorusValue i (t ^ n) = (N.genericSplitTorusValue i t) ^ n`
for every natural number `n`. The proof writes the value as the image of a
point of the split torus under the induced map on rational points
(`rationalPoints.map`), and both the coordinate equivalence of the split torus
and that map are group homomorphisms.

## Units of the maximal unramified integers

Let `F` be a nonarchimedean local field, `inertiaFixedField F` its maximal
unramified (separable inertia-fixed) extension, `fixedFieldIntegers F` the
integers of that field, and `fixedFieldValuation F` its valuation, all as in the
Library. `exists_unit_of_pow` states: if `x` is a unit of `inertiaFixedField F`,
`n ≠ 0`, and `x ^ n` is the image of a unit of `fixedFieldIntegers F`, then `x`
itself is the image of a unit of `fixedFieldIntegers F`. The proof shows that a
unit of the integers has valuation `1`, so `v(x) ^ n = 1` and hence `v(x) = 1`;
then `x` and `x⁻¹` both have valuation at most `1` and give inverse units of the
integers.

## Integrality from a power

Let `M : IntegralModel 𝒪[F] F G` be a supplied model of a group scheme `G` over
`Spec F`, and `M.baseChangeUnramified` its Library base change to the maximal
unramified integers. `mem_integralPoints_of_pow_mem_of_unramifiedSplitTorus`
takes a finite type `I`, a homomorphism
`i : splitTorus (Spec (fixedFieldIntegers F)) I ⟶ M.baseChangeUnramified.group`
that is a closed subgroup (`IsClosedSubgroup i`), a rational point `g` of `G`,
coordinates `t : I → (inertiaFixedField F)ˣ`, and `n ≠ 0`. It assumes

- the extension of `g` to `inertiaFixedField F`, `rationalExtend F (inertiaFixedField F) G g`,
  equals `M.baseChangeUnramified.genericSplitTorusValue i t`, and
- `g ^ n ∈ M.integralPoints`,

and concludes `g ∈ M.integralPoints`.

The proof uses the published descent criterion
`mem_integralPoints_rationalExtend_iff_unramified`: a rational point of `G` is
integral for `M` exactly when its extension is integral for
`M.baseChangeUnramified`. Applied to `g ^ n`, together with
`genericSplitTorusValue_pow`, it shows that the generic torus value at `t ^ n` is
integral. The published criterion `genericSplitTorusValue_mem_integralPoints_iff`
for closed split tori says this means that every coordinate `t j ^ n` comes from a
unit of `fixedFieldIntegers F`. By `exists_unit_of_pow` every `t j` comes from
such a unit, so the same two criteria, read backwards, give `g ∈ M.integralPoints`.

## Provenance

These are internal lemmas. They implement the split-torus step in the proof of
Maculan (2017), Proposition 4.6 (printed p. 11 / PDF p. 12), which shows that the
integral points of a torus over the integers are the unique maximal bounded subgroup
of its rational points: in the split case `𝔾ₘʳ(K°)` is the unique maximal bounded
subgroup of `𝔾ₘʳ(K)`, and the general case passes to an unramified extension where
the torus splits. Here boundedness is replaced by the power condition: a coordinate
whose positive power is a unit of the integers is itself a unit, and the descent
from the maximal unramified integers to `𝒪[F]` is the published Library criterion.
The Lean statements are not quoted from that source. The module does not prove that
any model torus splits over the maximal unramified integers; that input is supplied
as the hypothesis on `i` and `t`.
