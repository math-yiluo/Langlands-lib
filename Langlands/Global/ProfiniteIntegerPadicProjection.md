# Canonical projections from residue limits to p-adic integers

This module constructs the canonical ring homomorphisms

\[
\widehat{\mathbb Z}\longrightarrow\mathbb Z_p,\qquad
\widehat{\mathbb Z}^{(m)}\longrightarrow\mathbb Z_p
\quad\text{when }\gcd(p,m)=1.
\]

Here the source rings are the existing `ProfiniteIntegerRing` and
`PrimeToProfiniteIntegerRing m`: actual compatible families of finite residues,
with their subspace topologies from the corresponding products of finite
discrete rings. The target is Mathlib's `PadicInt p`, with its existing p-adic
metric topology. Throughout, `p : ℕ` has the hypothesis `[Fact p.Prime]`.
The excluded modulus `m : ℕ` is arbitrary.

## Construction and finite reductions

In namespace `Langlands.Global.ProfiniteIntegerRing`,
`primePowerModulus p n` is the positive integer \(p^n\), for every natural
exponent, including zero. `toPadic p` applies Mathlib's `PadicInt.lift` to the
ring homomorphisms

\[
x\longmapsto x_{p^n}\in\mathbb Z/p^n\mathbb Z.
\]

The cone compatibility required by this lift is exactly the existing
`ResidueLimit.transition_comp_reduction`, specialized to divisibility of
prime powers. Consequently `toZModPow_toPadic` states the exact formula

\[
\operatorname{toZModPow}_n(\operatorname{toPadic}_p(x))=x_{p^n}.
\]

`toPadic_intCast` asserts that every integer residue family maps to the same
integer in \(\mathbb Z_p\). This follows from the ring homomorphism law on
integer casts. `toPadic_unique` says that any ring homomorphism with the
displayed prime-power reduction formula equals `toPadic p`; no continuity
hypothesis is needed for this uniqueness assertion. Its proof uses Mathlib's
joint injectivity of all `toZModPow` maps.

In namespace `Langlands.Global.PrimeToProfiniteIntegerRing`,
`primePowerModulus p m h n` uses
`h : Nat.Coprime p m` to regard \(p^n\) as a permitted away modulus.
The identically named `toPadic`, `toZModPow_toPadic`, `toPadic_intCast`,
`continuous_toPadic`, and `toPadic_unique` give the corresponding construction
and laws for the away source ring. These use the same finite-residue lift.

The theorem `PrimeToProfiniteIntegerRing.toPadic_restrict` states

\[
\operatorname{toPadic}_{p,m,h}(\operatorname{restrict}_m(x))
=\operatorname{toPadic}_p(x).
\]

Its proof compares reductions modulo every \(p^n\). On these coordinates
the existing restriction of residue families is evaluation at the same
positive modulus, so the coordinates agree by definition. This also covers
the degenerate excluded moduli whenever a coprimality witness exists; the
theorem makes no assertion for a prime dividing the excluded modulus.

## Continuity

The helper `Langlands.Global.ResidueLimit.continuous_padic_lift` applies to
any topological `NonAssocSemiring R` and a compatible family of ring
homomorphisms \(f_n:R\to\mathbb Z/p^n\mathbb Z\), each continuous. It proves
that `PadicInt.lift` of this cone is continuous into the existing p-adic
topology. No continuity of the operations on `R` is assumed or needed.

For an arbitrary \(x\in R\) and \(\varepsilon>0\), the proof chooses \(n\)
with \(p^{-n}<\varepsilon\). Continuity of \(f_n\) into the discrete residue
ring gives a neighborhood on which \(f_n(y)=f_n(x)\). The lift reduction
formula places the difference of the lifted values in the kernel of
`toZModPow n`. Mathlib identifies this kernel with the ideal \((p^n)\), and
membership in that ideal is equivalent to the norm bound
\(\|\operatorname{lift}(y)-\operatorname{lift}(x)\|\le p^{-n}\).
The metric criterion for continuity finishes the proof.

Both `continuous_toPadic` results apply this helper to the existing continuous
coordinate reductions. Thus continuity is proved for the existing source and
target topologies, without transporting a topology along a proposed comparison.

## Provenance and scope

This is an internal construction derived from the published
`Langlands.Global.ProfiniteIntegerRing` definitions and Mathlib's p-adic
inverse-limit interface in `Mathlib.NumberTheory.Padics.RingHoms`. Its proof
dependencies include `PadicInt.lift`, `lift_spec`, `ker_toZModPow`,
`ext_of_toZModPow`, and the p-adic norm estimates in
`Mathlib.NumberTheory.Padics.PadicIntegers`. The construction rationale and
implemented proof are given above; no new claim is attributed to original
literature.

These projections supply a scalar interface for comparing full or away Tate
limits with their prime-power coordinate limits. This module proves neither
surjectivity of a projection nor an equivalence with a product of p-adic
integer rings. It introduces no finite-adele identification, rationalization,
Tate-module action, or geometric assertion. Those constructions and comparison
theorems are separate units.
