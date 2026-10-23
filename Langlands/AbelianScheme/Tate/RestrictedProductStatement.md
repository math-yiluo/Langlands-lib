# Exact restricted-product comparison for actual rational Tate modules

This module states the full and away algebraic comparison obligations
for actual rational Tate modules. It does not prove the obligations.
The targets use the restricted-product carriers and the canonical
rational prime-coordinate maps from the preceding construction modules.

## Parameters and actual carriers

Let `S` be a scheme, `G : Grp (Over S)` a commutative group scheme,
and `T : Over S` a test scheme. The commutativity hypothesis is
`[IsCommMonObj G.X]`. No finiteness, rank, characteristic or geometric
point hypothesis is imposed in these algebraic statements.

`RationalFull G T` is the actual tensor product
`ℚ ⊗[ℤ] Full G T`. The integral factor is the coherent limit of
multiplication-kernel sections at all positive orders, with
multiplication-by-quotient transitions. The local factor at a prime
`p` is `PrimeAdic.Rational G T p`, the tensor product
`ℚ_[p] ⊗[ℤ_[p]] PrimeAdic.Integral G T p`, where the integral limit
uses all powers `p ^ n` and transition multiplication by `p`.

`RationalRestrictedProduct G T` consists of families in these local
rational factors that belong to the image of
`PrimeAdic.toRational`, the map `x ↦ 1 ⊗ x`, at all but finitely
many primes. It uses Mathlib's restricted-product carrier and its
coordinatewise additive commutative group. The integral subsets
are images; injectivity of integral rationalization is not hidden
in a type identification.

For an excluded modulus `m : ℕ`, `RationalAway G T m` uses positive
orders coprime to `m`, and `RationalAwayRestrictedProduct G T m`
uses primes coprime to `m`. For positive `m` this excludes its prime
divisors. The boundary cases are retained: `m = 1` keeps all primes;
`m = 0` gives the trivial order-one inverse system and the unique
empty restricted family.

## Precise obligations

In namespace `Langlands.GroupScheme.Tate.PrimeComparison`,
`RationalRestrictedProductComparison G T` asserts existence of an
additive equivalence

\[
e:\mathbb Q\otimes_{\mathbb Z}T(G,T)
  \simeq_+ \prod_p' V_p(G,T)
\]

such that, for every source element `v` and every `p : Nat.Primes`,

\[
(e(v))_p=\operatorname{rationalFullToPrime}_p(v).
\]

Thus the witness is constrained to the constructed coordinate map
on every element. In particular, on pure tensors it must have
coordinate

\[
(e(q\otimes x))_p=\iota_p(q)\otimes\operatorname{fullToPrime}_p(x),
\]

where the right-hand tensor product is over the local integer ring
and the left-hand tensor product is over the integers. This formula
follows from the imported `rationalFullToPrime_tmul` theorem.
The existence assertion includes the claim that these coordinates
satisfy the cofinite integrality condition, and that the resulting
map is both injective and surjective. It cannot be satisfied by an
unrelated additive equivalence.

`RationalAwayRestrictedProductComparison G T m` makes the identical
assertion for the away source and target. Its coordinate equation
uses `rationalAwayToPrime G T p m h`, with the coprimality witness
supplied by the retained-prime subtype. The corresponding imported
pure-tensor formula gives its normalization.

`RationalRestrictedProductComparisons G T` is precisely the
conjunction of the full obligation and the away obligation for
every natural `m`. All three declarations are Prop-valued definitions.
A separate proof task must establish the combined proposition for
arbitrary parameters.

The namespace `Langlands.AbelianScheme.Tate.PrimeComparison`
provides the three matching Prop-valued abbreviations using
`A.toGrp` for an actual bundled abelian scheme `A`. At a geometric
point `s`, use `T = Over.mk s` to obtain the intended application.

## Why this is the intended algebraic comparison

The anticipated mathematical argument decomposes the integral
limit into its prime-power components by finite-order Chinese
remainder decomposition. Each prime-adic limit has no prime torsion:
if multiplication by `p` kills a coherent family, its coordinate at
`n` is multiplication by `p` of its coordinate at `n + 1`, hence
vanishes. Local rationalization is localization at powers of `p`,
so every local rational element has a prime-power denominator.
A restricted family has only finitely many nonintegral coordinates;
clearing their denominators gives one global integer denominator
and an integral family. Conversely, a rational tensor has a global
denominator, whose prime divisors give the finite possible exceptions
to integrality. The integral decomposition and local torsion argument
supply injectivity. This is a rationale for the stated generality,
not an implemented proof; these steps remain obligations of the
separate exact-target proof task.

The comparison is stated as an additive equivalence. This module
does not introduce a rational scalar action on the restricted product
or assert a bundled rational-linear or finite-adelic equivalence.
It asserts no topology or continuity on rational carriers. Those
extensions require their own constructions and compatibility proofs;
the algebraic comparison here is not an assumed identification for
them. Monodromy, rank, pairings and finite étaleness are also outside
this statement unit.

## Provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Chapter I, printed p.18 (PDF p.26), gives the
actual full and away Tate limits and their rationalizations over
the integers. Chapter III, printed pp.91–92 (PDF pp.99–100), uses
the full and prime-to-p rational Tate modules in PEL level structures.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The exact-coordinate restricted-product proposition and its
arbitrary commutative group-scheme/test-scheme generality are derived
infrastructure, not a theorem attributed to those pages. The actual
carriers and coordinate maps are reused from the preceding Tate
modules. The argument above explains why this is the required
comparison rather than defining the global rationalization to be
the restricted product. No comparison proof is supplied or assumed
by these declarations.
