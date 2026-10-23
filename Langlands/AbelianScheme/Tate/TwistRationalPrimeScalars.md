# Rational residue scalar compatibility of prime-adic twist projections

This module equips the existing rational-to-prime maps on actual
roots-of-unity twists with semilinear structures over the canonical
rational residue scalar projections. It works over any commutative ring
`R`. The local prime is `p : ℕ` with `[Fact p.Prime]`; a selected-index
predicate `P : ℕ → Prop` must satisfy `hP : ∀ n : ℕ, P (p ^ n)`.

Write
\[
 A=\mathbb Q\otimes_{\mathbb Z}\operatorname{ProfiniteIntegerRing},
 \qquad
 T_P(1)_{\mathbb Q}=\mathbb Q\otimes_{\mathbb Z}T_P(1).
\]
Here \(T_P(1)\) is the existing `Divisibility.Integral R P` of
coherent actual roots of unity, and its rationalization is
`Divisibility.Rational R P`. The local target is the existing
`TateTwist.Rational R p`, namely
\(\mathbb Q_p\otimes_{\mathbb Z_p}T_p(1)\).

The scalar projection
\(\pi_p:A\to\mathbb Q_p\) is the published
`Global.ProfiniteIntegerRing.rationalToPadic p`; its normalization is
\(\pi_p(q\otimes a)=q\,\operatorname{toPadic}_p(a)\), using the
canonical rational cast and the inclusion \(\mathbb Z_p\to\mathbb Q_p\).

## Locally installed scalar modules

In namespace `Langlands.TateTwist.Divisibility`,
`rationalScalarModule R P` packages the already published action
`rationalScalarAction R P` as an `A`-module using `Module.compHom`.
It is a definition for local installation, not a global instance.
`rationalScalarModule_smul` identifies this module's scalar multiplication
with evaluation of the existing action, by reflexivity.

`rationalScalarModule_scalarTower` proves
`IsScalarTower ℚ A (Rational R P)` under this local installation.
It uses the existing tensor-product rational actions. The proof constructs
the tower directly: rational linearity of the algebra homomorphism
`rationalScalarAction` and evaluation of scalar multiples of linear maps
give \((q\mathbin{\cdot}a)\mathbin{\cdot}x
=q\mathbin{\cdot}(a\mathbin{\cdot}x)\).

## Selected and full projections

For \(a\in A\) and \(x\in T_P(1)_{\mathbb Q}\),
`rationalToPrime_scalarAction` proves
\[
 r_{P,p}(a\mathbin{\cdot}x)
   =\pi_p(a)\mathbin{\cdot}r_{P,p}(x),
\]
where \(r_{P,p}\) is the existing `rationalToPrime R P p hP`.
The scalar action on the left is expressed explicitly as
`rationalScalarAction R P a x`.

The proof uses tensor induction first on \(a\), then on \(x\).
For \(a=q\otimes a_0\) and \(x=r\otimes x_0\), the published
pure-tensor formulas reduce the claim to
\[
 (qr)\otimes
   \bigl(\operatorname{toPadic}_p(a_0)\mathbin{\cdot}
     \operatorname{toPrime}(x_0)\bigr)
 =
 \bigl(q\,\operatorname{toPadic}_p(a_0)\,r\bigr)
       \otimes\operatorname{toPrime}(x_0).
\]
The imported integral law `toPrime_smul`, tensor balancing over
\(\mathbb Z_p\), and multiplication in \(\mathbb Q_p\) prove this
identity. Additivity proves the sum cases.

`rationalToPrimeSemilinear R P p hP` bundles the same additive map
as a semilinear map over \(\pi_p\), using `rationalScalarModule`
locally. `rationalToPrimeSemilinear_apply` is the reflexive equality
with `rationalToPrime`. The full-index specialization is
`rationalFullToPrimeSemilinear R p`. Its scalar law is
`rationalFullToPrime_scalarAction`, and its underlying-function
identity is `rationalFullToPrimeSemilinear_apply`.

## Away scalars and projections

Let `m : ℕ` be arbitrary and `h : Nat.Coprime p m`. Set
\[
 A^{(m)}=\mathbb Q\otimes_{\mathbb Z}
          \operatorname{PrimeToProfiniteIntegerRing}(m).
\]
The source twist is the existing `RationalAway R m`, which selects
the positive moduli coprime to \(m\). The scalar projection
\(\pi_p^{(m)}:A^{(m)}\to\mathbb Q_p\) is
`Global.PrimeToProfiniteIntegerRing.rationalToPadic p m h`.
Only \(p\) is assumed prime.

`rationalAwayScalarModule R m` locally installs the published
`rationalAwayScalarAction R m` as a module.
`rationalAwayScalarModule_smul` identifies its action by reflexivity,
and `rationalAwayScalarModule_scalarTower` proves compatibility with
the existing rational action by the same direct tower argument.

`rationalAwayToPrime_scalarAction` proves
\[
 r^{(m)}_p(a\mathbin{\cdot}x)
   =\pi_p^{(m)}(a)\mathbin{\cdot}r^{(m)}_p(x).
\]
Its tensor-induction proof uses `awayToPrime_smul` and the away
pure-tensor formulas, followed by the same balancing calculation.
`rationalAwayToPrimeSemilinear R p m h` packages the existing
`rationalAwayToPrime R p m h` with this law.
`rationalAwayToPrimeSemilinear_apply` identifies the underlying
function by reflexivity.

## Restriction and naturality

`rationalAwayToPrimeSemilinear_restrictAway` states pointwise that
rational restriction from the full twist to the away twist, followed
by the away semilinear projection, equals the full semilinear
projection. The proof evaluates the already published equality of
rational-linear maps `rationalAwayToPrime_restrictAway`.

For any commutative ring `S` and ring map `f : R →+* S`,
`rationalToPrimeSemilinear_map` states that applying the induced
selected rational twist map and then projecting equals projecting
and then applying the induced local rational twist map.
`rationalAwayToPrimeSemilinear_map` gives the away specialization,
using `h.pow_left n` to select every prime power. Both are pointwise
consequences of the existing equality `rationalToPrime_map`.
Thus these laws retain exactly the previously constructed root maps.

## Provenance and scope

This is an internal construction from the published
`TwistRationalPrime`, `TwistPrimeScalars`, `TwistRationalScalars`,
and `RationalProfiniteIntegerPadicProjection` modules and Mathlib's
module and tensor-product constructions. The implemented proofs are
described above. No new claim is attributed to original literature.

No characteristic, rank, finiteness, or primitive-root hypothesis is
needed. The module introduces no rational topology or continuity
claim, no product or restricted-product comparison, no finite-adele
scalar compatibility, and no injectivity or surjectivity assertion.
It chooses no basis or trivialization of a twist. The geometric
monodromy, Weil pairing, and PEL specializations remain separate
obligations.
