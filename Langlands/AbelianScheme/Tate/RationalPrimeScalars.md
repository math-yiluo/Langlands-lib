# Rational scalar compatibility of actual Tate prime coordinates

This module equips the canonical rational prime-coordinate maps of actual
Tate modules with semilinearity over the canonical rational residue scalar
projections. It covers selected levels containing all powers of the chosen
prime, full levels, and levels coprime to a natural modulus.

## Actual carriers and coefficient maps

Fix a scheme `S`, a commutative group object `G` in `Over S`, a test scheme
`T : Over S`, and a prime natural number `p`. For a level predicate `P`, write

\[
V_P=\mathbb Q\otimes_{\mathbb Z}\operatorname{Integral}(G,T,P),
\qquad
V_p=\mathbb Q_p\otimes_{\mathbb Z_p}\operatorname{PrimeAdic.Integral}(G,T,p).
\]

The integral carriers are the previously constructed compatible families of
actual torsion sections, with divisibility transitions. Full levels use
`P = fun _ => True`; away levels use `P = fun n => Nat.Coprime n m`.
The local coefficient and carrier types are Mathlib's `ℤ_[p]` and `ℚ_[p]`
and the published actual `PrimeAdic` Tate carriers.

For selected levels, `hP : ∀ n, P (p ^ n)` ensures that every prime-power
coordinate can be extracted. For away levels this follows from
`h : Nat.Coprime p m`. No characteristic, finite-etaleness, rank or
finite-level finiteness hypothesis is used. The modulus `m` is any natural
number. When `m = 0`, no prime meets the coprimality hypothesis for extraction;
the away carrier and module definitions still make sense.

The full scalar algebra is
`ℚ ⊗[ℤ] Global.ProfiniteIntegerRing`, and its local algebra homomorphism is
`Global.ProfiniteIntegerRing.rationalToPadic p`. The away scalar algebra is
`ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m`, with local homomorphism
`Global.PrimeToProfiniteIntegerRing.rationalToPadic p m h`.
These are imported canonical maps. On pure tensors they send
`q ⊗ a` to `q * toPadic(a)` in `ℚ_[p]`.
No finite-adele comparison hypothesis is involved.

## Module structures from the existing actions

In `Langlands.GroupScheme.Tate`, `rationalScalarModule` and
`rationalAwayScalarModule` expose the existing `rationalScalarAction` and
`rationalAwayScalarAction` as module structures. Each is defined by
`Module.compHom` from the corresponding rational-algebra action into
`Module.End ℚ`. They are definitions for local installation, not global
instances.

The lemmas `rationalScalarModule_smul` and
`rationalAwayScalarModule_smul` identify the module operation with evaluation
of those actions. The two `*_scalarTower` lemmas prove compatibility with the
existing rational multiplication. Their proofs use rational linearity of
the action homomorphisms, applied to a vector, to verify the scalar-tower
identity directly.

## Scalar compatibility of prime coordinates

In `Langlands.GroupScheme.Tate.PrimeComparison`,
`rationalToPrime_scalarAction` proves

\[
c_p(a x)=\rho_p(a)c_p(x),
\]

where `c_p` is exactly `rationalToPrime G T P p hP` from `RationalPrime`,
and `ρ_p` is the canonical full rational scalar projection above.
`rationalFullToPrime_scalarAction` specializes the result to the full carrier.
`rationalAwayToPrime_scalarAction` proves the analogous formula for the
away action and the canonical away scalar projection.

Both proofs use induction first on the tensor scalar and then on the tensor
vector. For scalar `q ⊗ a` and vector `r ⊗ x`, the existing action gives
`(q * r) ⊗ (a • x)`. Integral scalar compatibility from `PrimeScalars`
identifies its extracted second factor with
`toPadic(a) • toPrime(x)`. Balancing over `ℤ_[p]` moves that integral local
scalar into the `ℚ_[p]` tensor factor. The remaining equality is
commutative multiplication in `ℚ_[p]`; additivity gives the induction steps.
This argument uses the actual integral residue action, rather than assuming
the desired rational scalar compatibility.

`rationalToPrimeSemilinear`, `rationalFullToPrimeSemilinear`, and
`rationalAwayToPrimeSemilinear` bundle the existing additive coordinate maps
as semilinear maps along the ring homomorphisms underlying `ρ_p`. Their
`*_apply` lemmas are definitional identifications with the original
`rationalToPrime`, `rationalFullToPrime`, and `rationalAwayToPrime`.
There is no new choice of coordinate map.

## Restriction, naturality and abelian schemes

`rationalAwayToPrime_restrictAway_scalarAction` restricts both a full
rational residue scalar and a full rational Tate vector to the away system,
then extracts the retained prime coordinate. The result is the full local
scalar projection acting on the full prime coordinate. Its proof combines
the existing full-to-away action compatibility, the coordinate restriction
identity from `RationalPrime`, and the full scalar compatibility above.

`rationalToPrimeSemilinear_map` and `rationalAwayToPrimeSemilinear_map` state
pointwise naturality for actual group-object homomorphisms. They reuse
`rationalToPrime_map` from `RationalPrime`, so the local map is precisely the
published `PrimeAdic.rationalMap`, not an arbitrary linear map.

The `Langlands.AbelianScheme.Tate` namespace specializes both module
definitions to `A.toGrp` for an actual abelian scheme. Its `PrimeComparison`
namespace supplies selected, full and away semilinear aliases, and selected
naturality for actual abelian-scheme homomorphisms. This selected naturality
includes the full and away cases by choosing their predicates. Evaluation
at a geometric fibre uses the corresponding test scheme `T`.

## Provenance and scope

The source convention is Harris–Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), Chapter I, printed p.18 (PDF p.26), which
defines the actual full and away Tate limits and their rationalizations.
The registered source is `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The module is a derived algebraic compatibility construction using
`RationalScalars`, `PrimeScalars`, `RationalPrime`, and
`Global.RationalProfiniteIntegerPadicProjection`. The arbitrary commutative
group object, test scheme, level predicate and natural modulus are internal
generalizations. The direct scalar-tower proof route was coordinated with
Worker 92's analogous twist construction.

No injectivity or surjectivity of the coordinate maps, restricted-product
equivalence, finite-adele coordinate identification, rational topology,
continuity, monodromy or Weil pairing is asserted here. The rational
restricted-product statement and scalar comparison statements remain
separate proof obligations.
