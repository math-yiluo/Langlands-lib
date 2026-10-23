# Uniform nilpotence index of a central character

Author: Worker 19.

This module constructs `Langlands.centralCharacterNilpotenceIndex`, an
extended natural number attached to a representation and a full-center
character. It measures the least common power that annihilates the whole
uniform generalized character space. It is an algebraic prerequisite for
Silberger's critical and weakly critical exponents. It does not construct
those exponents or assert any analytic or Jacquet comparison theorem.

## Objects and quantifiers

The coefficient ring `R` is any commutative ring, `G` is any group, and `V`
is an `R`-module. The ring, group and carrier have independent universes.
The representation `ρ` is an actual `Representation R G V`, and `χ` is a
homomorphism from the full subgroup center of `G` to `Rˣ`. No topology,
smoothness, admissibility, finite generation or finite length is assumed.

The module reuses the published `centralCharacterSpace ρ χ n` and
`generalizedCentralCharacterSpace ρ χ` from
`Langlands.Representation.Exponents.Central`. Write them as `C_n` and `C_∞`.
Their memberships mean, respectively,

```
v ∈ C_n  iff  for every central z, (ρ(z) - χ(z) • 1)^n v = 0,
v ∈ C_∞  iff  there exists n such that v ∈ C_n.
```

The power in the second line may depend on the vector, but it must work for
all central elements. Each space is an actual invariant subspace, and `C_∞`
is the increasing union of the `C_n`. In particular, `C_0 = 0`.

The Prop-valued definition `IsCentralNilpotenceBound ρ χ n` is the inclusion
`C_∞ ≤ C_n`. Thus a bound is one exponent for every vector in the component
and every central element. This strengthens the per-vector bound already
present in generalized-space membership.

`centralCharacterNilpotenceIndex ρ χ : ℕ∞` uses the least such natural number
if a bound exists and infinity otherwise. Classical choice decides existence
and `Nat.find` selects the least witness; the construction does not accept a
bound or decomposition as input. The convention for an absent character is
zero, since its generalized space is zero. An unbounded component has index
infinity. These conventions extend the finite nonzero setting of the source.

This index is not the dimension of the component and not a Jordan–Hölder
multiplicity. For example, a nonzero representation on which the prescribed
character acts scalarly on the center has index one, regardless of its
dimension or number of composition factors: power one annihilates it, while
power zero cannot annihilate a nonzero vector. This example explains the
definition; no classification or finite-length result is assumed.

## Intrinsic laws and implemented proofs

The module proves the following laws.

- `isCentralNilpotenceBound_mono`: a larger natural number is again a bound.
  The proof composes the defining inclusion with the published monotonicity
  of the finite character spaces.
- `centralCharacterNilpotenceIndex_le_iff`: for every natural number `n`, the
  index is at most `n` exactly when `n` is a bound. In the finite case this
  follows from the least-witness property and monotonicity; in the unbounded
  case both sides are false.
- `centralCharacterNilpotenceIndex_eq_zero_iff`: the index is zero exactly
  when `C_∞ = 0`. The proof specializes the preceding law to zero and uses
  `C_0 = 0`.
- `centralCharacterNilpotenceIndex_eq_top_iff`: the index is infinity exactly
  when no finite bound exists. The proof unfolds the two construction cases.
- `isCentralNilpotenceBound_iff_eq`: a bound `n` is equivalent to `C_n = C_∞`.
  One inclusion is the defining bound and the other is the inclusion of an
  indexed summand into the increasing supremum.
- `isCentralNilpotenceBound_equiv_iff` and
  `centralCharacterNilpotenceIndex_equiv`: an actual equivariant linear
  equivalence preserves every bound and therefore the index. The proof moves
  vectors through the equivalence and its inverse using the published
  intertwiner preservation of finite and generalized character spaces. The
  two carrier universes remain independent.

No finiteness or decomposition theorem is hidden in these proofs.

## Original sources and derived scope

The generalized spaces come from W. Casselman, *Introduction to the theory of
admissible representations of p-adic reductive groups*, 1 May 1995 draft,
section 2.1, printed/PDF p.21. The retained source is registered as
`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
Casselman defines the spaces using one power for all central elements and
then takes their increasing union. Proposition 2.1.9(b) gives simultaneous
stabilization in a center-finite, finitely generated representation over an
algebraically closed field. The present construction records the least
stabilization index when it exists, with infinity allowed in its more general
algebraic setting. It neither assumes nor proves Proposition 2.1.9.

The intended exponent application is motivated by A. J. Silberger,
*Introduction to harmonic analysis on reductive p-adic groups* (1979),
section 2.4, printed pp.90–92, especially p.91, and section 4.5, printed p.189.
The retained source is registered as `silberger-1979-harmonic-analysis`,
SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
PDF page number is printed page plus six. These passages were read in their
page images as well as extracted text; both source fingerprints were checked.
No errata for these sources was present in the supplied Library.

On p.91 Silberger considers the generalized dual-character component of the
opposite Jacquet quotient and calls the maximum of its per-vector uniform
orders `d(χ)`, the multiplicity of the exponent. Its finiteness uses admissibility
and finite type. On p.92 the corresponding quotient component is killed by
power `d(χ)` and its preceding finite-character space is proper. This confirms
that the quantity is a nilpotence order, rather than a composition-factor
count. On p.189 weak criticality requires a strict decrease of this order for
every extending weak exponent along a proper smaller p-pair. It is not defined
merely by the absence of such exponents.

The construction here is derived from these finite-character spaces and the
least-common-order interpretation. It applies to an arbitrary representation
and its full center; it does not identify such an arbitrary input with
Silberger's normalized dual exponent component. That comparison requires the
actual opposite Jacquet module, normalization, restriction to the split center,
and the dual/primal generalized-component correspondence. In the finite,
center-decomposed setting, a common polynomial annihilates a component exactly
when its transpose annihilates the full dual component; this explains the
intended comparison but is not a theorem in this module. A contragredient
uses inverse group elements and corresponding inverse characters, so the
comparison must also keep that convention explicit.

For GL block Levis the full algebraic center is the split scalar torus. The
identification with its concrete scalar-coordinate group and all smooth,
finite-length and Jacquet comparison results are later obligations. This
module introduces no modulus, induction, Jacquet action, weak-critical
predicate, support choice or square-integrability conclusion. Its only
representation-theoretic dependency is the published `Exponents.Central`.
