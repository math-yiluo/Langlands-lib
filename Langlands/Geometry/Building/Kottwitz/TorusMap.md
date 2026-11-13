# Torus Kottwitz homomorphisms from the norm characterization

Source: Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
§11.1, Proposition 11.1.1, printed pp. 420–422 (PDF pp. 451–453).
The November 2024 corrections do not change Proposition 11.1.1.
The positive additive valuation convention follows the correction to §2.5.

All declarations are in `Langlands.Geometry.Building.Kottwitz`.
Let `F` be any nonarchimedean local field, `K = UnramifiedClosure F` and
`E = SeparableClosure F`. The original commutative group scheme `T` may be
defined over a field `k` mapping to `K` and `E` in a scalar tower, with
`Normal k K`. This coefficient-field parameter lets the same formula handle
a `K`-torus (`k = K`) and an `F`-torus (`k = F`) without introducing iterated
base changes in the point carrier. No local-field hypothesis on `K` or any
finite splitting extension is used.

`torusKPoints F k T` is the actual group of `K`-coefficient points of `T`.
For `k = K` it is canonically the Library's `rationalPoints T.toGrp` by
`GaloisPointComparison.rationalCoeffEquiv`; for general `k` it is canonically
the rational points of `T_K` by `baseChangeCoeffEquiv`.
`TorusTarget F k T` is the integral inertia quotient of the cocharacter
lattice of the actual base change `T_E`. Relative inertia is the kernel of
restriction from `Aut_k(E)` to `Aut_k(K)`, hence consists of the automorphisms
fixing `K` pointwise.

`extendGeometricCocharacters` extends actual cocharacters from `T_L` to
`T_E`, composing base change with the canonical comparison of direct and
iterated pullbacks in the field tower. `TorusNormLawAt` states the KP norm
square for one finite Galois intermediate splitting field `L/K`: the
constructed relative Galois norm of a point maps to the inertia class of its
split-torus valuation. The valuation is `normalizedIntermediateValuation F L`,
selected by equivalence to the actual restricted spectral valuation and
surjectivity onto the full integer value group. Its unconditional existence
and uniqueness obligation is `NormalizedIntermediateValuationStatement`.
The split valuation is the actual character-pairing construction
`splitValuation`; no map on torus points is supplied as input.

`IsTorusKottwitzHom` requires this norm law for every finite Galois splitting
field. `torusKottwitz` is classical epsilon among homomorphisms with that law;
the ambient type is inhabited by the trivial homomorphism. Its specification
is the unconditional `TorusKottwitzExistenceStatement` in the companion
statement module. The helper `torusKottwitz_spec` proves only the elementary
epsilon implication from existence. It does not prove KP Proposition 11.1.1.
The affine instance needed for the norm is obtained from the proved fact
that a torus is connected reductive.

For an `F`-torus, `TorusKottwitzEquivariant` expresses equivariance under the
actual group `Aut_F(K)` acting by coefficient automorphisms on points and by
the descended cocharacter action on the target. `TorusInvariantTarget` is
the fixed submodule of the inertia quotient. `IsTorusKottwitzRestriction`
identifies a homomorphism from `T(F)` to these invariants with the restriction
of `torusKottwitz` after the actual coefficient inclusion `F → K`.
`torusKottwitzRational` selects that restriction by epsilon; its unconditional
existence, uniqueness and restriction law are stated in
`TorusKottwitzDescentStatement`. Invariant inclusion is the actual subgroup
inclusion. `Multiplicative` changes notation for additive targets only.

These definitions contain no prescribed kernel or boundedness hypothesis.
The existence, uniqueness, independence, surjectivity and equivariance
assertions are proposition definitions awaiting proofs; this unit does not
claim those proofs or the reductive Kottwitz construction.
