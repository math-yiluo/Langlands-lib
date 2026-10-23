# Rational prime coordinates of actual Tate modules

Let `S` be a scheme, `G : Grp (Over S)` a commutative group scheme,
and `T : Over S` a test scheme. Let `p : ℕ` be prime, expressed by
`[Fact p.Prime]`. This module constructs canonical rational-linear
maps from the actual selected, full and away torsion limits to the
existing rational prime-adic Tate module. It specializes these maps
to bundled abelian schemes without replacing their torsion sections
by arbitrary modules.

## Carriers and the local rationalization map

In `Langlands.GroupScheme.Tate`, the published `Integral G T P` is the
coherent-family limit of the actual multiplication-kernel sections at
positive orders satisfying `P : ℕ → Prop`. The transition from order
`M` to a divisor `N` is multiplication by `M / N`. Its rationalization is
`Rational G T P = ℚ ⊗[ℤ] Integral G T P`.

The published `PrimeAdic.Integral G T p` uses orders `p ^ n` for all
natural exponents, including zero, and transition multiplication by
`p`. Its rationalization is

\[
V_p(G,T)=\mathbb Q_p\otimes_{\mathbb Z_p}T_p(G,T).
\]

In namespace `Langlands.GroupScheme.Tate.PrimeAdic`, the instances
`rationalRatModule`, `rationalPadicIntModule`,
`rationalRatScalarTower` and `rationalPadicIntScalarTower` expose the
standard actions of `ℚ` and `ℤ_[p]` on this tensor product and their
compatibility with the existing `ℚ_[p]` action. Each is inherited
directly from the underlying tensor product.

`PrimeAdic.toRational G T p` is the `ℤ_[p]`-linear map
\(x\mapsto 1\otimes x\); `toRational_apply` gives this formula by
reflexivity. No injectivity is asserted here.

## Selected rational extraction

In `Langlands.GroupScheme.Tate.PrimeComparison`, assume
`hP : ∀ n : ℕ, P (p ^ n)`. The construction
`rationalToPrime G T P p hP` is a `ℚ`-linear map

\[
\mathbb Q\otimes_{\mathbb Z}T_P(G,T)
 \longrightarrow \mathbb Q_p\otimes_{\mathbb Z_p}T_p(G,T),
\qquad q\otimes x\longmapsto
 \iota_p(q)\otimes\operatorname{toPrime}(x),
\]

where \(\iota_p\) is the canonical rational cast into \(\mathbb Q_p\).
The target is viewed as a rational vector space through the instance
above. The two displayed tensor products have different base rings.

The implementation composes the published additive coordinate map
`toPrime` with `PrimeAdic.toRational`, viewing both as integer-linear
maps. Multiplying this composite by each rational `q` produces the
bilinear input to `TensorProduct.AlgebraTensorModule.lift`.
Thus the construction uses a tensor universal property, with no
comparison isomorphism hypothesis.

`rationalToPrime_tmul` proves the displayed formula by evaluating the
lift on a pure tensor, moving the rational scalar to the first tensor
factor and simplifying its product with one.
`rationalToPrime_unique` proves that any rational-linear map satisfying
this formula on all pure tensors equals the constructed map. Its
proof uses tensor extensionality.

`rationalToPrime_toRational` identifies extraction after the global
canonical map \(x\mapsto1\otimes x\) with the local canonical map
after integral extraction. It is the pure-tensor formula at `q = 1`.

## Full, away and restriction maps

`rationalFullToPrime G T p` specializes `P` to the always-true
predicate. `rationalFullToPrime_tmul` gives its formula using the
published `fullToPrime`.

For any excluded modulus `m : ℕ` and `h : Nat.Coprime p m`,
`rationalAwayToPrime G T p m h` specializes to orders coprime to
`m`. The proof `h.pow_left n` ensures every `p ^ n` is selected.
`rationalAwayToPrime_tmul` gives its formula using `awayToPrime`.
For positive `m`, the retained primes are those not dividing `m`;
`m = 1` retains every prime, and `m = 0` admits no prime with the
required coprimality witness.

`rationalAwayToPrime_restrictAway` is equality of rational-linear maps:
rational restriction from the full limit to the away limit, followed
by extraction at a retained prime, equals full extraction. The proof
checks pure tensors and applies the existing integral restriction
identity `awayToPrime_restrictAway`.

## Naturality and actual abelian schemes

For another commutative group scheme `H` and an actual group-scheme
homomorphism `f : G ⟶ H`, `rationalToPrime_map` proves

\[
r_{H,P,p}\circ\operatorname{rationalMap}_P(f)
 =\operatorname{rationalMap}_p(f)\circ r_{G,P,p}.
\]

The local rational map on the right is restricted from
`ℚ_[p]`-linearity to `ℚ`-linearity using the inherited scalar tower.
The proof applies tensor extensionality, the pure-tensor formulas for
both induced maps, and the integral identity `toPrime_map`.
This gives full and away naturality by specialization.

`Langlands.AbelianScheme.Tate.PrimeAdic.toRational` and the three
`Langlands.AbelianScheme.Tate.PrimeComparison` abbreviations
`rationalToPrime`, `rationalFullToPrime`, and `rationalAwayToPrime`
apply these constructions to `A.toGrp` for an actual bundled abelian
scheme `A`. The abelian-scheme `rationalToPrime_map` theorem applies
the group-scheme result to `AbelianScheme.groupHom f`. At a geometric
point, take `T = Over.mk s`, as in the published Tate constructions.

## Provenance and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Chapter I, printed p.18 (PDF p.26), defines the
full and away Tate modules and their rationalizations over the
integers. Chapter III, printed p.91 (PDF p.99), uses the full rational
Tate module in the characteristic-zero PEL level condition. The
registered source is `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The imported `rationalTensorComm` accounts for the opposite order of
tensor factors in the source's notation.

The coordinate maps and their formulas are derived infrastructure
from the published `Rational` and `PrimeComparison` modules and
Mathlib's tensor universal property. The arbitrary commutative
group scheme, test scheme and selected predicate are explicit
generalizations. Worker 142 adapted Worker 92's root-twist tensor-lift
construction to these actual group-scheme carriers; no identification
with a root twist is used or asserted.

This unit assumes no characteristic, finiteness, rank or product
comparison hypothesis. It asserts no injectivity, surjectivity,
restricted-product equivalence, rational topology or continuity.
Compatibility with rational profinite or finite-adele scalars,
geometric monodromy and Weil pairings remain separate obligations.
