# Rational-to-prime maps on actual roots-of-unity twists

This module constructs the canonical rational-linear maps from the full,
away, or selected rational roots-of-unity limits to a prime-adic rational
twist. Let `R` be any commutative ring and `p : ℕ` a prime, with primality
expressed by `[Fact p.Prime]`. For `P : ℕ → Prop` and
`hP : ∀ n : ℕ, P (p ^ n)`, the map is

\[
\mathbb Q\otimes_{\mathbb Z} T_P(1)
 \longrightarrow
\mathbb Q_p\otimes_{\mathbb Z_p} T_p(1),
\qquad q\otimes x\longmapsto q\otimes\operatorname{toPrime}(x).
\]

Here \(T_P(1)\) denotes the existing `Divisibility.Integral R P` of
coherent actual roots of unity at selected positive moduli, and \(T_p(1)\)
denotes `TateTwist.Integral R p`. The scalar \(q\) on the right is mapped
by the canonical rational cast into \(\mathbb Q_p\). The two tensor
products have different base rings, exactly as displayed.

## The prime-adic rational target

In namespace `Langlands.TateTwist`, `Rational R p` is the existing type
\(\mathbb Q_p\otimes_{\mathbb Z_p}\operatorname{Integral}(R,p)\).
Its existing additive group and \(\mathbb Q_p\)-module structures are
retained. The instances `rationalRatModule` and `rationalPadicIntModule`
expose the standard tensor-product actions of \(\mathbb Q\) and
\(\mathbb Z_p\), respectively. The instances `rationalRatScalarTower`
and `rationalPadicIntScalarTower` express compatibility of each of
these actions with the existing \(\mathbb Q_p\)-action. All four are
inherited directly from the underlying tensor product.

`TateTwist.toRational R p` is the \(\mathbb Z_p\)-linear map
\(x\mapsto 1\otimes x\). `toRational_apply` gives this formula by
reflexivity. No injectivity is asserted.

## Rational extraction and its normalization

The remaining declarations are in
`Langlands.TateTwist.Divisibility`. `rationalToPrime R P p hP`
is a \(\mathbb Q\)-linear map into `TateTwist.Rational R p`.
First compose the existing additive extraction map `toPrime R P p hP`
with `TateTwist.toRational R p`, viewed as an integer-linear map.
For each \(q\in\mathbb Q\), multiply this map by \(q\).
This gives a map linear in \(q\) over \(\mathbb Q\) and linear in the
root family over \(\mathbb Z\).
`TensorProduct.AlgebraTensorModule.lift` supplies the desired map.
Thus the construction uses the tensor universal property; it does not
assume any full-to-local comparison isomorphism.

`rationalToPrime_tmul` proves the displayed pure-tensor formula. The
implemented proof unfolds the lift on a pure tensor, moves rational
scalar multiplication into the first tensor factor, and simplifies
the scalar multiple of \(1\) to the rational cast in \(\mathbb Q_p\).

`rationalToPrime_unique` says that any \(\mathbb Q\)-linear map with
this formula on every pure tensor equals `rationalToPrime`. Its proof
uses tensor extensionality and the two pure-tensor formulas.

`rationalToPrime_toRational` states that the canonical map from the
integral selected twist commutes with extraction and the canonical
map into the local rational twist. It is the pure-tensor formula at
\(q=1\).

## Full and away maps

`rationalFullToPrime R p` specializes the construction to the full
index predicate. `rationalFullToPrime_tmul` identifies its value at
\(q\otimes x\) with \(q\otimes\operatorname{fullToPrime}(x)\).

For any excluded modulus `m : ℕ` and witness
`h : Nat.Coprime p m`, `rationalAwayToPrime R p m h` specializes to
indices coprime to \(m\). The witness `h.pow_left n` ensures that
each \(p^n\) is selected. `rationalAwayToPrime_tmul` gives the
corresponding formula with `awayToPrime R p m h`.

The equality of \(\mathbb Q\)-linear maps
`rationalAwayToPrime_restrictAway` says that rational restriction
from the full twist to the away twist, followed by away extraction,
equals full extraction. The proof uses tensor extensionality, the
pure-tensor formulas, and the imported integral identity
`awayToPrime_restrictAway`.

## Naturality

For any commutative ring `S` and ring homomorphism `f : R →+* S`,
`rationalToPrime_map` states

\[
r_{S,P,p}\circ \operatorname{rationalMap}_{P}(f)
 =
\operatorname{rationalMap}_{p}(f)\circ r_{R,P,p}.
\]

On the right, the prime-adic rational map is restricted from
\(\mathbb Q_p\)-linearity to \(\mathbb Q\)-linearity. The target
scalar-tower instance makes that restriction available. The proof
checks pure tensors, applies the existing formulas for both
rational maps, and uses the integral naturality law `toPrime_map`.
This formula applies in particular to ring automorphisms and to
the full and away specializations.

## Provenance and scope

This is an internal construction from the published `TwistRational`
and `TwistPrimeComparison` modules and Mathlib's tensor-product
universal property in `LinearAlgebra.TensorProduct.Tower`.
The construction and implemented proofs are described above; no
new claim is attributed to original literature.

There are no hypotheses on characteristic, rank, finiteness, or the
existence of primitive roots. No topology is placed on the rational
source or target by this module, and no continuity is asserted.
The maps are not asserted to be injective, surjective, or comparison
isomorphisms. A restricted-product comparison and compatibility
with rational profinite or finite-adele scalars remain separate
obligations. No roots-of-unity basis or trivialization is chosen.
