# Concrete Cartan cells modulo the center

Author: Worker 292.

This pair constructs the integer chamber, actual diagonal matrices, subsets of
the actual central quotient, and radial weights used by later analytic
statements. Its namespace is `Langlands.GeneralLinear.CartanQuotient`.
It supplies the two definitional membership equivalences. Covering,
disjointness, scalar-shift laws, positivity, and agreement with the Borel
modulus are separate algebraic proof targets; none is stored as assumed data.

## Objects and exact scope

Let `p` be prime, `F : PadicField.{uF} p`, `T : F.TopologicalData`, and `n : ℕ`.
There is no representation carrier or representation-theoretic hypothesis.
All definitions allow rank zero, but `NormalizedTuple 0` is empty because the
normalization requires a coordinate attaining zero. Subsequent normalized
covering statements therefore require `0 < n`.

* `Normalized lam : Prop` means that `lam : Fin n → ℤ` is antitone, every
  coordinate is nonnegative, and some coordinate is zero.
  `NormalizedTuple n` is the subtype of these functions. It adds only this
  proposition; no covering or uniqueness assertion is a field. As a subtype
  of a finite product of integers, its carrier has the inherited `Countable`
  instance.
* `shift lam c` is `fun i => lam i + c`.
* `maximalCompact T n` is exactly
  `Iwasawa.integralRange T.discreteValuation n`, the image of the integral
  general linear group. This pair neither constructs a replacement compact
  group nor proves its topological compactness or maximality.
* `representative T lam` is exactly
  `Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit T) lam`.
  The underlying matrix is diagonal with entries `uniformizer ^ lam i`.
* `centralQuotient F n` is definitionally
  `GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`;
  `quotientMap F n` is its quotient homomorphism. Thus a consumer installing
  `T.topology` uses the existing quotient topology and Borel-Haar APIs directly,
  without transporting to a new abstract group or installing another topology.
  Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar` identifies this
  center with the full scalar subgroup.
* `subgroupCell T H lam` consists of all
  `quotientMap F n (h₁ * representative T lam * h₂)` with `h₁,h₂ ∈ H`.
  The definition is available for every subgroup `H`; it specializes without
  extra data to any `H ≤ maximalCompact T n`. Containment in a `K` cell will
  use that subgroup inclusion as an explicit hypothesis.
* `cell T lam` is `subgroupCell T (maximalCompact T n) lam`.
  `compactImage T n` is the actual subgroup image of `maximalCompact T n`
  under `quotientMap F n`. The name does not add a compactness certificate.
* `degree lam : ℤ` is the double finite sum
  `∑ i, ∑ j ∈ univ.filter (i < ·), (lam i - lam j)`.
  `delta T lam : ℝ` is `(T.residueCardinality : ℝ) ^ (-degree lam)`, with
  integer exponentiation. `height lam : ℝ` is `1 + ∑ i, |lam i|`, with the
  integer absolute values coerced to real numbers.
* `representativeLevi T lam` is the family of actual `1 × 1` scalar blocks
  `BlockShape.singletonLevi F.Carrier (fun i => uniformizerUnit T ^ lam i)`.
  `representativeBorel T lam` is its image under the published singleton
  `leviInParabolic` map. These expose the existing upper-Borel modulus API;
  their matrix identification and the equality with `delta` are separate laws.

Theorems `mem_subgroupCell` and `mem_cell` restate the two set definitions by
reflexivity. No other construction law is claimed as proved in this pair.

## Chamber, central normalization, and sign

For positive rank, an antitone tuple has its minimum at the last coordinate.
Thus nonnegative coordinates together with an attained zero are equivalent to
last-coordinate zero. Given any decreasing tuple, subtracting its last
coordinate produces this normalized tuple. Common translation by an integer
`c` multiplies the diagonal matrix by the scalar `uniformizer ^ c`; its class
in the central quotient is unchanged. Conversely, a nonzero scalar is a power
of the uniformizer times a valuation-one scalar, whose matrix lies in the
integral group. Together with the published unique Cartan exponents, this is
the algebraic route to normalized central double-coset coverage and uniqueness.
These sentences explain the normalization; they do not supply formal proofs
of those remaining targets.

The chosen uniformizer has normalized absolute value `q⁻¹`, where
`q = T.residueCardinality > 1`. The imported theorem
`LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs` gives diagonal absolute
values `q^(-lam i)`. Hence `Antitone lam` corresponds to **monotone** diagonal
absolute values. For the upper Borel the positive roots are `e_i-e_j` with
`i<j`, so their absolute values are `q^(-(lam i-lam j))`. Their product is
`q^(-degree lam)`. This is the full upper modulus, not its inverse or square
root. The published `T.leviModulus_singletonLevi` gives exactly the product of
these root quotients, and `glBlockModulusHaar` provides its Haar-scaling
interpretation. The new pair claims neither that interpretation anew nor a
volume estimate.

`degree` and `delta` are designed to be invariant under common integer
translation. `height` is a chosen coordinate weight on normalized tuples; it
is not asserted invariant before normalization. In rank one the normalized
tuple is zero, and the intended weights are degree zero, delta one, and height
one. The corresponding formal laws are separate proof targets.

## Provenance and boundaries

Original source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.
Source ID `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Retained original:
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
Read PDF pages 4–8, printed pages 238–242. No matching errata note was located
in the project's public or project notes.

In I.1, printed p.239 defines the closed positive chamber by nonnegative simple
roots. Printed p.240 defines `H_G` using `q^(-<chi,H_G(g)>) = |chi(g)|`, making
the decreasing integer convention agree with this chamber. The same page
chooses the standard kind of maximal compact subgroup. Equation (4), p.241,
states the disjoint Cartan covering by `K m K`. Equation (5), pp.241–242,
relates cell volumes to the inverse modulus; this explains the orientation
needed by consumers, but no volume bound is included here.

The concrete finite integer coordinates for `GL_n`, their normalization by a
common scalar shift, the quotient-image subsets, and the finite root sum are
**derived specializations**, rather than definitions quoted verbatim from
Waldspurger. The root calculation above explains the specialization. The
particular height `1 + ∑ |lam i|` is an internal coordinate weight. It is not
Waldspurger's `1 + sigma(g)` from p.242, and no comparison with that function is
claimed. Analytic summability, topology, Haar-volume estimates, coefficient
bounds, and temperedness belong to subsequent tasks.
