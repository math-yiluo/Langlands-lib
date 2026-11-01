# Commutation of the actual Aubert operator with normalized induction

Author: Worker 320.

This module defines the proposition
`Langlands.Aubert.InductionCommutationStatement.{uF,uV} F T`.
For every natural rank `n` and every ordered positive block shape `B` of
that rank, it asserts the equality of integer-linear maps

```text
(alternatingOperator F T n).comp (normalizedInductionK0 F T B)
  =
(normalizedInductionK0 F T B).comp (alternatingOperatorOnLevi F T B).
```

Thus normalized induction from the actual product Levi `B.Levi F.Carrier`
to `GL_n(F)` intertwines the two unadjusted alternating operators. This
statement module supplies no proof of the equality.

## Exact objects, maps and scope

The source of both composites is
`B.FiniteLengthGrothendieckGroup.{uV,uF} F.Carrier`, and their target is
`GeneralLinear.FiniteLengthGrothendieckGroup.{uV,uF} n F.Carrier`. These are
the exact Grothendieck groups of actual smooth complex representations
with finite group-algebra length. Their relations come from all actual
short exact sequences, including nonsplit sequences. They are not the
finite-dimensional split representation groups.

The imported `Parabolic.normalizedInductionK0` is induced by the actual
normalized upper block parabolic induction functor. Its finite-length
preservation and exactness have already been proved. Its function-space
model uses positive half-modulus covariance and right translation.

The ambient operator sums induction after Jacquet restriction over all
ordered positive block shapes `C` of rank `n`, with integer coefficient
`(-1)^(n - C.length)`. The product-Levi operator sums the actual refined
induction-after-Jacquet composites over all `S : Geometric.BlockRefinement B`,
with coefficient

```text
(-1)^(sum i, B.size i - (S i).length).
```

The subtraction is inside the summand. The published
`refinementSignExponent_eq` identifies its exponent with
`n - sum i, (S i).length`. These are the unadjusted operators; no
cuspidal-support-dependent sign is inserted. Refined induction and
Jacquet restriction use actual subgroups and their actual normalized
functors, without identifying the product-Levi group with an ambient
general linear group.

The proposition has only the outer parameters `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and supplied `T : F.TopologicalData`. The two
universe levels are independent, and all representation carriers are
saturated at `Type (max uF uV)`. It quantifies every `n`, including zero,
and every block shape. There is no positivity, admissibility,
irreducibility, central-character or additional theorem-valued premise.
Rank zero is the corresponding identity for the trivial rank-zero group
and its empty product Levi; its proof remains part of this proposition.

## Original source and translation

Source: Anne-Marie Aubert, *Dualité dans le groupe de Grothendieck des
représentations lisses de longueur finie d'un groupe réductif p-adique*,
Transactions of the American Mathematical Society 347 (1995), 2179–2189.
Registered source ID: `aubert-1995-duality`.
SHA-256:
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.

Theorem 1.7(2), first equality, printed p.2181 (one-based PDF p.3),
asserts `D_G` composed with normalized induction equals normalized
induction composed with `D_L`. Definition 1.5 on the same page uses
the sign `(-1)^|I|` for the standard Levi indexed by a subset `I` of
the simple roots. For `GL_n`, that subset has size `n - C.length`.
Inside the product Levi of `B`, its size is the sum over blocks of
`B.size i - (S i).length`. This gives precisely the two imported signs.
The statement is for the actual product Levi and does not require a
tensor-product realization of its Grothendieck group.

The proof on printed pp.2181–2182 uses the geometric lemma, induction
transitivity, whole-Levi conjugacy (1.2), and the total Solomon
coefficient identity. That is the source's proof route, not a proof
implemented by this module. The project must use independently proved
inputs along that route. In particular, the classification dependency
in a later proof of whole-Levi conjugacy cannot be imported silently.
The relevant source boundaries and corrections are recorded in
[`notes/henniart/aubert-duality-route.md`](../../../notes/henniart/aubert-duality-route.md).

The all-rank formulation includes the elementary rank-zero specialization;
this extension adds no theorem assumption and leaves a real proof
obligation. No irreducible-image theorem, involutivity, twisted Jacquet
compatibility or analytic segment classification follows merely from
this proposition definition.
