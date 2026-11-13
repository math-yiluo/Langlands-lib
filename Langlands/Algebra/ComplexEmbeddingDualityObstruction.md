# Complex self-embeddings and restriction modules

Module `Langlands.Algebra.ComplexEmbeddingDualityObstruction`, with the
same namespace. Worker 1222 constructed this internal algebraic input for
the coefficient audit of Renard I.4.2. It is not a statement of Renard's
theorem or an identification of his functors.

The source motivation is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, I.4.2, Theorem,
printed pp.23–24 / PDF pp.29–30. The existing
[coefficient audit](../../notes/renard/duality-coefficient-conventions.md)
distinguishes the common-coefficient theorem from its bare additive
ring-bimodule interpretation. This module develops a possible input to
that audit; the construction and proofs here are derived mathematics,
rather than claims in the book.

## Construction and intrinsic laws

For any unital ring endomorphism `σ : ℂ →+* ℂ`, `Carrier σ` is a distinct
copy `ULift ℂ` of the ordinary complex field. Its field structure is the
usual one. The ring equivalence `carrierRingEquiv σ` forgets the lift.
The complex algebra structure is specified separately by the algebra map
`c ↦ σ(c)`, transported through this ring equivalence. Thus
`carrier_smul` states exactly

```text
carrierRingEquiv σ (c • z) = σ(c) * carrierRingEquiv σ z.
```

The parameter keeps the selected algebra structure attached to this
carrier. The codomain of `Module.Dual ℂ (Carrier σ)` is the ordinary
complex field with its ordinary complex coefficients. Twisting the source
does not twist that codomain.

The following intrinsic facts are proved.

| Declaration | Content and hypotheses |
| --- | --- |
| `exists_nonsurjective_endomorphism` | There exists a unital complex field endomorphism that is not surjective. No endomorphism-existence hypothesis is assumed. |
| `carrier_algebraMap`, `carrier_smul` | The selected algebra map and scalar action have the formulas above, for every `σ`. |
| `not_finite σ hσ` | If `σ` is not surjective, its restriction module `Carrier σ` is not finite-dimensional over `ℂ`. |
| `rank_lt_dual σ hσ` | Under the same hypothesis, its complex dimension is strictly smaller than that of its full algebraic complex dual. |
| `no_linearEquiv_dual σ hσ` | There is no complex-linear equivalence from the restriction module to that dual. This rules out every such equivalence, with no prescribed formula. |

All carriers here are in `Type 0`; no topology, continuity, conjugate
linearity or restricted dual is imposed.

## Implemented argument

Let `K` be the fraction field of `ℂ[X]` and `L` its algebraic closure.
Polynomial, fraction-field and algebraic-extension cardinality theorems
give `#L = #ℂ`. The inclusion of `ℂ` into `L` misses the polynomial
variable: transcendence of `X` persists through both injective algebra
maps, whereas every scalar image is algebraic.

Mathlib's classification of uncountable algebraically closed fields of
characteristic zero gives an abstract field equivalence `L ≃+* ℂ`.
Composing with the inclusion gives the required `σ`. This equivalence is
an abstract field equivalence, not an equivalence of complex algebras.

If `Carrier σ` were finite-dimensional, its field extension of `ℂ` would
be integral. Since the base field is algebraically closed, its algebra
map would be surjective. Transport through `carrierRingEquiv σ` would
make `σ` surjective, a contradiction.

The failure of finite-dimensionality implies that its dimension is at
least `ℵ₀`, using `Module.rank_lt_aleph0_iff`. Mathlib's
`Cardinal.rank_lt_rank_dual`, proved by the Erdős–Kaplansky and Cantor
argument, then gives the strict dimension inequality. A linear
equivalence would give equality of ranks and contradict that inequality.

## Reuse and remaining source obligation

The implementation reuses Mathlib's complex-field algebraic closedness,
cardinality results, algebraic closure, field classification, finite
extension integrality and dual-dimension theorem. Its only project input
is the approved Lean environment.

To turn this construction into a formal counterexample to the bare
additive reading of I.4.2, one must still instantiate the published
original-action tensor, Hom, nondegenerate-part and dual constructions,
identify their actual recovered coefficient modules with the carriers
above, and transport a proposed original module isomorphism to a
complex-linear equivalence. Those identifications are not supplied here.
The common-coefficient statements and their proof obligations remain
separate, and this unit does not close I.4.2 or Chapter I.
