# Reversed-Levi Jacquet compatibility of the actual Aubert operator

Author: Worker 320.

`Langlands.Aubert.JacquetCompatibilityStatement.{uF,uV} F T` is a
proposition definition asserting, for every natural rank `n` and every actual
ordered positive block shape `B` of that rank,

```text
Jac_B ∘ D_n = transport_(B.reverse → B) ∘ D_(B.reverse) ∘ Jac_(B.reverse).
```

Here `D_n` is the existing `alternatingOperator F T n`, `D_(B.reverse)`
is `alternatingOperatorOnLevi F T B.reverse`, and `Jac` is the actual
`normalizedJacquetK0`. The transport is exactly
`leviTransportK0 F.Carrier B.reverse B B.reversePermutation` with the concrete
conjugacy witness proved in this module. This module supplies no proof of the
Jacquet compatibility equality.

## Concrete reversal and direction

The existing `B.reverse` reverses the ordered list of block sizes.
The existing permutation is characterized by

```text
B.reversePermutation (B.reverse.index i a) = B.index i.rev a.
```

Thus it sends reversed-shape coordinates to original-shape coordinates and
keeps the order inside each block. The small derived theorem
`Langlands.CuspidalSupport.conjugatesLevi_reversePermutation` proves that this
permutation conjugates the actual embedded Levi of `B.reverse` onto that of
`B`, over any field and at every rank. It applies the published criterion
`conjugatesLevi_of_blockIndex`: a reversed source block label `i` becomes the
original label `i.rev`, and reversal is injective. The coordinate identity
above and `blockIndex_index` verify the criterion. This is an internal
consequence of existing matrix/block definitions; no extra group conjugacy
assumption is inserted into the proposition.

The existing transport on representations is inverse conjugation: if `A` is
a representation of the reversed Levi, its transport acts on `m` in the original
Levi by `A(w⁻¹ m w)`, using the actual Levi embeddings. Its exact K0 map has
the forward direction from the reversed Levi group to the original Levi group.
The displayed statement uses `w = B.reversePermutation`, not its inverse.
For example, for `B = (1,2)` its images on `0,1,2` are `1,2,0`; the inverse
has images `2,0,1`. This example explains the direction and is derived from
the coordinate formula, not asserted as an extra Lean theorem.

## Original source and type-A translation

Source: Anne-Marie Aubert, *Dualité dans le groupe de Grothendieck de la
catégorie des représentations lisses de longueur finie d'un groupe réductif
p-adique*, Transactions of the American Mathematical Society 347 (1995),
2179–2189. Registered literature ID: `aubert-1995-duality`. PDF SHA-256:
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.

The exact source assertion is Theorem 1.7(2), second equality, printed p.2181
(one-based PDF p.3): Jacquet restriction after `D_G` equals `Ad(w_J)` after
the Levi operator and restriction to `L_(J')`. The notation on printed p.2180
(PDF p.2) defines `J' = w_J⁻¹(J)` and characterizes `w_J` by sending the
inverse images of `J` to positive roots and of its complement to negative
roots. Those two pages were read as text and rendered images for this module.
The proof passage on printed pp.2182–2183 (PDF pp.4–5) was read as text, and
p.2183 was also checked as an image.

For upper standard parabolics of `GL_n`, `J` is the set of adjacent simple
roots inside the blocks of `B`. The stated root-sign conditions give exactly
the block-order reversal that preserves order within each block, namely
`B.reversePermutation`; the inverse image `J'` is the set of roots inside
`B.reverse`. The source's `Ad(w_J)` therefore has the concrete inverse-action
transport just described. This is the derived type-A dictionary. It agrees
with the distinguished permutation in the separately published
`Geometric.PointwiseJacquetCoefficientStatement`, but neither that proposition
nor its coefficient proof is assumed by this statement module.

Definition 1.5 on printed p.2181 uses the unadjusted sign `(-1)^|I|`.
For a shape `C` the corresponding root subset has cardinality `n - C.length`.
Within a product Levi the exponent is
`sum i, (B.size i - (S i).length)` for a refinement `S`.
These are exactly the imported ambient and product-Levi operators. No
cuspidal-support-dependent sign adjustment, smooth contragredient or
unrecorded change to an opposite parabolic occurs in the proposition.

## Objects, universes and scope

The outer parameters are arbitrary `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and supplied `T : F.TopologicalData`. The proposition
installs the supplied topology, valuation and local-field structure to form
the existing continuous Levi transport. Universes `uF` and `uV` remain
independent and representation carriers are in `Type (max uF uV)`.
Both sides are integer-linear maps from the exact finite-length smooth complex
Grothendieck group of actual `GL_n(F)` to that of the actual product Levi
`B.Levi F.Carrier`. These quotients impose relations from all actual short
exact sequences, including nonsplit ones; no finite vector-space dimension
is required.

Jacquet restriction is the actual upper-unipotent coinvariant functor with
inverse half-modulus action. The alternating operators use actual normalized
upper-block parabolic induction with positive half-modulus covariance and
right translation, together with actual normalized Jacquet/refined functors.
The product-Levi operator acts on the group of the actual product and is not
identified with the group of an ambient general linear group.

Every natural `n` is included. At zero the block shape is empty, the permutation
is unique, and both signs are `1`; proving the identity for the actual trivial
group functors remains an obligation. There is no positive-rank,
admissibility, irreducibility, cuspidality, central-character, preservation or
other theorem-valued premise.

## Remaining proof and independence

The source proof expands the actual geometric Jacquet-induction formula,
uses restriction transitivity, cancels the fixed-permutation coefficients,
and identifies the surviving reversed-Levi term. These are proof obligations,
not consequences of the proposition definition. A coefficient identity alone
does not supply the actual-map comparisons. The module proves only the small
concrete conjugacy witness; it proves no formal Aubert identity, irreducible
image or analytic classification theorem.

The direct imports are the published `Aubert.AlternatingOperator`,
`Aubert.RefinedAlternatingOperator`, `CuspidalSupport.LeviGrothendieckTransport`
and `Group.GL.ReverseBlocks`.
All existing definition and statement pairs remain unchanged. The upstream
independence restrictions in
[`notes/henniart/aubert-duality-route.md`](../../../notes/henniart/aubert-duality-route.md)
remain: a future proof must avoid the analytic segment classification,
multisegment exhaustion, ordered strong-head existence, quotient coverage,
tempered block uniqueness, square-integrable Langlands classification or
exhaustion, regular exhaustion, and their proof successors and transitive
proof inputs. Formal identities do not resolve the separate corrected
irreducibility-complex obligations.
