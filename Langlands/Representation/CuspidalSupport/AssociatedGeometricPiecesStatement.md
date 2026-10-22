# Individual geometric pieces for associated Levis

Author: Worker 178.

This pair states the reduction of the individual geometric pieces used in
Bernstein–Zelevinsky (1977), Corollary 2.13(c), for actual general linear
groups over finite p-adic extensions. Its four declarations are Prop-valued
definitions. It supplies no proof of the reduction or the geometric lemma.

## Scope and component propositions

`Langlands.CuspidalSupport.PadicAssociatedGeometricPiecesTheorem` quantifies
every prime `p`, actual `F : PadicField.{uF} p`, compatible topological data
`T : F.TopologicalData`, and positive rank `n`. It conjoins three component
propositions, each with parameters `F T n`. All smooth representation
categories use `T.topology`. Field universe `uF` and input-carrier universe
`uV` are independent.

The first two components quantify ordered positive block shapes
`B C : BlockShape n`, an arbitrary
`ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)`, its
`IsLeviQuasicuspidal B ρ.representation` hypothesis, and
`LevisAssociated (F := F.Carrier) B C`. For every
`w : MinimalRepresentatives B C`, they quantify every pair of actual
refinements `S : BlockRefinement B`, `R : BlockRefinement C` with

```text
hS : IsIntersectionRefinement B C w.val S
hR : IsIntersectionRefinement C B w.val⁻¹ R.
```

Here the implicit field in both predicates is `F.Carrier`. The predicates
give equalities of the actual parabolic, Levi, and unipotent intersection
subgroups with their refinement subgroups. The resulting piece is exactly

```text
(geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1).obj ρ.
```

The two projections select the existing Levi subgroup equalities used to
type the composite. These structural equalities do not supply a
representation equivalence or assume a geometric lemma.

- `AssociatedGeometricPieceVanishingTheorem` asserts that this piece has a
  `Subsingleton` carrier when `w.val` does not conjugate the whole source
  Levi onto the whole target Levi.
- `AssociatedGeometricPieceEquivalenceTheorem` asserts, for every
  `hw : ConjugatesLevi B C w.val`, a `Nonempty` actual `Representation.Equiv`
  from this piece's representation to
  `transport B C w.val hw ρ.representation`. The piece's carrier is in
  universe `max uF uV`; the transported carrier remains in `uV`.
- `MinimalWeylTransportQuasicuspidalTheorem` quantifies the same smooth
  quasicuspidal input and every minimal representative with such an `hw`,
  and asserts `IsLeviQuasicuspidal C` of the transported representation.
  It has no refinement, intersection-equality, or geometric-piece
  parameters. A separate association hypothesis is unnecessary here
  because `hw` already witnesses association.

The component definitions themselves are meaningful at any rank; the
aggregate asserts them only for positive rank. There are no irreducibility,
admissibility, finite length, finite dimension, or nonzero-input assumptions.
The zero input is included. No filtration, splitting, natural equivalence,
or choice of an equivalence is assumed. The equivalence component asserts
existence at each input representation, rather than a natural isomorphism
of functors.

## Original source and derived GL reduction

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472, literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Sections 2.11–2.12, printed page 448 / PDF page 9, give the minimal
representatives, standard intersections, and individual functors
`i_{N,N'} ∘ w ∘ r_{M',M}`. Corollary 2.13(c) and its complete proof,
printed page 449 / PDF page 10, use quasicuspidality to remove proper
source intersections and identify the remaining conjugating representatives.
Those pages were read directly, together with section 1.7 (printed
page 443 / PDF page 4), sections 2.1–2.4 (printed page 446 / PDF page 7),
and sections 2.6–2.7 (printed page 447 / PDF page 8).

This pair isolates the individual-piece and transport assertions implicit
in that argument. It does not restate the full filtration or the Weyl-coset
bijection. The GL-specific reasoning needed for a future proof is as follows.

1. Write `M = B.Levi F.Carrier`, `N = C.Levi F.Carrier`,
   `M' = M ∩ w⁻¹(N)` and `N' = w(M) ∩ N`, with the intersections expressed
   in the Library's actual product coordinates. The refinement equalities
   identify the parabolic triples, as in BZ77 2.11–2.12. If the source
   refined parabolic is proper, quasicuspidality gives zero raw
   coinvariants. The normalized refined Jacquet functor has exactly the
   same quotient carrier, so its value is also zero. Equality relabeling,
   inverse-conjugation transport, and induction then preserve this zero
   carrier.
2. If the source refinement is full, the source intersection Levi is all
   of `M`, so `w(M)` is contained in `N`. Association forces equality in
   this setting. Concretely, a permutation conjugating block Levis is
   governed by their coordinate-block partitions. Containment makes the
   transported source partition refine the target partition, while
   association gives the same multiset of positive block sizes (BZ77
   2.7), hence the same number of blocks. A refinement with that block
   count is equality. Thus the target intersection is also full. This
   rules out a full source refinement for a nonconjugating representative
   and gives the first component.
3. If `hw` holds, both intersection Levis and their refined parabolics are
   full. Their radicals are trivial and their explicit positive moduli
   are one. Jacquet by the trivial radical is equivalent to the original
   representation, and induction from the full group is equivalent to
   the inducing representation by evaluation at the identity. Under the
   actual subgroup identifications, `intersectionTransport` agrees with
   `transport`: both actions use inverse permutation-matrix conjugation,
   as in BZ77 1.7. These identifications give the second component without
   an extra character.
4. A minimal permutation conjugating the whole Levis permutes their
   blocks while preserving the order inside each block. It therefore
   carries proper standard refinements and their unipotent radicals
   between the two product Levis. The corresponding coinvariant
   quotients of the transported and original actions are equivalent.
   Their vanishing proves the third component, using the definition
   of quasicuspidality from BZ77 2.4. This is the GL-specific transport
   invariance behind the quasicuspidality assertion of 2.13(c).

These are explanations of provenance and future proof obligations.
This statement pair establishes none of the partition geometry,
full-refinement identifications, modulus simplifications, zero-preservation
or representation equivalences described above. In particular the
intersection equalities in its hypotheses identify existing groups;
they do not encode those further conclusions.

The pair imports the published `CuspidalSupport.LeviDefinitions` and
`Geometric.GeometricLemmaStatement`, reusing `RefinementFunctors` and
`IntersectionTransport` through the latter. Merely importing a proposition
definition does not assume its truth: neither `GeometricLemmaTheorem` nor
`PadicGeometricLemmaTheorem` is a hypothesis. Constructing the refinements
and a natural filtration belongs to the geometric-lemma proof; identifying
minimal conjugating representatives with right source-Weyl cosets is a
separate statement and proof obligation. Passing from these individual
pieces to the associated Jacquet filtration, including its rank-zero case
and quasicuspidality under finite extensions, belongs to the consumer.
