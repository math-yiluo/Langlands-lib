# Renard A.IX: disjointness of the actual full supported sums

Authors: Workers 709 and 1006.

This module proves the unchanged published proposition
`Langlands.Renard.SimpleSupportSumOrthogonalityStatement` from
`Langlands.CategoryTheory.Renard.SimpleSupportSumOrthogonalityStatements`.
Its exported theorem has the complete unapplied type

```lean
Langlands.Renard.simpleSupportSumOrthogonality.{w, v, u} :
  (C : Type u) → [Category.{v} C] → [Abelian C] →
    Langlands.Renard.SimpleSupportSumOrthogonalityStatement.{w} C
```

The conclusion concerns the actual full supported-subobject sums:

```lean
simpleSupportSum S X ⊓ simpleSupportSum T X = ⊥ ∧
  Mono (biprod.desc (simpleSupportSum S X).arrow
    (simpleSupportSum T X).arrow)
```

## Source and scope

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, A.IX,
printed page 268 / PDF page 274. Its registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Renard defines `E_S` as the sum of all subobjects of `E` supported on `S`,
states that this sum is supported, and asserts zero intersection and
the inclusion of the binary direct sum for disjoint `S` and `T`.
This module proves those last two assertions at the published target's
explicit size scope.

Worker 1006 read the complete A.IX page and the categorical conventions
at A.VI.2–3, printed pages 263–264 / PDF pages 269–270. The source's
Grothendieck convention supplies coproducts and directed-subobject-sum
distributivity, without a generator clause. Its AB6 is the local
finite-type condition, as explained in the source footnote and the
published `SourceAB6` definition.

The public [Appendix A discrepancy note](../../../notes/renard/appendix-a-corrections.md)
was read. The supplementary registered 2010-edition corrections,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF pages 18–19. Their old-page-310 letter correction is
already incorporated in the 2026 supported-sum passage. This is a
bounded comparison with the older corrections. Both retained source
files match their registered hashes.

## Implemented composition

The proof introduces `hG : IsSourceGrothendieck.{w} C` and installs
`HasCoproducts.{w} C := hG.1`. It retains `SourceAB6 C`, arbitrary sets
`S T : Set (ObjectClass C)`, both inclusions in `simpleClasses C`,
`Disjoint S T`, and every actual object `X`. The two instance premises
`Small.{w} (simpleSupportSubobjects S X)` and
`Small.{w} (simpleSupportSubobjects T X)` are introduced separately.
Each gives its corresponding full-family coproduct using the target's
`hasCoproductsOfShape_of_small.{w}` instance.

The first application of the published `simpleSupportSumSupport`
proves `HasSimpleSupport S (simpleSupportSum S X : C)`, using the
smallness premise for the full `S` family. The second application
proves `HasSimpleSupport T (simpleSupportSum T X : C)`, using the
separate smallness premise for the full `T` family. These applications
use the actual published sums with the derived coproduct instances.
The support conclusions come from the published support theorem;
they are not inferred merely from the sums' least-upper-bound laws.

With these two support proofs and `Disjoint S T`,
`inf_eq_bot_of_hasSimpleSupport_of_disjoint` gives zero intersection
of the actual sums. Apply
`mono_biprod_desc_arrow_of_inf_eq_bot` to that same equality to obtain
monicity of the actual `biprod.desc` of their inclusion arrows.
Pair the equality and monicity in the target's order.
The proof imports these results by Lean name from
[SimpleSupportSumProof](SimpleSupportSumProof.md) and
[SimpleSupportOrthogonality](SimpleSupportOrthogonality.md).

The universes `w`, `v`, `u` remain independent. The proof does not
discharge either full-family smallness premise or replace either family
with a chosen or finite subfamily. The target's source-sized coproducts
are preserved. No enlarged global coproduct hypothesis, finite-length
assumption or concrete-category restriction is introduced. Empty
supports and zero ambient objects remain included.

This is the literal-full-sum specialization reserved by the generic
orthogonality proof. It supplies no epimorphism, isomorphism,
exhaustiveness, size-discharge theorem, additional splitting or category
decomposition. Those obligations retain their separate scope and owners;
this result does not declare A.IX or the whole-book program complete.

## Authorship

Worker 709 supplied the private composition diagnostic using the two
support applications and the generic intersection and monicity results.
Worker 1006 adapted it to the exported exact-target theorem, shared the
intersection equality between the two conclusions, and wrote this
companion. The published support and generic orthogonality proofs are
reused unchanged by Lean name.

## Development check

The exported module compiled in the approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings.
Declaration inspection confirms a theorem with independent level parameters
`w`, `v`, `u` and only `propext`, `Classical.choice` and `Quot.sound`.
The target pair and all ten transitive Library pairs, including the target,
were compared with the assigned Library base and are unchanged. These
development checks are separate from exact-target validation, independent
semantic acceptance and publication.
