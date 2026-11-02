# Renard II.2.1: sheaf germ separation and corrected target compatibility

This module states the zero-germ separation lemma and the corrected local
compatibility needed in David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed pp.35–37 /
one-based PDF pp.41–43. The precise source lemma and displays
(II.2.1.3)–(II.2.1.5) are on printed p.36 / PDF p.42. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
All three pages were read directly, and the formulas and lemma on PDF p.42
were visually checked.

The separately registered 2010-edition *Corrections et compléments*, source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF pp.2–3. Those pages correct other cover-index and adjunction
formulas. This is a supplementary older-edition check, not a claim that this
errata document supplies the correction below.

The imported `BasisPresheaf`, `BasisSheaf` and `BasisStalk` constructions supply
the actual chosen topological basis, section groups, restrictions, stalks,
germ maps and morphisms. Every declaration here is a `Prop`-valued `def`.
None is a theorem or a proof of its asserted proposition.

`SheafZeroGermSeparationStatement G` is the source lemma on a bundled
`BasisSheaf`: if a section on a basis open has zero germ at every point of
that open, it is zero. Its section group is `Sections G.obj.obj U`, and its
germs are the existing normalized maps `germ G.obj U x hx`. The sheaf
condition is supplied by the actual bundled object, rather than an added
assumption about an unrelated group of sections.

`RawSheafZeroGermSeparationStatement F` is an internal extension of the same
assertion to `RawPresheaf` with the literal hypothesis `SheafCondition F`.
This does not drop the source's empty normalization: the published
`SheafCondition.isNormalized` already derives it from empty-cover uniqueness.
The raw statement uses the original, unlifted sections as inputs to
`rawGerm F U x hx`. The actual stalk is `rawStalk F x`, whose group carrier
lies in `Type (max u v)`.

`RawSheafGermEqualityStatement` and `SheafGermEqualityStatement` are the
corresponding derived equality-detection assertions for two sections on the
same basis open. Their expected mathematical derivation applies zero-germ
separation to the difference, using additivity of the existing germ maps.
They quantify equality at every point and membership proof on the whole
open. They do not assert injectivity of the germ map at any single point.
No derivation is proved in this module.

The independently published
[source-error note](../../../notes/renard/basis-sheafification-source.md)
explains why the printed equality (II.2.1.3) is false for the arbitrary
source presheaf in the adjunction argument. Equality of all original germs
does not imply equality of original presheaf sections. Its normalized
two-point counterexample has group `ℤ` on the whole discrete space and
zero groups on all proper opens. All stalks vanish, so the distinct whole
sections zero and one have equal germs. Repeating the whole open twice in
the cover gives the false claimed overlap equality. The source-error note
also records that an arbitrary chosen basis need not contain the
intersection of two members.

`RawTargetGermCompatibilityStatement F G ψ` therefore states the corrected
conclusion needed for (II.2.1.4). Assume `SheafCondition G`, let
`ι : Type w`, take any family `U : ι → BasisOpen B` and original sections
`s i : Sections F (U i)`, and assume that their `F`-germs agree at every
common point. The conclusion is the literal published predicate
`Compatible G U (fun i => ψ.app (op (U i)) (s i))`. On unfolding, it says
that for every `i`, `j`, actual basis open `W`, and inclusions
`hWi : W.obj ≤ (U i).obj`, `hWj : W.obj ≤ (U j).obj`,

```text
restriction G hWi (ψ.app (op (U i)) (s i)) =
  restriction G hWj (ψ.app (op (U j)) (s j)).
```

Thus restrictions are compared on every smaller basis open contained in
both members. There is no need to evaluate a presheaf on an intersection
outside the basis. No sheaf condition, normalization or separation is
assumed on the raw source `F`. No covering hypothesis is imposed on `U`.
Omitting that hypothesis is a derived strengthening of the local
compatibility used in the source's cover argument, since the comparison
only concerns points of each smaller overlap open.

The corrected mathematical route is to apply the actual induced stalk
map of `ψ` to equality of the original germs. The published
`rawStalkMap_germ` and `rawGerm_restriction` then identify the germs of the
two restricted image sections on `W`. Equality detection applies to the
target sheaf `G` on `W`. This route explains the provenance and hypotheses
of the corrected assertion; its Lean proof remains an obligation.

`TargetGermCompatibilityStatement F G ψ` specializes this assertion to the
actual source categories `F : Presheaf B`, `G : BasisSheaf B`, and
`ψ : F ⟶ G.obj`. Its premise uses the normalized `germ F` and its image
family uses the actual underlying components `ψ.hom.app`. Its conclusion
is `Compatible G.obj.obj U` on those images. The source is merely
normalized; the target's sheaf condition is supplied by `G`.

`RenardSheafGermSeparationStatement` is the closed conjunction of all six
component families, in the order raw zero, raw equality, bundled zero,
bundled equality, raw target compatibility, and normalized target
compatibility. It quantifies over the actual space `X : Type u`, its
supplied topology, chosen basis, all presheaves, sheaves and morphisms.
The space level `u`, original section-group level `v`, and family-index
level `w` are independent. There is no universe inequality or smallness
hypothesis; the imported stalk remains in `max u v`.

No separation, countability, local compactness, global nonemptiness or
intersection-closure assumption is added. Empty opens, empty families,
empty spaces and bases are retained wherever the actual basis condition
permits them. On an empty open the all-points premises are vacuous and
the sheaf condition still supplies uniqueness. Empty-index compatibility
is the literal vacuous predicate.

Worker 595 authored these statement definitions and their source
comparison. Worker 6 supplied the original-source audit, the target
separation correction and the focused statement design. The raw-input
extension, equality consequences, cover-free local strengthening and
closed aggregate are derived formal packaging, rather than additional
verbatim claims of the book.

The proofs of these propositions, the canonical germ-section unit,
actual descent maps, Hom equivalence and adjunction, the sheaf unit
isomorphism, and the basis/all-open category equivalence remain separate
obligations. This statement family does not complete II.2.1.
