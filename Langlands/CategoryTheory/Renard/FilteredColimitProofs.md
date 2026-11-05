# Renard A.IV.2: the concrete directed quotient is a colimit

This proof unit proves the existing
`Langlands.Renard.FilteredColimit.FilteredColimitStatements` using the actual
objects in [FilteredColimit](FilteredColimit.md). Its only import is the
published [statement module](FilteredColimitStatements.md); neither imported
pair is changed. The theorem `filteredColimitStatements` conjoins the five
published targets in their original order.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, Appendix A.IV.2, printed page 258 / PDF264,
final two paragraphs. The ordered-system convention appears on printed
page 257 / PDF263. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both pages were read and PDF264 visually inspected. The supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, was also read. Its old-page-298 correction from limit to colimit
is already incorporated in the governing 2026 text. No project
source-errata directory was present at this Library base.

## Implemented proof

`compatibleFamilyLiftStatement` proves factorization of the actual additive
quotient `lift` by evaluating it on `classOf` using `lift_classOf`. To prove
uniqueness, `exists_classOf` writes every quotient element as a representative.
The competing homomorphism's component equation then determines its value,
which is also the value of the published lift. This proof allows the target
abelian group in an independent universe `uH`.

`quotientColimitStatement` constructs an `IsColimit` witness for the exact
`cocone G f`. Given another cocone `s`, its legs are composed with the
additive equivalence raising each `G i` to `ULift.{uI} (G i)`. This produces
a compatible family on the original groups: cocone naturality, evaluated
at a raised element, is precisely the required compatibility equation.
The descent is the actual quotient `lift` of this family. Its representative
formula gives factorization of all the lifted legs. The compatible-family
uniqueness just proved gives categorical uniqueness after evaluating each
factorization equation on raised elements. The quotient vertex, its canonical
maps, and all transitions remain the published objects.

`eventualZeroStatement` uses the defining relation directly. Zero is the
class of zero at the given index by `zero_eq_classOf`. Thus
`classOf_eq_iff` turns the assumed equality with zero into equality of the
forward images of the given element and zero at a common later stage.
Every transition preserves zero, giving the required witness `j ≥ i`.
This proves the source's forward implication.

`eventualZeroIffStatement` reuses that implication. For the derived converse,
`of_comp` identifies the original canonical image with that of its forward
transition. If the latter representative is zero, zero preservation of
`of` proves that the original class is zero. The equivalence is an explicit
derived strengthening rather than another assertion attributed to Renard.

`emptyColimitStatement` constructs an `IsColimit` witness for the published
`emptyCocone G f`. The descent from its `PUnit` vertex is the zero additive
homomorphism; the component equations are vacuous because the index is
empty. Every element of `PUnit` equals zero, so any competing additive
homomorphism agrees by preservation of zero. This proof has no directedness
or nonemptiness premise.

## Scope and provenance

The nonempty quotient conclusions retain `PartialOrder I`,
`IsDirectedOrder I`, `Nonempty I`, arbitrary abelian groups and additive
transitions with their intrinsic `DirectedSystem` identity and composition
laws. The independent universes are `uI` for indices, `uG` for components
and `uH` for a compatible family's target. The categorical diagram retains
the published `ULift` factors in `AddCommGrpCat.{max uI uG}`. No injectivity,
countability, finiteness or generation assumption is introduced.

Renard's pairwise-upper-bound convention permits an empty index, but the
literal quotient of the empty disjoint union is empty and has no group
identity. The separate singleton cocone is the already published internal
completion of this boundary. It is distinguished from the nonempty
quotient and from author-issued errata. The proof does not change the
unrestricted general ordered-system statements, and it does not complete
Appendix A.IV or the whole-book program.

Worker 1153 implemented these proofs using the published construction and
statements by Worker 709 with Worker 6's source-scope reconciliation.
All mathematical imports use their current Lean names. The underlying
quotient and category APIs come from Mathlib at pin
`5ed2965256430c3649e86755f9576b54eca72435`, as documented in the imported
construction pair.
