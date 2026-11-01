# Renard A.IV: inverse and direct systems

Author: Worker 709.

This pair states the universal-property characterizations for inverse
and direct systems in Appendix A.IV. It contains three closed
`Prop`-valued definitions, with no proofs of the propositions and no
existence assertion for limits in arbitrary categories.

## Source and conventions

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passages are A.IV.1 example 5 and the explicit direct-system
paragraph of A.IV.2, both at printed p.257 / one-based PDF263. The
concrete universal property after (A.IV.1.2) at printed p.256 / PDF262,
and its A.IV.2 dual, supply the factorization properties expanded here.
Both original pages were read in full; PDF263 was also visually checked.

The supplementary author errata for the 2010 edition are registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
PDF18–19 were read. On PDF18 the correction to old printed p.298
identifies the direct limit with a colimit. The governing 2026 paragraph
already says colimit. This is a bounded errata check, and the older
errata do not replace the governing edition.

The source takes an ordered set with a common upper bound for each pair
of elements. We use `I : Type uI`, `[PartialOrder I]` and
`[IsDirectedOrder I]`. The latter is precisely the pairwise upper-bound
condition. Neither it nor the source's displayed definition requires
`Nonempty I`; empty indices are retained. Infinite indices are retained
as well. The universal-property equivalences would also hold without
directedness, but the statements preserve the hypotheses of this source
example.

Mathlib's ordinary preorder category has a morphism `i ⟶ j` for
`i ≤ j`, written `homOfLE h`. The source's inverse-system index category
instead has `j ⟶ i` for `i ≤ j`. It is modeled by `Iᵒᵖ`. The direct-system
index category is modeled by `I` itself. These canonical index categories
have object and morphism universe `uI`. The object universe `uC` and
morphism universe `vC` of the target category are independent of each
other and of `uI`.

For inverse transitions, the source first writes
`D(j → i) = f_ji` but interchanges the displayed subscripts in the
example's final sentence. We use the direction fixed by its definition
`j → i`. The general colimit prose also reverses its factor arrows;
the displayed `D → ΔX → ΔY` fixes their direction as `X → Y`.
That general correction was diagnosed by Worker 6 and implemented by
Worker 610 in the separate
[`ConeBridge` pair](ConeBridge.md), as explained in the
[Appendix A source audit](../../../notes/renard/appendix-a-corrections.md).
The present direct-system statement retains that outward factor map.

## The two characterizations

All names below are in `Langlands.Renard.OrderedSystemLimit`.
Each component binds every parameter internally, starting with an
arbitrary `C : Type uC` and `[Category.{vC} C]`. No zero, additive or
abelian structure is assumed.

`InverseLimitStatement.{vC,uC,uI}` takes an actual
`D : Iᵒᵖ ⥤ C` and `t : Cone D`. For `h : i ≤ j`, its transition is

```text
D.map (homOfLE h).op : D.obj (op j) ⟶ D.obj (op i).
```

It asserts `Nonempty (IsLimit t)` if and only if, for every `Y : C`
and every family `q i : Y ⟶ D.obj (op i)` satisfying

```text
q j ≫ D.map (homOfLE h).op = q i,
```

there is a unique `l : Y ⟶ t.pt` satisfying
`l ≫ t.π.app (op i) = q i` for every `i : I`.

`DirectLimitStatement.{vC,uC,uI}` takes an actual
`D : I ⥤ C` and `t : Cocone D`. For `h : i ≤ j`, its transition is

```text
D.map (homOfLE h) : D.obj i ⟶ D.obj j.
```

It asserts `Nonempty (IsColimit t)` if and only if, for every `Y : C`
and every family `q i : D.obj i ⟶ Y` satisfying

```text
D.map (homOfLE h) ≫ q j = q i,
```

there is a unique `l : t.pt ⟶ Y` satisfying
`t.ι.app i ≫ l = q i` for every `i : I`.

In both components compatibility is required for every `i`, `j` and
proof `h : i ≤ j`. Each morphism in the corresponding index category
comes from such an inequality. Thus these are exactly the naturality
conditions on a competing cone or cocone. The functor identity and
composition laws already encode the system's transition laws, and the
supplied cone or cocone stores its vertex and compatible legs. No custom
system or universal-property certificate is introduced.

`IsLimit` and `IsColimit` carry universal-witness data. `Nonempty` turns
existence of those data into a proposition on the left of the
equivalence. The right side quantifies unique actual categorical
morphisms satisfying the displayed equations. No limiting witness or
universal-factorization property is assumed as an input.

`OrderedSystemLimitStatements.{vC,uC,uI}` is exactly the conjunction
of `InverseLimitStatement` followed by `DirectLimitStatement`, at the
same three independent levels.

## Provenance and boundary

The identification of inverse/direct systems with the respective
ordered-diagram limits/colimits is in the source. The explicit `iff`
formulas expand the concrete general universal property on these
shapes. The closed definitions, proposition wrappers and conjunction
are internal formal packaging, rather than additional numbered source
assertions. The precise inequality formulas follow from the source's
stated arrow conventions.

The imported Mathlib modules provide actual preorder categories,
functors, cones, cocones and universal witnesses. A later proof can
assemble a cone or cocone from an inequality-compatible family and
use `IsLimit.existsUnique` / `IsLimit.ofExistsUnique` and their colimit
duals. This is an implementation route, not proof evidence.

The preceding general `ConeBridge`, the eight elementary shape
characterizations, subobject intersections and unions, existence
results in abelian categories, concrete abelian-group products and
direct sums, and filtered-colimit quotient/eventual-equality
constructions are separate units. This pair completes none of A.IV,
Appendix A or the whole-book program. A proof successor must target the
unchanged Library aggregate after independent statement acceptance and
actual publication.
