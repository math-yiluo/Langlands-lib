# Actual adelic Hausdorff topological groups

`Langlands.Global.adelicSpreadGroup` proves exactly
`Langlands.Global.AdelicSpreadGroupStatement` at arbitrary common universe
`u`. Both arithmetic clauses use the existing actual full-adele point carrier,
the canonical group on morphisms into the group object, and precisely the
specified-spread topology in the target. The chosen arithmetic model has no
group structure or separatedness assumption.

## Group operations

The private `pointGroup_topological` works with the actual point type
`RingPoint R G.X A`, namely `ringTest R A ⟶ G.X`, and two supplied topologies
on the group and its scheme product. Mathlib's existing Hom multiplication is
the categorical product lift followed by `μ[G.X]`; inversion is postcomposition
by `ι[G.X]`. The hypothesis here is a homeomorphism from product-scheme points
to the product of group-point spaces, together with continuity of the two
scheme-operation point maps.

The product comparison sends the lift of two points back to the same pair by
`lift_fst` and `lift_snd`. Its inducing property therefore proves continuity of
the lift map from the topological product. Composing with the multiplication
point map proves continuity of the canonical Hom multiplication. The inversion
hypothesis is already continuity of the canonical inverse operation. This
constructs `IsTopologicalGroup` for the existing group, without replacing its
operations or defining a topology from them.

## Hausdorffness

The private `group_diagonal_closed` uses the published
`Langlands.GroupScheme.fieldSeparated` theorem. The scheme map underlying the
categorical diagonal `lift (𝟙 G.X) (𝟙 G.X)` is Mathlib's
`pullback.diagonal G.X.hom`; separatedness over the field makes this a closed
immersion. This argument concerns the field group scheme and places no
separatedness assumption on its arithmetic model.

The private `pointGroup_t2` composes the closed embedding on points induced by
this diagonal with the product comparison homeomorphism. The categorical
projection identities identify the composite with `p ↦ (p, p)`. Its range is
the usual diagonal subset of the product topological space, hence is closed.
`t2_iff_isClosed_diagonal` gives Hausdorffness for the original point topology.

## Arithmetic specialization

In each arithmetic clause, take the actual product `M ⨯ M` over the same
integer base. The product is finite type: its first projection is the base
change of the finite-type structure map of the second factor, and the product
structure map is the composite with the first factor's structure map. The
published `finiteType_overProd` from `AdelicSpreadProductProof` records this
without separation assumptions.

Generic-fiber pullback preserves binary products. The published
`productModelIso` from the same imported module uses that preservation, the two copies of the specified
isomorphism `e`, and uniqueness of limiting binary fans to identify the
generic fiber of `M ⨯ M` with the cartesian monoidal product `G.X ⊗ G.X`.
`adelicSpreadProduct` then gives the homeomorphism on actual full-adele points
with the required spread topologies. `adelicSpreadFunctoriality`, applied to
multiplication and inversion as field-scheme morphisms, gives the two
continuity inputs. `adelicSpreadClosedImmersion`, applied to the closed field
diagonal and the chosen product spread, gives the closed embedding used for
Hausdorffness. The two generic point-topology helpers finish these clauses.

For function fields, these steps retain arbitrary perfect constant fields,
the specified rational-function action and scalar tower, and potentially
inseparable function-field extensions. Only after introducing `Finite k`
does the proof apply `adelicSpreadTopologicalProperties.1`, taking its local
compactness and second-countability components. For number fields it uses the
corresponding `.2` components, and all infinite factors remain in the actual
full adele ring. Empty finite place sets are allowed in both clauses.

## Provenance and submission boundary

The target's source is Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed
p.9, Section 4. That passage gives locally compact Hausdorff adelic topological
groups over global fields, with the preceding countable-base assertion. The
arbitrary-perfect-constant Hausdorff topological-group extension is derived
as explained in the target Markdown and implemented above. The proof does not
assert existence of arithmetic spreads or complete the whole-paper parent.

Worker 208 authored the proof and its explanation, including the use of the two small
product-model helpers from that worker's earlier product proof. Worker
1644 checked the pair against the current Library and prepared this submission.
The prerequisite proof modules are imported from the published Library; this
contribution contains only the new proof and its paired Markdown.
