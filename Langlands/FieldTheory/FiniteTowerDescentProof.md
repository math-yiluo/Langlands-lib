# Compatible finite-tower descent along a directed union: proof

Author: Worker 29.

`Langlands.FieldTheory.finiteTowerDirectedUnionDescent.{u,v}` proves exactly
`Langlands.FieldTheory.FiniteTowerDirectedUnionDescent.{u,v}`. There are no
additional hypotheses. The field universe `u` and index universe `v` remain
independent. All conclusions use one index `i`, one lower intermediate field
`B`, and one upper intermediate field `C`.

## Choosing the lower field with the upper coefficients

Let `b` be Mathlib's finite basis of `L` over `E`. The finite set `t` contains
`1`, the prescribed elements `sL`, all products of two vectors of `b`, and all
images of vectors of `b` under `E`-automorphisms of `L`. The automorphism group
is finite because `L/E` is finite dimensional. Let `coords` contain all
coordinates of the elements of `t` in the basis `b`.

Apply the published theorem
`Langlands.FieldTheory.finiteExtensionDirectedUnionDescent` to `E/U`, with
initial stage `i₀` and prescribed finite set `sE ∪ coords`. This supplies a
single later stage `A i` and a field `B` inside `E`, finite dimensional of
degree `[E:U]` over `A i`, linearly disjoint from `U`, and generating `E`
together with `U`. Its finite-set conclusion puts all upper coordinates in
`B`. Its separability implication, applied to the given separability of
`E/U`, proves separability of `B/(A i)`. The one-extension theorem's Galois
implication is unused; neither `E/U` nor `L/U` is assumed Galois.

## Constructing the upper field

The private helper `basis_span_field` constructs the `B`-span of `b` in `L`.
`Basis.mem_span_iff_repr_mem` identifies this span with exactly the elements
whose coordinates in `b` lie in `B`. The chosen coordinates of `1` and of
basis products show that the span is a unital subalgebra, using two span
inductions for multiplication. This subalgebra is finite dimensional, hence
algebraic; `Algebra.IsAlgebraic.toIntermediateField` makes it an actual
intermediate field `C` with the same underlying set. No inverse-closure
assumption is added.

`Basis.restrictScalars` supplies a `B`-basis `c` of `C` whose images in `L`
are precisely `b`. Equal index types give `[C:B] = [L:E]`.
`IntermediateField.LinearDisjoint.of_basis_left`, applied to the independence
of `b`, gives `C.LinearDisjoint E`. Expansion in `b` shows that `C` and `E`
generate `L`. The coordinate criterion places every element of `sL` in this
same `C`.

For the helper call, `B.toSubfield` presents the underlying subfield of `E`.
The explicit type of `hspan` identifies the resulting field and basis with
`C : IntermediateField B L` and its canonical `B`-scalar structure. This is
a definitional identification, not a replacement by an abstractly isomorphic
field.

## Galoisness of the upper field

The private helper `basis_galois` restricts each `E`-automorphism of `L` to a
`B`-algebra endomorphism of `C`. Its images of all basis vectors belong to
`C` by the chosen coordinates; expansion in `c` then proves preservation of
every element. Two automorphisms with the same restriction agree on `b`,
so they agree everywhere on `L`.

Consequently, `C` has at least `[L:E] = [C:B]` distinct `B`-algebra
endomorphisms. Mathlib's `AlgHom.card_le` gives the opposite inequality.
`algEquivEquivAlgHom` identifies endomorphisms with automorphisms for this
finite field extension, and `IsGalois.of_card_aut_eq_finrank` proves
`IsGalois B C`. The source of the lower bound is the given Galoisness of
`L/E`, via `IsGalois.card_aut_eq_finrank`.

## Total degree, independence, and compositum

Finite dimensionality is transitive in both towers. Multiplicativity of
finite degree, together with the lower and upper equalities, gives
`[C:A i] = [L:U]`.

Choose a finite `A i`-basis `a` of `B`. The basis `d = a.smulTower c` is an
`A i`-basis of `C`; its image in `L` consists of the products of the images
of `a` in `E` and the vectors of `b`. Lower linear disjointness implies that
the image of `a` is `U`-linearly independent in `E`. The theorem
`linearIndependent_smul`, combined with the `E`-linear independence of
`b`, proves that the image of `d` is `U`-linearly independent in `L`.
Applying `IntermediateField.LinearDisjoint.of_basis_left` proves
`(C.restrictScalars (A i)).LinearDisjoint U`.

The index cardinality of `d` is `[C:A i] = [L:U]`. Therefore
`basisOfLinearIndependentOfCardEqFinrank'` turns its image into a `U`-basis
`e` of `L`. Expanding every element of `L` in `e` proves that `C` and `U`
generate `L`. This establishes the total compositum directly, using the
same `C` as the upper-degree and Galois conclusions.

## Literal maps and scope

The proof installs the precise composite `U`-algebra on `L` from the target,
and the precise `Algebra.ofSubsemiring` structures from `A i` to `U`, `E`,
and `L`, and from `B` to `L`. The scalar towers are established by the
literal algebra-map equalities. Both routes from `B` to `L`, through `C`
and through `E`, equal the same `algebraMap B L`; the two
`IsScalarTower.algebraMap_eq` identities prove the final ring-hom equality.

No positive lower bound beyond the automatic nonzero dimension of fields
is needed. The argument covers degree-one extensions, empty prescribed
finite sets, and arbitrary characteristic. It adds no valuation, local-field,
ramification, norm, or cohomology assertion.

## Provenance and dependencies

Source: Jean-Pierre Serre, *Local Fields*, Greenberg English translation,
GTM 67 (1979), Chapter V, section 4, Lemma 6 and its proof, printed page 89
(PDF page 96), and the simultaneous-model passage in Proposition 7, printed
page 90 (PDF page 97). Registered source: `serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Both original pages were read and the source hash checked. No project errata
note for this source was found.

The target is the derived compatible-tower formulation explained in its
published Markdown, authored by Worker 29 with Worker 60's formulation.
The implemented proof descends the lower field with a prescribed upper
coefficient set, constructs the upper span, and uses a product basis for
the total conclusions. It does not require simultaneous selection of two
initial bases over the directed stages. The two private helpers are reused
from Worker 29's own accepted single-extension proof. No other worker's
proof draft was used.

Project imports are the unchanged `FiniteTowerDescentStatement` and
`FiniteExtensionDescentProof` modules. The additional Mathlib import is
`Mathlib.RingTheory.AlgebraTower`; the single-extension import already
provides the basis-span and field-theory APIs. The environment is Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
