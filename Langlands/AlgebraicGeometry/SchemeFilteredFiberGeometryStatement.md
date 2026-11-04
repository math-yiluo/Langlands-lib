# Descent of nonempty geometrically connected pure-dimensional fibres

`Langlands.AlgebraicGeometry.SchemeLimitModel.FinitePresentationInitialRingFiberGeometryDescent`
is the proposition target for the final property clause of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp. 5–6, Theorem 3.4(2). Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It is a statement definition, not a proof.

Fix a natural number `d`, a small filtered category `J`, a diagram `F` of
actual commutative rings, an actual colimit cocone `c` with its colimit
witness, and a chosen starting stage `j₀`. Let `X` and `Y` be two schemes
over `Spec (F.obj j₀)` and `f : X ⟶ Y` a morphism over that base.
Both model structure maps are locally of finite presentation,
quasi-compact and quasi-separated. This is precisely the
finite-presentation convention immediately before the source theorem.
The models may be nonaffine and nonseparated.

The target asserts equivalence between:

- all residue-field fibres of the actual base-changed morphism over
  `Spec c.pt` being nonempty and geometrically connected of pure
  dimension `d`;
- that same fibre property for the actual base change along an outgoing
  original diagram arrow from `j₀`.

The left base map is exactly `Spec.map (c.ι.app j₀)`. A witnessing
`j : Under j₀` consists of an original stage `j.right` together with an
original arrow `j.hom : j₀ ⟶ j.right`; the right base map is exactly
`Spec.map (F.map j.hom)`. Thus the assertion keeps the original rings and
transition maps, including noninjective transitions. For a directed poset,
this is exactly existence of a later index `j ≥ j₀`. The extension from
directed posets to small filtered categories retains the outgoing arrow,
which need not be unique for a general category.

`AffineLimit.baseChangeMap` is the actual morphism between the two scheme
pullbacks, induced by `f` and the displayed common base map.
`SchemeFiberGeometry.NonemptyGeometricallyConnectedPureDimensionFibers`
uses their actual residue-field fibre schemes. Every irreducible component
of each fibre must have topological Krull dimension `d`, as explained in
the defining construction; the statement does not replace this with a
bound on total fibre dimension.

There are no properness, smoothness, flatness, noetherianity, separatedness
or affineness hypotheses in addition to the two models' finite
presentation assumptions. In particular, existing descent theorems that
assume properness and smoothness do not prove this target. The two
directions require stability of the fibre property under the relevant
base changes and its eventual detection in this finite-presentation
setting. Both remain proof obligations of this target. The statement covers this one property
clause, not the other assertions of Theorem 3.4 or whole-paper completion.
