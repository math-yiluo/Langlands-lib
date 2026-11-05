# Finite separable splitting of actual irreducible components

`Langlands.AlgebraicGeometry.SchemeFiberGeometry.FiniteSeparableComponentSplitting`
states Stacks Project Lemma 33.8.16 (054R) in arbitrary common universe `u`.
For a field `K` and an actual locally finite-type scheme morphism
`f : X ⟶ Spec K`, assume only that the type of actual maximal irreducible
components of `X` is finite. There exists a field `L`, an actual `K`-algebra
structure on it, a finite-dimensional `K`-vector space structure, and
separability of the extension such that all actual maximal components of
`pullback f (Spec.map (algebraMap K L))` are geometrically irreducible over `L`.

The extension map is the actual spectrum map of the chosen algebra map.
The structure morphism of the scalar extension is the second pullback
projection. For each component, the closed subscheme is defined by its
actual vanishing ideal, and geometric irreducibility applies to its
closed immersion followed by that second projection. Thus the indices
are the maximal irreducible subsets of the scalar extension, with their
reduced closed scheme structures. They are not an assumed family of
components or rational points. The field and scheme universes are the
same arbitrary `u`, with no finite-universe specialization.

The finite-component hypothesis matches the source's finiteness of the
set of irreducible components. Quasi-compactness is not assumed. Local
finite type alone would not imply finiteness of the components for a
non-quasi-compact scheme; the explicit finite type of components retains
the source's separate assumption. No separatedness, reducedness,
Noetherianity of the whole source, perfectness of `K`, characteristic
condition, or nonemptiness of `X` is added. For the empty scheme the
component condition is vacuous, as in the source.

Source: `stacks-finite-separable-component-splitting-054r-2026-11-04`,
retained original HTML of Lemma 33.8.16, tag 054R, statement and proof,
retrieved 4 November 2026, SHA-256
`913a8e8981dbf528885f614299c5a4b6b474d3579b789f33bda810a0cb4a05df`.
The original proof passes to a separable algebraic closure, uses the
finiteness and component descent in Lemma 33.8.15, and descends the
finitely many components to a common finite subextension. The retained
054R page has no comments or corrections.

This pair supplies a proposition definition only. It proves neither
this splitting theorem nor the finite étale cover construction in
Stacks 0551. It is a substantial independent prerequisite for the
latter exact generic-fibre splitting target.
