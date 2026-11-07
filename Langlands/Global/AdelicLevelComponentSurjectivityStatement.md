# Almost-all native level surjectivity without a common fibre dimension

This derived statement isolates the cofinite-surjectivity input in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Theorem 4.5, printed pp.12–13. It combines the finite-component version of
uniform Lang–Weil and Henselian lifting with the finiteness of the places
having bounded residue cardinality. It does not assume a common fibre
dimension across the target's connected components.

Both clauses retain the full `UniformLangWeilStatement` as a premise. The
actual target model `B` is quasi-compact and locally of finite type over
`Spec (ULift ℤ)`, expressing finite type over the integers. The relative
morphism `f : Y ⟶ B` is smooth, separated, quasi-compact and geometrically
connected. Smoothness supplies local finite type, and geometric
connectedness includes nonempty geometric fibres and hence surjectivity.
There is no separate assumption that either model is affine or separated
over the coefficient base. The absolute finite-type hypothesis on `B`
remains explicit and must be verified in an application to a chosen spread.

For every original finite set `S` and every enlarged level `T` containing
`S`, the actual maps on native local-factor points are surjective at
cofinitely many indices. The point types are the original `RingPoint`
types over the S-integer ring. Their coefficient actions are the native
T-level actions restricted along the literal inclusion from the original
S-integer ring. Surjectivity therefore asserts lifts over that original
base, with the actual equation `a ≫ f = p`.

The function-field clause covers every finite constant field `k` and
function field `F`, with its actual curve places, completed fields, and
completed integer rings. The number-field clause uses every finite place
of `K` and retains all original infinite-place factors. The schemes,
coefficient rings and fields have an arbitrary common universe `u`.
No separability assumption is added to the function-field presentation.

The finite exceptional index set can contain every supported completed
field factor, every infinite factor in the number-field case, and every
integral factor with residue cardinality below the uniform bound.
Consequently the assertion requires no surjectivity at any exceptional
field factor. Outside this finite set, smooth Hensel lifting of finite-field
points gives exact integral lifts. The uniform bound comes from applying
the fixed-dimension estimate separately to the finitely many actual
target components and taking a finite bound on their constants; an entire
adelic point need not occupy one component.

These are proposition definitions awaiting a separate proof. They supply
the cofinite input of `AdelicModelOpenReductionStatement`; they do not
prove uniform Lang–Weil, local openness, compatible model existence or
adelic openness. These remain separate obligations of the whole-paper task.
