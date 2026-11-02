# Renard A.IX: internal simplicity and the partition of simple classes

The module `Langlands.CategoryTheory.Renard.CategoryDecompositionSimpleClassesProof`
proves the unchanged published aggregate
`Langlands.Renard.CategoryDecompositionSimpleClassesStatement.{w} C`.
Its main theorem is
`Langlands.Renard.CategoryDecompositionSimpleClassesProof.simpleClasses`.
The same namespace supplies the two constituent proofs `simplicity` and
`partition`.

## Source and provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix A.IX, first assertion
after the definition of a category decomposition, printed page 268 / one-based
PDF page 274. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The complete page was read. Renard asserts that a category decomposition gives
a disjoint union of simple isomorphism classes in his Grothendieck and AB6
setting, without a proof of this assertion on that page.

This proof has **derived provenance**: it establishes the published target's
generalization to arbitrary abelian categories and makes the internal/ambient
simplicity comparison explicit. That generality is not attributed verbatim to
the original. The proof uses only the particular cofans already supplied by
the actual decomposition assumption, zero morphisms, full-subcategory
morphisms, and the abelian mono/epi isomorphism criterion.

The project note [Appendix A discrepancies](../../../../notes/renard/appendix-a-corrections.md)
records no correction to this assertion. The supplementary 2010-edition errata,
registered as `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were also read at PDF pages 18–19. The entry for old page 310 corrects later
supported-sum notation; it does not amend this simple-class assertion. This is
a bounded comparison with a different edition.

## Exact scope

Let `C : Type u` have `[Category.{v} C] [Abelian C]`. The index universe `w`,
Hom universe `v` and object universe `u` are independent. The two constituents
quantify arbitrary `I : Type w`, `P : I → ObjectProperty C` and
`hP : IsCategoryDecomposition P`.

The first proves, for each `i : I` and `X : (P i).FullSubcategory`,
`Simple X ↔ Simple X.obj`. Internal simplicity uses Mathlib's actual full
subcategory and its inherited zero morphisms. The second proves, for every
ambient `q : ObjectClass C`,

```lean
q ∈ simpleClasses C ↔
  ∃! i : I, ∃ X : (P i).FullSubcategory,
    Simple X ∧ objectClass X.obj = q
```

The uniqueness is of the component index. Representatives and isomorphisms
are not asserted unique. Literal membership in a component is supplied for
the selected representative, and comparison with other ambient objects uses
the published isomorphism-class quotient.

## Implemented proof

The helper `cofan_leg_mono` takes an actual colimiting cofan with legs
`ι i : Y i ⟶ T`. For a fixed index it descends the identity on that component
and zero maps on every other component, using equality transport on the
matching index. The cofan factorization equation makes this a retraction of
`ι i`. Thus each leg is a split monomorphism and in particular a monomorphism.
No chosen global coproduct is used.

The helper `mono_hom` proves that a monomorphism inside a component is also
monic in the ambient category. To cancel it against maps from any ambient
object `T`, decompose `T` by `hP`. After precomposing with the matching leg,
internal cancellation applies because the test component belongs to the same
full subcategory. After every other leg both maps vanish by `hP`'s
off-diagonal Hom condition. Joint determination of maps by a colimiting
cofan's legs gives ambient cancellation.

The theorem `simple_iff` proves the comparison in both directions. Suppose
first that `X` is internally simple. Its identity remains nonzero in the
ambient category by faithfulness. For a nonzero ambient monomorphism
`f : T ⟶ X.obj`, decompose `T`. The composite with the leg at `i` is nonzero:
otherwise every composite would be zero, by off-diagonal vanishing at all
other indices, forcing `f = 0`. That composite is mono, because both the
cofan leg and `f` are mono, and is a morphism between actual objects of the
component. The inclusion reflects monomorphisms, so internal simplicity
makes the internal composite invertible. Its ambient image is invertible,
which makes `f` epi; since `f` was mono, the abelian mono/epi criterion makes
it invertible. Conversely, an invertible `f` cannot be zero because the
ambient identity of `X.obj` is nonzero. This gives ambient simplicity.
In the reverse direction `mono_hom` lets ambient simplicity apply to every
internal monomorphism. The full-subcategory inclusion reflects
isomorphisms and detects zero morphisms, giving the internal simplicity
criterion. The theorem `simplicity` packages this as the exact first target.

For `partition`, take an ambient simple representative `T` of the given
class and decompose it. Some cofan leg must be nonzero: if all were zero,
the cofan universal property would force the identity of `T` to be zero,
contrary to simplicity. That leg is mono by `cofan_leg_mono` and therefore
invertible by ambient simplicity. Its source is an actual object of its
component, is ambiently simple by transport along that isomorphism, and is
internally simple by `simple_iff`. The isomorphism gives equality with the
original ambient class via `objectClass_eq_iff`.

For uniqueness, any simple representative in another component with the
same ambient class would be isomorphic to the selected representative.
If its index were different, the isomorphism's forward map would vanish by
off-diagonal orthogonality. Composing with its inverse would force the
identity of a simple object to be zero. Therefore the indices coincide.
The reverse implication simply takes the representative supplied by the
unique-existence assertion and uses `simple_iff` to recover ambient
simplicity. Finally `simpleClasses` pairs `simplicity` and `partition` in
the order of the unchanged aggregate definition.

## Dependencies and boundaries

The sole direct import is the unchanged
[statement module](CategoryDecompositionSimpleClassesStatements.md). Its
published imports provide the actual decomposition predicate and the
ambient isomorphism-class quotient. The proof imports those constructions
by Lean name and changes none of their Lean or Markdown files.

There is no assumption of repleteness, component abelian structures,
closure under subobjects, well-poweredness, finite length, a nonempty index
type, Grothendieck or AB6 axioms, or global coproducts. The nonzero-leg
argument also covers the empty-index case: under the decomposition
antecedent such a category has no simple objects. Zero components require
no separate treatment. The proof does not construct supported sums,
product-category equivalences, support closure, splitting, or subquotient
results, and does not assert completion of A.IX.

The proof is checked in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection retains independent
universe parameters `w`, `v`, `u` and uses only `propext`,
`Classical.choice`, and `Quot.sound`.
