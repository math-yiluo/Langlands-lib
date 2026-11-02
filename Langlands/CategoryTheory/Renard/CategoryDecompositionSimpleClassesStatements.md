# Renard A.IX: simple classes of a category decomposition

This statement unit makes precise the first assertion after the definition of
a category decomposition in Renard 2026 A.IX. It uses the published actual
coproduct and off-diagonal Hom conditions and explicitly compares internal and
ambient simplicity. The module supplies proposition definitions, with no
proof of any of them.

The module is
`Langlands.CategoryTheory.Renard.CategoryDecompositionSimpleClassesStatements`,
in namespace `Langlands.Renard`.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, Appendix A.IX, printed page 268 / PDF page 274.
The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The complete original page was read for this assertion audit.

The source introduces the decomposition in its Grothendieck and AB6 setting,
then asserts that the simple isomorphism classes are the disjoint union of
the component simple classes. This module's provenance is **derived**:
the internal/ambient comparison is an explicit prerequisite, the partition is
expressed through actual representatives in the ambient class quotient, and
the targets omit the source's infinitary and local-finite-type assumptions.
This is an internal generalization to arbitrary abelian categories, not
wording attributed to a separately printed source theorem. The actual
decomposition assumption still supplies a coproduct cofan for every object.
No weaker decomposition certificate is substituted.

The project note `notes/renard/appendix-a-corrections.md` has no correction
to this assertion. The supplementary 2010-edition errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked at PDF pages 18–19. Their entry for old page 310 repairs the
later supported-sum notation, not this assertion. These are bounded checks;
the 2026 edition remains the governing source.

## Exact targets

Let `C : Type u` have `[Category.{v} C] [Abelian C]`. The three universes
`w`, `v` and `u` are independent. All targets quantify over arbitrary
`I : Type w`, including empty `I`, and arbitrary actual object properties
`P : I → ObjectProperty C`.

The shared antecedent is the existing `IsCategoryDecomposition P`. It says
that every ambient object `T` admits actual objects `Y i` with `P i (Y i)`
and maps `Y i ⟶ T` exhibiting `T` itself as their coproduct; every morphism
between objects of different component full subcategories is zero.

`CategoryDecompositionSimplicityStatement C` states:

```lean
∀ (I : Type w) (P : I → ObjectProperty C), IsCategoryDecomposition P →
  ∀ (i : I) (X : (P i).FullSubcategory), Simple X ↔ Simple X.obj
```

On the left, `Simple X` is simplicity in the actual full subcategory
`(P i).FullSubcategory`, with its inherited zero morphisms. On the right it
is simplicity in `C`. Mathlib defines `Simple` in any category with zero
morphisms: a monomorphism into the object is an isomorphism exactly when
it is nonzero. Consequently no abelian structure on the full subcategory
is an input. The comparison is asserted as a conclusion, rather than
silently identifying these two notions.

`CategoryDecompositionSimplePartitionStatement C` states:

```lean
∀ (I : Type w) (P : I → ObjectProperty C), IsCategoryDecomposition P →
  ∀ q : ObjectClass C, q ∈ simpleClasses C ↔
    ∃! i : I, ∃ X : (P i).FullSubcategory,
      Simple X ∧ objectClass X.obj = q
```

Here `ObjectClass C` is the published quotient by actual ambient
isomorphisms, and `simpleClasses C` is its set of simple classes. The
predicate after `∃! i` describes the image of the internally simple
component classes under the full-subcategory inclusion. It does not test
literal membership of an arbitrary ambient representative in `P i`.
Uniqueness concerns the index `i`, not an object or an isomorphism.
Equality of the ambient classes of two component representatives in the
same block gives an ambient isomorphism, which also gives an isomorphism
inside that full subcategory. Thus the image formulation does not
identify different internal isomorphism classes.

The statement gives both exhaustion of all ambient simple classes and
disjointness of the component images. If `I` is empty it asserts that
there are no simple ambient classes; the antecedent then requires every
ambient object to be an empty coproduct.

`CategoryDecompositionSimpleClassesStatement C` is the conjunction, in
order, of the simplicity comparison and the class-partition target.
All three declarations are `def` returning `Prop`.

## Reason for the generalization

The intended proof uses only the supplied coproduct cofans, zero
morphisms and the definition of simplicity. The decomposition lets one
test a monomorphism between objects of a fixed block against any ambient
object: decompose the test object, use the internal test on the matching
component, and use off-diagonal vanishing on the other components.
This accounts for the internal/ambient comparison without assuming
closure under ambient subobjects.

Each leg of a supplied coproduct cofan has a retraction obtained from
the identity on its component and zero maps on the other components.
For a nonzero simple vertex some leg is nonzero, and that monomorphism
must be an isomorphism. Off-diagonal vanishing excludes a nonzero simple
representative in two different blocks. These observations motivate the
targets under the stated hypotheses; they are a proposed proof route,
not an implemented or accepted proof.

No global coproduct instance, well-poweredness, smallness, relation
between the universes, finite-length restriction, nonempty-index
assumption, repleteness, closure hypothesis or abelian-subcategory
instance is imposed. In particular, source-sized coproduct transport is
not needed: the antecedent already supplies the particular cofans used
here.

## Scope

The existing `RenardCategoryDecomposition` and `CompositionChains` pairs
are imported unchanged. This unit does not construct a category
equivalence, a supported sum or a supported-subcategory abelian
structure, and it proves no simple-support closure or splitting result.
The existing `SimpleSupport` task families retain their scopes. A proof
successor must target the exact published aggregate statement after
independent review and publication.
