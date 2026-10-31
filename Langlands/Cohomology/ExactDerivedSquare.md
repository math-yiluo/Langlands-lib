# Exact squares on actual derived categories

This module is an internal categorical construction for the Harris coefficient
framework. It extends Mathlib's exact-functor localization machinery to a square
with four separately chosen derived-category universes. It makes no new direct
assertion from Harris or Berkovich.

## Inputs and conventions

Let `A`, `B`, `C`, and `D` be abelian categories. Their object and morphism
universes are independent. For each category, a `HasDerivedCategory` instance is
explicit input, with independent localization universes `wA`, `wB`, `wC`, and
`wD`. These are Mathlib's actual unbounded derived categories of cochain
complexes indexed by the integers, obtained by inverting quasi-isomorphisms.

The four functors are

```text
F : A → B       R : B → D
G : A → C       S : C → D.
```

Each is additive and preserves finite limits and finite colimits. These
hypotheses allow its termwise complex functor to descend to the derived
category. The construction takes an ordinary natural isomorphism
`e : F ⋙ R ≅ G ⋙ S`. This generic module does not prove such an isomorphism for
arbitrary functors; geometric applications must supply their constructed
comparison.

## Construction and representative formula

`exactDerivedSquareIso F G R S e` is a natural isomorphism

```text
F.mapDerivedCategory ⋙ R.mapDerivedCategory
  ≅ G.mapDerivedCategory ⋙ S.mapDerivedCategory.
```

The implementation first maps `e` to complexes, using
`Functor.mapHomologicalComplexCompIso` to compare the separately mapped
composites with the mapped ordinary composites. It then postcomposes with
`DerivedCategory.Q` and descends the comparison by
`Localization.liftNatIso`. Associators match the composite lifting instances.
This builds the comparison on the derived category itself, rather than only on
its complex representatives. Its hom is proved to commute with integer shifts;
the four individual derived functors are triangulated by the imported exact
functor machinery.

`exactDerivedSquareIso_hom_app_Q_obj` computes its hom at every `Q.obj K`.
Writing `facF` for `F.mapDerivedCategoryFactors`, and similarly for the other
functors, the formula is

```text
Rᴰ(facF.hom_K) ≫ facR.hom_(F K) ≫ Q(e_K) ≫
  facS.inv_(G K) ≫ Sᴰ(facG.inv_K).
```

Here `e_K` is the actual termwise chain map induced by `e.hom`, not an extra
comparison supplied on complexes. The formula follows from the localization
lifting formula; the component maps of the complex composition comparisons
reduce to the corresponding termwise maps and identities.

## Single-degree recovery

`exactDerivedSquareIso_hom_app_single` works for every integer degree `q` and
every `M : A`. It computes the same comparison on
`(DerivedCategory.singleFunctor A q).obj M` by

```text
Rᴰ(singleF.hom_M) ≫ singleR.hom_(F M) ≫ singleD(e_M) ≫
  singleS.inv_(G M) ≫ Sᴰ(singleG.inv_M).
```

The `singleF`, `singleR`, `singleG`, and `singleS` maps are Mathlib's canonical
`mapDerivedCategorySingleFunctor` isomorphisms. Thus the construction recovers
the original ordinary square with the standard identifications of the two
composites on single-degree objects. The implemented proof uses the
representative formula, the termwise single-complex comparisons and naturality
of the localization factorization isomorphisms.

## Compatibility with transformations

For further exact functors `F' : A → B`, `G' : A → C`, comparisons `e` and `e'`,
and natural transformations `a : F ⟶ F'`, `b : G ⟶ G'`, assume the ordinary
square equation

```text
whiskerRight a R ≫ e'.hom = e.hom ≫ whiskerRight b S.
```

`exactDerivedSquareIso_naturality` proves its derived version, replacing `a`,
`b`, `R`, and `S` by their actual induced derived transformations and functors.
This is equality of natural transformations, so it holds on every derived
object and is compatible with every derived morphism. The proof uses faithful
precomposition with `Q`, the representative formula, cancellation of the
factorization isomorphisms and their naturality. The remaining chain-map
equality is checked degreewise using the supplied ordinary square equation.
The principal component formulas and this equation have reassociated variants.

## Provenance and scope

The construction reuses the pinned Mathlib modules
`Algebra.Homology.DerivedCategory.ExactFunctor`,
`CategoryTheory.Localization.Predicate`, and `Algebra.Homology.Additive`.
Its mathematical content is the universal property of actual localization and
the canonical termwise complex and single-degree comparisons. No additional
axiom or assumed derived compatibility is introduced. The ordinary comparison
and its transformation equation are explicit generic inputs; the later
small-etale application must use the existing proved source-change and
invariant-evaluation equations.

This module constructs no particular scheme, torsor, compact-support or global
cohomology functor, inverse limit, or Harris specialization. It is a reusable
prerequisite and does not complete the broad Harris implementation task.
