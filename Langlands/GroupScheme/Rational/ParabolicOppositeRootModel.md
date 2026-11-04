# Opposite dynamic models with the specified Levi

This derived construction reverses the split-component cocharacter of an
existing compatible parabolic root presentation. It constructs a closed
decomposition model with the literal supplied Levi, proves both geometric
radical predicates, and identifies the complete root intersection of supplied
positive and negative radicals. Algebraic parabolicity of the negative dynamic
group is not asserted here.

## Hypotheses and provenance

Let `k : Type u` be an arbitrary field, let `G` have an affine structure
morphism, and let

```
r : ParabolicRootPresentation p l a
p : P ⟶ G,   l : M ⟶ P,   a : A.toGrp ⟶ M.
```

All compatibility fields of the presentation are retained, including its
realization witness. In particular, `M` is connected reductive and `a` is its
specified split component. Write

```
ν = r.splitComponentCocharacter
χ⁻ = CommGroupScheme.groupHom (-ν) ≫ a ≫ l ≫ p.
```

The construction uses the canonical affine representatives of
`Dynamic.parabolic χ⁻` and `Dynamic.unipotent χ⁻`. The equality
`groupHom_neg_comp_eq_oppositeCocharacter` identifies parameter reversal with
inversion on the multiplicative group.
`Dynamic.centralizer_inverseCocharacter` shows that this reversal preserves the
centralizer on every test scheme. Together with the defining centralizer law
of `ν`, this proves `levi_eq_neg_splitComponentCocharacter`:

```
SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χ⁻.
```

These are internal consequences of the imported dynamic and
compatible-presentation interfaces. No new literature assertion or universal
centralizer-reductivity hypothesis is introduced.

## The closed decomposition model

`oppositeDecompositionModel` has the canonical affine negative dynamic group
as its `parabolic`, the original `M` as its `levi`, and the canonical affine
negative identity-limit group as its `unipotent`. The latter two inclusions
are constructed by factoring their represented subgroup functors into the
represented negative dynamic parabolic.

The model proves all fields of `SubgroupFunctor.ClosedDecompositionModel`:
the ambient images represent exactly the three displayed subgroup functors;
the three inclusions are closed; and Levi-first multiplication is an
isomorphism of schemes over `k`. On every test scheme, the unipotent subgroup
is normal in the parabolic subgroup, it is complementary to the Levi, and the
parabolic is the set product of the Levi and unipotent subgroups.

The exact composite law `oppositeDecompositionModel_leviHom_comp` is

```
r.oppositeDecompositionModel.leviHom ≫
    r.oppositeDecompositionModel.parabolicHom = l ≫ p.
```

Closedness of the Levi follows from its original closed ambient embedding
and closedness of the negative parabolic embedding. Closedness of the
unipotent inclusion follows in the same way from its canonical dynamic
embedding. The multiplication isomorphism and the all-test decomposition
follow from the existing compatible dynamic multiplication and complement
theorems. These results require no smoothness assumption on `G`.

## Geometric radicals and arbitrary representatives

For the remaining results assume also that `G` is smooth.
`isGeometricUnipotentRadical_oppositeModel` applies
`Dynamic.isGeometricUnipotentRadical_of_centralizer` with the specified
connected reductive `M` and its exact ambient embedding. Thus the constructed
negative identity-limit group satisfies the full semistandard geometric
radical predicate.

`leviSubgroup_isGeometricUnipotentRadical_oppositeModel` also proves the
rational-Levi predicate: greatestness over both the ground field and its
algebraic closure. It uses the proved preservation of unipotence under field
extension and the affineness of the canonical negative dynamic representative.

More generally, let `q : Q ⟶ G` represent `Dynamic.parabolic χ⁻`, and let
`v : V ⟶ Q` satisfy `LeviSubgroup.IsGeometricUnipotentRadical v`.
`range_comp_oppositeRadical_eq` proves

```
SubgroupFunctor.range (v ≫ q) = Dynamic.unipotent χ⁻.
```

This is equality on every test scheme. It follows from the generic
per-centralizer radical comparison in `ParabolicRootRadicals`, with
reductivity supplied by the original `M`. A representative of the negative
dynamic parabolic is an explicit hypothesis of this comparison.

`subgroupRelativeRoots_oppositeRadical` then gives

```
RelativeRoot.subgroupRelativeRoots (a ≫ l ≫ p)
    (SubgroupFunctor.range (v ≫ q))
  = positiveRelativeRoots (a ≫ l ≫ p) (-ν).
```

The split-torus hypothesis comes from the specified split component.
Rewriting the ambient image allows the existing complete tangent-weight
support theorem for dynamic identity-limit groups to apply.

## The complete common-Levi root intersection

Let `r' : ParabolicRootPresentation p' l' a` be a second presentation with the
same specified `M` and `A`, and assume the exact ambient equality
`hM : l ≫ p = l' ≫ p'`. Let `n : U ⟶ P` be any supplied positive geometric
radical, and let `v : V ⟶ Q` be any supplied geometric radical of a
representative of the negative dynamic parabolic of `r'`. Put
`η = r'.splitComponentCocharacter`.

`intertwiningRelativeRoots_commonLevi` proves

```
RelativeRoot.intertwiningRelativeRoots (a ≫ l ≫ p)
    (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q))
  = {α | α ∈ relativeRoots (a ≫ l ≫ p) ∧
      0 < latticePairing A α ν ∧ latticePairing A α η < 0}.
```

The proof rewrites both supplied radical images using their exact dynamic
comparison laws, rewrites the second ambient Levi embedding by `hM`, and
applies `RelativeRoot.intertwiningRelativeRoots_dynamic`. It retains every
actual relative root in the two supports, including multipliable roots.

## Scope

The universe and field characteristic are arbitrary; nonsplit ambient groups
and rank zero are allowed. The results assume existing compatible
presentations and do not prove their general existence or independence.
Algebraic parabolicity of the negative model, the comparison with any
independently specified opposite algebraic parabolic, and the analytic
intertwiner and Plancherel conclusions remain separate obligations.
