# Actual radicals of compatible parabolic root presentations

This is a derived construction on the existing group-scheme and rational-Levi
interfaces. It constructs an actual radical for a supplied compatible parabolic
root presentation, identifies its image with that of every supplied geometric
radical, and calculates its complete relative-root support. It does not assert
existence of compatible presentations for all parabolics.

## Provenance and hypotheses

The generic comparison works over an arbitrary field `k : Type u`. The ambient
group `G` has an affine smooth structure morphism. A cocharacter `χ` has specified
representatives `p : P ⟶ G` of `Dynamic.parabolic χ` and `z : Z ⟶ G` of
`Dynamic.centralizer χ`, and the specified `Z` is connected reductive.
Representation means monicity and equality of the full subgroup functors on
every test scheme.

The construction uses the following existing results:

- `Dynamic.isGeometricUnipotentRadical_of_centralizer`, in
  `Dynamic/GeometricUnipotentRadicalReduction`, proves the full geometric
  greatestness predicate from connected reductivity of this centralizer.
- `unipotentFieldExtensionStatement`, in
  `Reductive/UnipotentFieldExtensionProof`, and
  `IsGeometricUnipotentRadical.isUnipotentRadical_of_unipotentFieldExtension`
  give ground-field greatestness for an affine ambient group.
- `IsUnipotentRadical.range_eq` compares greatest represented radicals.
- `Dynamic.unipotentToParabolic` constructs the actual inclusion of a represented
  identity-limit subgroup into a represented dynamic parabolic.
- `Dynamic.isIso_subgroupMultiplication` proves the compatible Levi-first
  multiplication isomorphism.
- `ParabolicRootPresentation.splitComponentCocharacter` and its defining laws
  give the cocharacter in the specified split component.
- `RelativeRoot.subgroupRelativeRoots_dynamicUnipotent` computes the complete
  actual tangent-weight support of a dynamic identity-limit subgroup.

These dependencies explain the internal provenance. No new literature assertion
is introduced. In particular, neither the universal dynamic-centralizer
reductivity statement nor the universal dynamic-radical statement is a
hypothesis of any result here.

## Comparing a supplied radical

For `n : U ⟶ P` satisfying
`LeviSubgroup.IsGeometricUnipotentRadical n`,
`Dynamic.mem_range_radical_iff_of_reductive_centralizer` proves, for every test
scheme `T` and `x : T ⟶ P.X`,

```
x ∈ range(n)(T) ↔ x ≫ p ∈ Dynamic.unipotent χ (T).
```

The proof constructs the canonical affine representative of the identity-limit
subgroup and factors it into `P`. The specified connected reductive centralizer
proves its geometric radical predicate. Affineness of `P` follows from the
closedness of its dynamic embedding into affine `G`. Preservation of unipotence
under field extension upgrades this predicate to ground-field greatestness.
The supplied radical has the same ground-field image by `range_eq`. Finally,
monicity of `p` identifies membership in this image with ambient identity-limit
membership.

`Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer` concludes

```
SubgroupFunctor.range (n ≫ p) = Dynamic.unipotent χ.
```

Both directions are proved on arbitrary test schemes. In the reverse direction,
the containment of the identity-limit subgroup in the dynamic parabolic first
supplies a lift through `p`, and the membership comparison supplies its radical
lift.

## The actual radical of a presentation

Let `r : ParabolicRootPresentation p l a`, with `p : P ⟶ G`, `l : M ⟶ P`
and `a : A.toGrp ⟶ M`. Assume `G` affine. All fields of the compatible
presentation are retained, including its realization witness. Write

```
ν = r.splitComponentCocharacter
χ = CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p.
```

`r.radicalHom` maps the actual affine group
`Dynamic.Affine.unipotentScheme χ` into the supplied `P`. Its law
`radicalHom_comp` identifies its composite with `p` with
`Dynamic.Affine.unipotentHom χ`. Thus this is a construction from the canonical
identity-limit representative and the literal supplied parabolic.

`isIso_subgroupMultiplication_radicalHom` proves that
`subgroupMultiplication l r.radicalHom` is an isomorphism of schemes over `k`.
It uses the exact parabolic and centralizer laws of `ν` and the compatible
dynamic multiplication theorem. This law requires no smoothness assumption on
`G`.

Assume in addition that `G` is smooth.
`isGeometricUnipotentRadical_radicalHom` proves the full semistandard geometric
radical predicate. The specified Levi's connected reductivity is already a
field of the compatible presentation. Its ambient inclusion represents exactly
the centralizer of `χ`, so the per-centralizer theorem applies.
`leviSubgroup_isGeometricUnipotentRadical_radicalHom` also proves the
rational-Levi predicate, namely greatestness both over the ground field and over
its algebraic closure. The comparison of the two interfaces uses the proved
field-extension theorem and the affineness of `P` supplied by the rational Levi.

For every other `n : U ⟶ P` satisfying the rational-Levi geometric radical
predicate, `range_comp_radical_eq` identifies its full ambient image with
`Dynamic.unipotent χ`.

Finally, `subgroupRelativeRoots_radical` proves

```
RelativeRoot.subgroupRelativeRoots (a ≫ l ≫ p)
    (SubgroupFunctor.range (n ≫ p))
  = positiveRelativeRoots (a ≫ l ≫ p) ν.
```

The split-torus hypothesis follows from the specified split component. After
rewriting by the ambient-image equality, the existing complete dynamic support
theorem applies. These are actual nonzero conjugation weights with a nonzero
tangent vector in the subgroup. No restriction to simple or indivisible roots
is made, and multipliable roots remain.

## Scope

The field universe and characteristic are arbitrary, and the ambient group need
not be split or quasisplit. The construction also allows rank zero. It assumes a
compatible presentation rather than proving its existence or independence.
Opposite-parabolic and common-Levi comparisons, representation finite length,
intertwiner convergence and rational continuation, and the Plancherel theorem
remain separate obligations.
