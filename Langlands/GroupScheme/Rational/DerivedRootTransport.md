# Actual root subgroup transport through a derived inclusion

This is an internal derivation toward the cover comparison for the simply
connected normalizer action. It uses the actual all-test orbit extensions and
subgroup functors in `Rational.RootSubgroup`. It is an intermediate construction;
the apartment-action theorem remains open.

## Closed ambient inclusions

Over an arbitrary scheme `B`, let `j : T → D`, let `d : D → G` be a closed
subgroup homomorphism, and let `b : T → Gm` be a character whose underlying
scheme map is quasi-compact, flat and surjective.
`IsOrbitExtension.exists_of_closedEmbedding` lifts every ambient extension of
the orbit of `d(g)` to an extension of the orbit of `g`. Indeed, base change of
the fpqc character is an effective epimorphism. Its commuting square against
the monomorphism `d` supplies a punctured-line factorization through `D`.
`AffineLine.exists_lift_of_unitInclusion` extends that factorization over zero.
Monicity reflects the orbit equation and the identity value at zero.
`subgroup_comap_closedEmbedding` consequently proves

```text
(subgroup (j ≫ d) b).comap d = subgroup j b.
```

The fpqc hypothesis is used for the punctured-line descent; this proof does not
assert that an arbitrary character has that property. The argument includes
nonreduced test schemes.

## A supplied central complement

For commutative group schemes `T`, `A`, `S` over `B`, maps `e : T → S` and
`c : A → S`, and an ambient map `i : S → G`,
`centralComplementProduct e c` is the actual product homomorphism
`T × A → S`, with value `e(t)c(z)` on every test scheme.
Assume its underlying scheme map is flat and surjective, assume `c ≫ i` is
central on all tests, and let `a` be a character of `S` with `c ≫ a = 0`.

`isOrbitExtension_centralComplement_iff` says that an affine-line map is an
extension for `(i,a)` exactly when it is one for `(e ≫ i,e ≫ a)`.
After precomposition with the base change of the product map, the two orbit
equations agree: the second factor acts trivially by centrality, and the
character is trivial on that factor. Flat surjective base change is an
epimorphism, so it reflects the equation. The reverse implication is ordinary
torus reparametrization. It follows that `subgroup_centralComplement` proves

```text
subgroup (e ≫ i) (e ≫ a) = subgroup i a.
```

The hypotheses do not assert surjectivity of `e` itself.
`precomp_ne_zero_of_centralComplement` also proves that `e ≫ a` is nonzero if
`a` is nonzero: vanishing on both factors would force vanishing after the
epimorphic product map, and hence vanishing on `S`.

## The actual derived inclusion

Now work over any field `k : Type u`. Supply split tori `T` and `S`, the above
central-complement data and flat-surjective product, an actual derived
inclusion `d : D → G` exhibiting `IsDerivedSubgroup d`, and a commuting square

```text
j ≫ d = e ≫ i.
```

For `a ≠ 0` vanishing on the complement, its restriction to `T` is nonzero by
the preceding lemma. `RelativeRoot.characterFpqc` therefore provides exactly
the fpqc hypothesis needed for the closed-inclusion comparison.
`subgroup_comap_derived` combines the two comparisons to prove

```text
(subgroup i a).comap d = subgroup j (e ≫ a).
```

The published `RelativeRoot.subgroup_le_derivedSubgroup` places the whole
ambient root subgroup for a nonzero character inside the actual derived
subgroup, on every test scheme. `subgroup_map_derived` uses this containment
and the image/preimage identity to obtain

```text
(subgroup j (e ≫ a)).map d = subgroup i a.
```

`derivedRootPointsEquiv` packages this equality and monicity of `d` as a
multiplicative equivalence on points over every test scheme. Its forward map
is exactly postcomposition by the supplied derived inclusion, as proved by
`derivedRootPointsEquiv_coe`.

Finally, when `G` is affine and locally of finite type, `A` is split and `a`
is an actual relative root of `i`, the published
`root_restrict_eq_zero_of_isCentral` supplies `c ≫ a = 0` and relative-root
membership supplies `a ≠ 0`. `derivedRelativeRootPointsEquiv` specializes the
construction with no extra vanishing premise, and its coe lemma again
identifies the original point map.

## Provenance and retained obligations

Every result here is derived from the imported actual-object definitions,
fpqc descent, affine-line closed-subgroup lifting, central root restriction
and derived containment. No additional assertion is attributed to the
literature. The product map and its flatness and surjectivity are supplied;
this module does not construct the derived tori or prove their product has
these properties. It does not assert a bijection of relative-root sets, nor
prove that every restricted character is an actual root in `D`. Root
reindexing, cover composition, valuation/apartment comparison and the final
normalizer-action equality remain separate obligations. No rational-point
surjectivity of an ambient map is assumed.
