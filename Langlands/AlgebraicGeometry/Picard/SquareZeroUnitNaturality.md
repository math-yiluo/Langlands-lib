# Actual unit boundaries for nested square-zero thickenings

This module treats actual scheme morphisms `i : Y ⟶ X` and `j : Z ⟶ Y`
in an arbitrary common universe `u`. The unit-sequence and boundary
constructions assume that `i` and `j ≫ i` are closed immersions and that
their actual ideal sheaves satisfy
`hi : i.ker ^ 2 = ⊥` and `hji : (j ≫ i).ker ^ 2 = ⊥`.
There is no separate closed-immersion or square-zero hypothesis on `j`.
There are no properness, noetherianity, affineness, or field hypotheses.
All the sheaves on the ambient scheme are on its small Zariski site.

The construction compares the published actual square-zero unit sequences
on the common scheme `X`. Write `I = kernelModule i` and
`J = kernelModule (j ≫ i)`. For every open `U` of `X`, their sections are
the kernels of the actual structure maps to sections on `i⁻¹U` in `Y`
and `(j ≫ i)⁻¹U` in `Z`, respectively.

`quotientStructureMap i j` is the morphism of ring presheaves on `X`
obtained by whiskering the actual structure morphism `j.c` along
`(Opens.map i.base).op`. It needs no immersion hypothesis.
`kernelModuleMap i j : I ⟶ J` sends a section to the same section of
`O_X`. Membership in `I` implies membership in `J` because the composite
structure map applies `j`'s structure map to zero. The additive,
restriction, and module compatibility laws follow from retaining the
same section. `kernelModuleMap_app` records this value reflexively.
For every degree `n`, `idealCohomologyMap i j n` is the underlying
additive homomorphism of the actual module-cohomology map
`(Modules.DerivedSections.cohomology X n).map (kernelModuleMap i j)`.

`quotientUnitsMap i j` applies the published `unitsSheafMap` to
`quotientStructureMap i j`. Thus it maps the units of the pushed-forward
structure sheaf of `Y` to those of `Z`, with both sheaves on `X`.
It has the following compatibility with the published actual unit maps:

```text
unitsReduction i ≫ quotientUnitsMap i j = unitsReduction (j ≫ i)
(toAbSheaf X).map (kernelModuleMap i j) ≫ schemeOneAdd (j ≫ i) hji
  = schemeOneAdd i hi.
```

These are `unitsReduction_comp` and `kernelModuleMap_oneAdd`.
The first equation needs no immersion or nilpotence assumptions.
The second expresses that both maps send the same kernel section `a`
to the same actual unit `1+a`. The proofs use sheaf, natural
transformation, additive-group, and unit extensionality.

`sequenceKernelMap`, `sequenceQuotientMap`, and `sequenceMiddleMap`
give these maps with the precise endpoints of the published short
complexes `schemeUnitSequence i hi` and
`schemeUnitSequence (j ≫ i) hji`. The middle map is the identity on
the common actual sheaf of units of `X`. The two commuting-square
lemmas `sequenceKernelMap_comm` and `sequenceQuotientMap_comm` check
the component formulas. `unitSequenceMap` packages them as a morphism
of those actual short complexes.

Let `Hⁿ` denote Mathlib's actual Ext-defined abelian-sheaf cohomology,
`q = quotientUnitsMap i j`, and `k = kernelModuleMap i j`.
For any natural degree `n` and any
`a : Hⁿ((schemeUnitSequence i hi).X₃)`, `delta_naturality` says

```text
δ_(j≫i)(Hⁿ(q)(a)) = Hⁿ⁺¹((toAbSheaf X).map k)(δ_i(a)).
```

Here both connecting maps are exactly Mathlib's `Sheaf.H.δ` of the
published `schemeUnitSequence_shortExact` witnesses. The proof applies
`Sheaf.H.δ_naturality` to `unitSequenceMap`; it does not replace the
boundary by an unspecified homomorphism.

`pushedBoundaryMap i hi n` composes `δ_i` with the published
`idealCohomologyAddEquiv i (n + 1)`, giving a map from the quotient-unit
cohomology on `X` to the actual module cohomology of `I`.
The lemma `pushedBoundaryMap_naturality` states

```text
pushedBoundaryMap (j ≫ i) hji n (Hⁿ(q)(a))
  = idealCohomologyMap i j (n + 1) (pushedBoundaryMap i hi n a).
```

After `delta_naturality`, this is precisely the published coefficient
naturality of the unchanged
`Modules.AbelianSheafComparison.HAddEquiv`.

To express the quotient term on its own scheme, let `e_i,n` and
`e_ji,n` denote the published additive equivalences
`nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n` and
`nilpotentUnitsCohomologyPushforwardEquiv (j ≫ i) ⟨2, hji⟩ n`.
Their sources are the respective pushed-forward unit cohomology
groups on `X`, and their targets are `unitCohomology Y n` and
`unitCohomology Z n`. The definition `quotientUnitCohomologyMap` is
the explicit additive homomorphism

```text
qₙ = e_ji,n ∘ Hⁿ(q) ∘ e_i,n⁻¹.
```

It is defined by transport through these existing equivalences.
`boundaryMap_naturality` proves, for every `y : unitCohomology Y n`,

```text
boundaryMap (j ≫ i) hji n (qₙ(y))
  = idealCohomologyMap i j (n + 1) (boundaryMap i hi n y).
```

The proof expands the published `boundaryMap`, cancels the consecutive
equivalence and its inverse, and applies `pushedBoundaryMap_naturality`.
`quotientUnitCohomologyMap_reductionMap` similarly proves

```text
qₙ(reductionMap i hi n x) = reductionMap (j ≫ i) hji n x
```

for every `x : unitCohomology X n`. After cancelling the comparison,
this is cohomology functoriality applied to `unitsReduction_comp`.
Finally, `oneAddMap_naturality` proves

```text
oneAddMap (j ≫ i) hji n (idealCohomologyMap i j n a)
  = oneAddMap i hi n a
```

for every `a : idealCohomology i n`. The proof uses the published
inverse `HAddEquiv` coefficient naturality, cohomology functoriality,
and `kernelModuleMap_oneAdd`. All these equations include degree zero.

This is an internal derived construction from the published actual
structure kernels, unit sheaves, square-zero unit short exact sequence,
nilpotent topological pushforward comparison, and module/abelian-sheaf
cohomology comparison, together with Mathlib's connecting-map
naturality. No additional external mathematical assertion is assumed.
The claims are additive. The module does not identify the transported
`qₙ` with an independently defined intrinsic reduction map for `j`,
establish general scheme base change, assert scalar stability of a
boundary image, compare with a separately defined module-derived
connecting map, classify line bundles, or prove Picard representability.
