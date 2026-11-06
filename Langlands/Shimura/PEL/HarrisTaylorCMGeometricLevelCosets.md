# Target cosets on the geometric CM tower

Worker 57. This internal construction transports the published target-coset
equality on the exact CM moduli schemes through their actual change of base to
the algebraic closure of the original CM field. It constructs geometric scheme
maps from the existing quotient of transporter arrows, with both field and
original-scheme projection compatibilities. It also proves that a level element
acts by the identity on its own geometric level, a prerequisite for smooth
cohomology over sufficiently small levels.

The input is precisely the existing `CentralSimpleUnitaryData`, its CM-compatible
`HarrisSignatureCharts`, and the named tensor, Picard, duality, polarization,
finite Weil-transition, finite-adele comparison and torsion-etaleness premises.
The proposition `q : CMRepresentabilityStatement ...` retains the exact normalized
moduli presheaves, smoothness and projectivity. `chosenCMLevelRepresentation`
chooses witnesses of this precise proposition, and the existing Yoneda
construction determines their scheme transitions. No arbitrary tower is supplied.
All field, algebra and scheme carriers have universe zero, as in the existing
geometric tower. No existence of a sufficiently small level is asserted.

For genuine arrows `f, g : U ⟶ V`, the existing relation is
`f.hom.element⁻¹ * g.hom.element ∈ V.obj.subgroup`. It compares target right
cosets in the original opposite finite-adelic group. The existing
`SmallCMTargetCosetArrow D U V` is the quotient of exactly these arrows; neither
the relation nor the transporter convention is changed.

`cmGeometricOverTower_map_eq_of_target_coset` uses the published
`representedCMSchemeTower_map_eq_of_target_coset` for the chosen representation
witnesses. Equality of the underlying maps gives equality over `Spec F` by
faithfulness of `Over.forget (Spec F)`; the functor
`Over.pullback (cmGeometricFieldMap ...)` preserves that equality.
`cmGeometricSchemeTower_map_eq_of_target_coset` forgets to the
underlying geometric schemes. Thus no cancellation of the geometric projection,
which need not be a monomorphism, is used.

`cmGeometricTargetCosetMap` descends the actual geometric transporter map by
`Quotient.lift` using this equality. Its `mk` lemma is definitional: evaluating a
class at an actual representative recovers the original geometric scheme map.
`cmGeometricTargetCosetMap_over` proves that every such map commutes with the
structure maps to `Spec (AlgebraicClosure F)`. The theorem
`cmGeometricTargetCosetMap_projection` proves

```text
geometric coset map >> projection at V
  = projection at U >> original chosen coset map.
```

Both equations follow by quotient induction from the original over-category
morphism law and the naturality of `cmGeometricProjection`, respectively.

`cmGeometricSchemeTower_map_eq_id_of_mem` applies target-coset equality to an
endomorphism `f` whose translating element lies in the same level and to the
identity transporter. The required coset relation is subgroup closure under
inverse; the tower identity law finishes the proof. The quotient identity lemma
and `cmGeometricTargetCosetMap_comp` likewise retain the original identity and
composition of representatives. The latter does not define a quotient category
or a composition on arbitrary quotient arrows.

The construction uses only the published CM target-coset API and geometric tower
and ordinary functor, quotient and over-category laws. It makes no new claim from
external literature. It assumes no dual-existence, dual-geometry, coarse-rigidity
or dominant-unramified-etale criterion beyond the earlier named hypotheses in
`q`. It does not prove `q`, an arithmetic instance, existence of small levels,
transition etaleness, level-triviality of a nonconstant coefficient system, or a
smooth cohomology or Galois representation. Those remain separate obligations.
