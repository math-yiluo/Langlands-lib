# The exponent-transfer step of Renard VII.1.3 from the geometric lemma

Author: Worker 1714. This is an internal conditional reduction for the proof of Renard
VII.1.3.

`MaximalLeviSupercuspidalExponentTransferReductionStatement` is the implication

```lean
RepresentedGeometricLemmaStatement.{u, v} →
  MaximalLeviContainmentStatement.{u} →
    MaximalLeviSupercuspidalExponentTransferStatement.{u, v}
```

and `maximalLeviSupercuspidalExponentTransfer_of_geometricLemma` proves it. So the
published `MaximalLeviSupercuspidalExponentTransferStatement.{u,v}` follows from two
statements:

- the represented geometric lemma `RepresentedGeometricLemmaStatement.{u,v}`
  (Renard VI.5.1);
- the structural statement `MaximalLeviContainmentStatement.{u}`: the Levi of a proper
  parabolic that contains a maximal Levi equals it.

Neither premise is proved here. All three propositions are the published declarations,
used unchanged.

## Provenance

The implication is internal: it has no separate counterpart in the literature. It is
the step of Renard's proof of VII.1.3 that passes from the parabolics `P` and `P'` to all
parabolics, recorded as a statement so that it can be reviewed on its own.

## Source

Renard, VII.1.3, proof (printed p.224, PDF p.230). Casselman's criterion is applied to
`π₁` because `r_Q^G π₁ = 0` for the other proper standard parabolics `Q`, by the
geometric lemma VI.5.3. Every parabolic is conjugate to a standard one (VII.2.1,
Remark 3). The Lean proof follows this argument for arbitrary actual parabolics. It
replaces "standard" by inner conjugation together with a reparametrization of the Levi
source.

## The proof

Fix the data of the transfer statement:

- `P = MN`, maximal and proper;
- `ρ` irreducible with all proper Jacquet modules zero;
- `i_P^G ρ` with a unitary central character `c`;
- `W` with an injective map into `i_P^G ρ` or a surjective map from it, whose exponents
  along the parabolics with Levi source `M` are positive.

Let `χ` be a normalized Jacquet exponent of `W` along a represented parabolic
`(q, lQ, rQ, a)` with root presentation `pres`.

1. If `q` is an isomorphism, `lQ` is one as well (`isIso_of_isIso_parabolic`).
   `W` inherits a unitary central character from `c`
   (`unitaryCentralCharacterOfInjective` or `unitaryCentralCharacterOfSurjective`).
   The published `normalizedJacquetExponent_mem_positiveCone_of_isIso` concludes.
2. Otherwise:
   1. The exponent makes `r_Q W` nontrivial
      (`nontrivial_jacquet_of_isNormalizedJacquetExponent`). Then `r_Q i_P^G ρ` is
      nontrivial (`nontrivial_jacquet_of_injective` or
      `nontrivial_jacquet_of_surjective`).
   2. `exists_range_le_innerIso_of_nontrivial_jacquet` applies the geometric lemma to
      `(P, Q)`. The identity of the value of `r_Q ∘ i_P` at `ρ` is nonzero. Hence, by
      `IsGluedFrom.exists_piece_intertwiningMap_ne_zero`, some piece `D i` is
      nontrivial at `ρ`. A piece with proper source parabolic `P' = M ∩ zQz⁻¹` vanishes
      at `ρ` (`GeometricLemmaIntersectionDatum.pieceFunctor_subsingleton_of_proper`),
      so `P'` is full. Then its Levi `M' = M ∩ zLz⁻¹` is full too, and the datum's
      Levi equation gives `M ⊆ zLz⁻¹` as subgroup functors
      (`GeometricLemmaIntersectionDatum.range_le_of_isIso_p'`).
   3. `q ≫ innerIso z` is a proper parabolic (`IsParabolicSubgroup.comp_iso`). The
      containment statement therefore gives `M = zLz⁻¹`. Both inclusions are closed
      immersions, so `isoOfIsRepresentedBy` gives `e : M ≅ L` with
      `e.hom ≫ lQ ≫ q ≫ innerIso z = l ≫ p`.
   4. By `isNormalizedJacquetExponent_comp_innerIso_iso_comp_iff`, `χ` is an exponent
      of `W` along `(q ≫ innerIso z, e.hom ≫ lQ, rQ, a ≫ e.inv)`. That datum has Levi
      source `M` and composite `l ≫ p`. Its presentation is
      `(pres.compAmbientIso (innerIso z)).leviIsoComp e`. The hypothesis on `W` puts
      the real part of `χ` in that presentation's positive cone. By
      `positiveCone_leviIsoComp` and `positiveCone_compAmbientIso`, this is the
      positive cone of `pres`.

## Scope

The statement's universes `u` (field) and `v` (carrier of `ρ`) are kept. `W` has
carrier universe `max u v`. The geometric lemma is used at universes `u, v`, and the
containment statement at the field universe. No other hypothesis is added. The
irreducibility of `ρ` is not used.
