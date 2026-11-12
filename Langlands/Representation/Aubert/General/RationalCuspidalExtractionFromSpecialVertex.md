# Proper-induction exclusion and cuspidal extraction from one special vertex

Worker 4358. This module reduces the rational cuspidal Jacquet-factor
extraction target
`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalJacquetFactorExtractionStatement.{u, v}`
to one published proposition:
`Langlands.CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u}`
(module `RationalCuspidalInertiaDecompositionReduction`). That proposition
provides a special vertex with its compact, basis and finite Cartan covering
properties for every connected reductive group. It is not proved here, so this
module does **not** prove the extraction target. It also derives the same
conclusion from
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}`,
through the published `rationalSpecialVertexCompactInputs_of_jointBasis`.

The published route through Renard VI.3.5
(`rationalCuspidalExtractionInputs_of_wholeStatement`, module
`RationalLeviInductionExclusionFromWhole`) needs the whole-category splitting.
Its proof, in the draft of Task 4386, needs both the special-vertex inputs and
the fixed-level finiteness (KF) of Renard VI.3.4. The route here needs only the
special-vertex inputs. It does not use (KF), the whole-category splitting or the
compact-restriction category decomposition.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The
relevant passages are:

- Lemme VI.5.2, printed p.173 / PDF p.179: no irreducible subquotient of a
  proper parabolic induction is supercuspidal;
- the theorem of VI.2.1, printed pp.137–139 / PDF pp.143–145: cuspidality and
  compact restriction to the norm kernel;
- IV.1.6, printed pp.94–95 / PDF pp.100–101: compact representations are
  semisimple, and their simple objects are projective.

## Generic results

The group `G` is locally compact, nonarchimedean, Hausdorff and totally
disconnected. `N` is an open normal subgroup.

- `hom_eq_zero_of_isCuspidalFor_of_induction` (first adjointness). Let a
  family `P k = M k ⋉ U k` be given, a member `k` with unimodular `U k`, and a
  smooth `σ` of `M k`. Every intertwiner from an object that is
  `IsCuspidalFor` the family into the normalized induction of `σ` along `k`
  is zero. Its image under the published `FirstAdjointness.equiv` lands in
  maps out of the Jacquet module along `k`, which is subsingleton by
  cuspidality, and the equivalence is injective. The argument is the one in
  the published `no_cuspidal_subquotient_of_induction_splitting`, stated
  without a splitting.
- `compactRestrictionSubrepresentation_ne_bot_of_isSubquotient`. Let `τ` be
  nontrivial, with compact smooth-dual coefficients on `N`, and let `τ` be an
  actual subquotient of `V`. Then the published
  `compactRestrictionSubrepresentation N V` is not `⊥`. This is the ambient
  subrepresentation of vectors of `V` whose coefficients on `N` have compact
  support. The proof writes the subquotient as `C ↪ V` and `C ↠ τ`
  (`SmoothRep.isSubquotient_iff_exists`) and restricts the surjection to `N`.
  The restriction of `τ` to `N` has compact coefficients, so it is projective
  (published `CompactCoefficient.projective_of_compactCoefficients`, the
  projectivity of IV.1.6). It therefore has a section `s` into the restriction
  of `C`. For a nonzero vector `w` of `τ`, the vector `ι (s w)` of `V` is
  nonzero. It is a compact-coefficient vector by the published
  `range_le_compactCoefficientVectors`.
- `compactRestrictionProperty_compactRestrictionSubrepresentation`. The
  subrepresentation `compactRestrictionSubrepresentation N V`, as an actual
  smooth `G`-representation, has compact smooth-dual coefficients on `N`. This
  is the published `hasCompactSmoothDualCoefficients_subrepresentation_of_le`.
  Its compact-open cofinality input is the published
  `CuspidalSupport.openSubgroup_compactOpenCofinal` for the open subgroup `N`.
- `not_isSubquotient_of_compactRestriction`. Let `Cusp` be any predicate on
  smooth `G`-representations, and suppose compact restriction to `N` implies
  `Cusp`. Suppose every intertwiner from a `Cusp` object into `V` vanishes. Then
  a nontrivial `τ` with compact restriction to `N` is not a subquotient of
  `V`. Indeed, the inclusion of `compactRestrictionSubrepresentation N V` into
  `V` comes from a `Cusp` object, so it vanishes and the subrepresentation is
  `⊥`. This contradicts the previous result.

## The exclusion inside a standard Levi

`pointLeviStandardInductionCuspidalExclusion_of_specialVertexInputs` proves the
published `PointLeviStandardInductionCuspidalExclusion.{u, v} i ν hInter hG hi
hν hM hU`, defined in module `RationalCuspidalExtractionInputs`, from
`hSV : RationalSpecialVertexCompactInputsStatement.{u}`. Its other inputs are
the displayed data of that definition and `StandardCocharacterStatement.{u}`.
Fix a simple-root subset `J`, a proper subset `K` of `J`, a smooth `ρ` on the
fine Levi inside `levi i ν J`, and an irreducible inside-Levi cuspidal `τ` on
`levi i ν J`. The carrier universe is `max (u + 1) v`. Let `V` be the actual
normalized induction of `ρ` inside `levi i ν J`. We show that `τ` is not a
subquotient of `V`. Irreducibility of `τ` is used only through its
nontriviality.

1. The represented standard Levi scheme `L = Standard.leviScheme i ν (rootSet i
   ν J)` is set up exactly as in the published
   `hasLeviCuspidalRemainderSplitting_of_wholeStatement`. Its connected
   reductivity comes from `standardLeviScheme_isConnectedReductive` and its
   torus `iL` is maximal split. Genericity of `ν` comes from
   `standardLeviStandardFamilies`. The point topology of `L` is locally compact,
   nonarchimedean, Hausdorff and totally disconnected, and its unipotent
   subgroups are closed. Its relative root system is the published
   `GroupScheme.relativeRootSystem`, as in
   `pointLeviStandardInductionCuspidalExclusion_of_wholeStatement`.
2. The published `rationalLeviCuspidalityTransport` identifies, for every
   smooth `B` on `levi i ν J`, cuspidality of the pullback of `B` along
   `e = leviRationalPointHomeomorph i ν J` with `IsLeviCuspidal B`. Cuspidality
   of the pullback is `IsCuspidal` for the intrinsic standard family of `L`.
3. On the literal side, every intertwiner from an `IsLeviCuspidal` object into
   `V` vanishes. This is `hom_eq_zero_of_isCuspidalFor_of_induction` at the
   proper subset `⟨K, hK⟩`. The unimodularity is the published
   `isUnimodularModulus_standardUnipotent_in_levi`.
4. This vanishing transfers to the intrinsic side. Let `C'` be intrinsically
   cuspidal and `f' : C' ⟶ pullback e V`. Then `pullback e.symm C'` is
   `IsLeviCuspidal`, by step 2 and the counit isomorphism of the published
   `SmoothRep.pullbackEquivalence e`. Its map to `V`, composed with the inverse
   unit isomorphism, therefore vanishes. Both isomorphisms have the identity as
   their linear map, so `f' = 0`.
5. `hSV` applied to `L, iL, ν` gives a special vertex `D, x` with its four
   properties. The published `rationalCuspidalCompactRestriction` (VI.2.1
   (a) ⇒ (c)) gives compact coefficients of the pullback of `τ` on
   `Plancherel.rationalCommonNormKernel L`. That kernel is open
   (`Plancherel.isOpen_rationalCommonNormKernel`) and normal.
6. `not_isSubquotient_of_compactRestriction` applies with `N` this kernel and
   `Cusp` intrinsic cuspidality. The published `rationalCompactRestrictionCuspidal`
   (VI.2.1 (c) ⇒ (a), unconditional) supplies the implication from compact
   restriction to cuspidality, and step 4 supplies the Hom vanishing. So the
   pullback of `τ` is not a subquotient of the pullback of `V`. This contradicts
   `IsSubquotient.pullback e` applied to the hypothesis.

## Assembly

- `rationalCuspidalExtractionInputs_of_specialVertexInputs` proves the
  published `RationalCuspidalExtractionInputsStatement.{u, v}` from `hSV`. It
  has the binders of the target. Its first conjunct is Worker 174's published
  unconditional `exists_pointInducedJacquetGeometricFiltration`. The second
  conjunct is the exclusion above.
- `rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs` composes it
  with the published `rationalCuspidalJacquetFactorExtraction_of_inputs`. It
  concludes `RationalCuspidalJacquetFactorExtractionStatement.{u, v}`.
- `rationalCuspidalJacquetFactorExtraction_of_jointBasis` derives the same
  conclusion from `JointSpecialCompactBasisExistenceStatement.{u}`.
- The entry declaration `rationalCuspidalJacquetFactorExtractionOfSpecialVertexInputs`
  is a `def` whose type is the implication
  `RationalSpecialVertexCompactInputsStatement.{u} →
  RationalCuspidalJacquetFactorExtractionStatement.{u, v}`.

## Scope

The field universe `u` and the carrier universe `v` are independent. No
characteristic, rank, admissibility, finite-length or finite-generation
restriction is added. No published statement or imported pair is changed. The
special-vertex inputs (equivalently, for this purpose, the joint basis
existence of Task 4169, `8c39faa0-2a70-4fc4-a027-914987aba924`) remain the only
unproved input. Once one of them is proved, the target is a direct application
of `rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs` or
`rationalCuspidalJacquetFactorExtraction_of_jointBasis`. Development
compilation reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The proof of the exclusion is an alternate route to Renard's proof of
VI.5.2. Renard removes the supercuspidal part of `i_P ρ`, which he obtains from
the VI.3.5 splitting. The proof here lifts the compact restriction of the given
subquotient into the induced object. It then uses the subrepresentation of
compact-restriction vectors, which is cuspidal by VI.2.1, as that part.
