# Harris's inverse limit over `m` and Lemma 2.8

Author: Worker 61. Built on
`Langlands.Cohomology.DivisibleSystem.InvariantLimit`
(`quotientInvariantsLimit`, `quotientInvariantsLimitToRepExtend`,
`quasiIso_quotientInvariantsLimitToRepExtend`), and through it on the base
module `DivisibleSystem` (`tower`, `obj`, `epi_projection`, `extendSystem`),
`…Invariants` (`toRepComplexes`, `smoothQuotientInvariants`),
`…InvariantTransition` (`quotientProjection`), `…ProPInvariants`
(`IsProPSubgroup`) and Worker 3's
`Langlands.Cohomology.ProPInvariants.Statement`
(`ProPInvariantSubcomplexStatement`). It also uses Worker 3's
`Langlands.Cohomology.InverseLimit.Statement`
(`FiniteCohomologyInverseLimitStatement`). Both statements are unproved and
appear only as hypotheses. From Mathlib it uses `limit.post`,
`limit.post_post`, `limMap`, `ShortComplex.mapHomologyIso`, the forgetful
functor `forget₂ (Rep k G) (ModuleCat k)`, `HomologicalComplex.extend`,
`extendHomologyIso`, `extend_exactAt` and `isoOfQuasiIsoAt`.

Everything is in the namespace `Langlands.Cohomology`. The declarations of
the sections "Inverse limits of ℓ-divisible systems" and "Harris's Lemma
2.8" are in `Langlands.Cohomology.DivisibleSystem`. Composition `f ≫ g` is
`f` followed by `g`.

## Homology of limits of complexes

`C` and `D` are abelian categories, `c` is a complex shape on `ι`, and
`F : C ⥤ D` is an additive functor preserving homology.

- `mapHomologicalComplexHomologyIso F c q`: the natural isomorphism
  `F.mapHomologicalComplex c ⋙ homologyFunctor D c q ≅ homologyFunctor C c q
  ⋙ F`. Its component at a complex `K` is
  `(K.sc q).mapHomologyIso F`, the isomorphism comparing the homology of the
  image under `F` with the image of the homology. Mathlib has this for short
  complexes (`ShortComplex.homologyFunctorIso`), not for homological
  complexes.
- `isIso_limit_post_homology_iff F c K q`: let `J` be a category such that
  `C` and `D` have limits of shape `J`, `F` preserves them and `F` reflects
  isomorphisms. Then for `K : J ⥤ HomologicalComplex C c`, the canonical
  comparison `limit.post K (homologyFunctor C c q)`, from the degree-`q`
  homology of `lim K` to the limit of the degree-`q` homologies, is an
  isomorphism if and only if the same comparison for
  `K ⋙ F.mapHomologicalComplex c` is. Proof: `F` applied to the first
  comparison, followed by the isomorphism `limit.post (K ⋙ H_q) F`, is
  `limit.post K (H_q ⋙ F)` (`limit.post_post`). Similarly, `H_q` applied to
  the isomorphism `limit.post K F'` (where `F' = F.mapHomologicalComplex c`),
  followed by the second comparison, is `limit.post K (F' ⋙ H_q)`. These two
  maps differ by `mapHomologicalComplexHomologyIso` and the limit of its
  components (checked on the limit projections). Then `F` reflects
  isomorphisms.

## Finiteness of representations

`k` is a commutative ring and `G` a monoid. "Finite" means that the
underlying type is finite.

- `finite_of_rep_iso e h`: if `X ≅ Y` in `Rep k G` and `X` is finite, so is
  `Y`.
- `finite_of_rep_isZero h`: a zero object of `Rep k G` is finite (its
  underlying module is a subsingleton).
- `finite_homology_extend_embeddingUpNat X h q`: if an `ℕ`-graded cochain
  complex `X` of representations has finite cohomology in every degree, then
  its extension by zero to `ℤ` along `ComplexShape.embeddingUpNat` has finite
  cohomology in every degree `q : ℤ`. For `q = n ≥ 0` its cohomology is
  isomorphic to that of `X` in degree `n` (`extendHomologyIso`); for `q < 0`
  the extension is exact at `q` (`extend_exactAt`), so its cohomology is
  zero.

## Inverse limits of ℓ-divisible systems

`C` is an abelian category and `T` an `ℓ`-divisible system in `C`, with
tower `T.tower : ℕᵒᵖ ⥤ C`.

- `epi_tower_map T f`: every transition map `T.tower.map f` is an
  epimorphism. This is the base module's `epi_projection` for the
  corresponding inequality of levels.
- `epi_tower_map_f T f q`: for a system of complexes, every transition map is
  an epimorphism in each degree `q`.

Assume `C` has limits of shape `ℕᵒᵖ`.

- `inverseLimit T`: the limit of the tower, `limit T.tower`.
- `inverseLimitHomologyComparison T q`: for a system of complexes, the
  canonical comparison `limit.post T.tower (homologyFunctor C c q)` from the
  degree-`q` homology of `inverseLimit T` to the limit over `m` of the
  degree-`q` homologies of the levels. `inverseLimitHomologyComparison_π`:
  followed by the projection to level `m` it is the map induced on homology
  by the limit projection to level `m`.
- `isIso_inverseLimitHomologyComparison_of_finite hS T hfin q`: let `R` be a
  ring and `T` an `ℓ`-divisible system of `ℤ`-graded cochain complexes of
  `R`-modules, with finite cohomology at every level and in every degree
  (`hfin`). Given `hS : FiniteCohomologyInverseLimitStatement R`, the
  comparison is an isomorphism in every degree `q`. The statement's
  surjectivity hypothesis on the transition maps is supplied by
  `epi_tower_map_f` (epimorphisms of modules are surjective).
- `isIso_inverseLimitHomologyComparison_rep hS T hfin q`: the same for an
  `ℓ`-divisible system of `ℤ`-graded cochain complexes of representations in
  `Rep k G`, given `FiniteCohomologyInverseLimitStatement k`. Proof: the
  forgetful functor to `ModuleCat k` preserves homology and limits of shape
  `ℕᵒᵖ` and reflects isomorphisms, so `isIso_limit_post_homology_iff`
  reduces the claim to the system of underlying complexes of modules. Its
  transition maps are surjective and its cohomology is finite.

## Harris's Lemma 2.8

The variables are those of the InvariantLimit module's section "The direct
limit": `K` is an `ℓ`-divisible system of `ℕ`-graded complexes of smooth
representations of `G` (`SmoothRep.{uR, uG, max w uR uG} R G`), `N : ℕ`, `ι`
a filtered preorder with an antitone family `H` of normal subgroups of finite
index (`hH`), and the hypotheses `hK` (surjectivity on invariants) and `hk`
(kernel orders are units in `R`).

- `quotientInvariantsInverseLimit N K H hH hK hk`: our `lim C_m^•`, the
  inverse limit of `quotientInvariantsLimit N K H hH hK hk` (our `C_m^•`), a
  `ℤ`-graded cochain complex in `Rep R G`.
- `quotientInvariantsInverseLimitComparison N K H hH hK hk hN q` (for `K`
  vanishing in degrees `q ≥ N`, `hN`): the map from the degree-`q`
  cohomology of `quotientInvariantsInverseLimit` to
  `lim_m H^q(K.toRepComplexes.extendSystem.obj m)`, the limit of the
  degree-`q` cohomologies of the underlying complexes of representations of
  `K` extended to `ℤ`. It is `inverseLimitHomologyComparison q`, followed by
  the limit over `m` of the maps induced on degree-`q` cohomology by the
  level-`m` components of (2.6), `quotientInvariantsLimitToRepExtend`.
- `isIso_quotientInvariantsInverseLimitComparison N K H hH hK hk hS hS' hP
  hR hN htriv hfin q`: let `G` be a topological group,
  `hS : ProPInvariantSubcomplexStatement.{uG, uR, max w uR uG}` and
  `hS' : FiniteCohomologyInverseLimitStatement.{uR, max w uR uG} R`. Assume
  every `H i` is pro-`p` (`hP`) with `p` a unit in `R` (`hR`), and `H i` acts
  trivially on the cohomology of `K.toRepComplexes.obj m` for every `m` and
  `i` (`htriv`). Assume also that this cohomology is finite in every degree
  (`hfin`). Then the comparison is an isomorphism in every degree `q : ℤ`.
  Proof: by `quasiIso_quotientInvariantsLimitToRepExtend`, (2.6) is a
  quasi-isomorphism at every level. Hence the cohomology of each `C_m^•` is
  isomorphic to that of the extended `K.toRepComplexes.obj m`, which is
  finite by `finite_homology_extend_embeddingUpNat`. So
  `isIso_inverseLimitHomologyComparison_rep` makes the first factor an
  isomorphism. The second factor is the limit of a natural transformation
  whose components are isomorphisms, so it is an isomorphism too.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.306: "The maps
j : C_m^•(U(ẽ)_F̄) → C_{m'}^•(U(ẽ)_F̄), for m > m', are all surjective by
hypothesis. It thus follows from Fact 1 bis that the system of complexes
{C_m^•(U(ẽ)_F̄)} satisfies a Mittag-Leffler condition [EGA III, Chap. 0,
Proposition 13.2.3], hence that Lemma 2.8. For every q, there is a canonical
isomorphism H^q(lim C_m^•(U(ẽ)_F̄)) ≅ lim H_c^q(U(ẽ)_F̄, Z/ℓ^mZ)." Worker 61
read this passage in the scanned original. Fact 1 bis, earlier in section
2, states that the cohomology groups with `ℤ/ℓ^mℤ` coefficients are finite.

Our rendering:

1. Harris derives the isomorphism from EGA's Mittag-Leffler criterion. We do
   not formalize that argument. We assume Worker 3's
   `FiniteCohomologyInverseLimitStatement` (hypothesis `hS'`), whose
   hypotheses are surjective transition maps and finite cohomology. The
   surjectivity holds for every `ℓ`-divisible system, so finiteness is the
   only remaining hypothesis (`hfin`).
2. The target of our comparison is the limit of the cohomologies of the
   abstract complexes `K.toRepComplexes.obj m` (extended to `ℤ`), not of
   Harris's compactly supported cohomology `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)`. His
   (2.3) identifies the two, and that is not formalized. Likewise `hfin` and
   `htriv` are stated for the abstract complexes.
3. Harris's isomorphism of Lemma 2.8 is "canonical" without a named map. Our
   map is the composite of the canonical comparison `limit.post` with the
   maps induced on cohomology by our (2.6). Harris's (2.7) combines (2.3)
   with the level-`m` map induced by (2.6) on cohomology; our second factor
   is the limit over `m` of the latter maps.
4. The theorem inherits the hypotheses of
   `quasiIso_quotientInvariantsLimitToRepExtend` at every level: Worker 3's
   unproved `ProPInvariantSubcomplexStatement` (`hS`), pro-`p`-ness (`hP`),
   trivial action (`htriv`) and the surjectivity and unit hypotheses `hK`
   and `hk`. Harris's specific family of subgroups is not constructed (see
   the InvariantLimit module).
5. The generic results (`mapHomologicalComplexHomologyIso`,
   `isIso_limit_post_homology_iff`, the finiteness lemmas, `inverseLimit`,
   `inverseLimitHomologyComparison` and its isomorphism criteria) are ours.

## Scope

The module defines the inverse limit of an `ℓ`-divisible system and the
comparison map of Lemma 2.8. It proves that the comparison is an isomorphism,
assuming Worker 3's two statements and the hypotheses above. All maps are in
`Rep R G`, so they are `G`-equivariant. It does not prove the Mittag-Leffler
argument or either statement. It does not identify the cohomology of `K`
with Harris's `H_c^q`. It does not treat smoothness or topology of the
inverse limit, or the passage to `ℤ_ℓ`- or `ℚ_ℓ`-coefficients.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
