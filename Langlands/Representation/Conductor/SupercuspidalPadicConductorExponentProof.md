# Proof of the JPSS conductor theorem for supercuspidal representations over p-adic fields

Module `Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof`.

`Langlands.Conductor.supercuspidalPadicConductorExponent` proves the published
[`Langlands.Conductor.SupercuspidalPadicConductorExponentStatement`](SupercuspidalPadicConductorExponentStatement.md)
at independent universes `uF` (the field) and `uV` (the carrier of `π`). It adds no
hypothesis. It holds for every prime `p`, every p-adic field `K`, every choice of the
measurable and Borel structures that the statement binds, every normalization
`(q, abv, ϖ, ψ, ν)`, every rank `n + 1`, and every representation `π` with
`IsGeneric ψ n π` and `IsSupercuspidal π`. The conclusion gives `c : ℂˣ` and `m : ℕ` with

- `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`,
- `IsNewvectorConductor π m`, and
- `Module.finrank ℂ (levelFixedVectors π m) = 1`.

Mathematically this is Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), §(5.1), Théorème (i)-(iii),
printed p. 211 (literature ID `jpss-1981-conductor`), for supercuspidal `π`. The proof
does not use the generic JPSS 1983 (9.4)/(8.4) generation statement, and it does not
use `Conductor.EssentialVectorExistence`.

## Imported results

The four general inputs are published proofs for every nonarchimedean local field. They
are used at `F = K.Carrier`:

- `Whittaker.mirabolicRestrictionInjectivity` (module
  `Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityProof`) proves
  `MirabolicRestrictionInjectivityStatement`. For a nonzero Whittaker functional, the
  restriction of the Whittaker model to the mirabolic subgroup is injective.
- `Conductor.essentialDualComparison` (module
  `Langlands.Representation.Conductor.EssentialDualComparisonProof`) proves
  `EssentialDualComparisonStatement` (JPSS 1981, (5.3), printed p. 213). Let `π` be a
  generic representation of `GL_r(F)` with `r = k + 2 ≥ 2`. Let `W` be an essential
  vector of the model of a nonzero `ψ`-Whittaker functional `ℓ` of `π`. Let `W'` be an
  essential vector of the model of the dual functional of `inverseTransposePullback π`
  (a `ψ̄`-Whittaker functional). Let `c q^(-ms)`, with `m : ℤ`, be the epsilon factor of
  `π` against the trivial character of `GL_1`. Put `W̃ = dualFunction W`, so
  `W̃(g) = W(w_r · ᵗg⁻¹)`, where `w_r` is the long Weyl element. Then some constant `C`
  satisfies `W̃(g) = C · W'(g · a)` for every `g ∈ GL_r(F)`. Here
  `a = rankInclusion 1 (scalar (ϖ^m)) = diag(ϖ^m, …, ϖ^m, 1)`. The identity is about
  the transformed function `W̃`, not about `W` itself. The transform `dualFunction`
  uses the long Weyl element and the inverse transpose, and it turns `ψ`-Whittaker
  functions into `ψ̄`-Whittaker functions.
- `Conductor.conductorMinimalityStatement` (module
  `Langlands.Representation.Conductor.ConductorMinimalityProof`) proves
  `ConductorMinimalityStatement`. A nonzero level-`u` fixed vector of the model satisfies
  `m ≤ u`. At `u = m` it satisfies Jacquet's identity scaled by a constant.
- `Conductor.trivialCharacterEpsilon` (module
  `Langlands.Representation.Conductor.TrivialCharacterEpsilonProof`) proves
  `TrivialCharacterEpsilonStatement`. An epsilon factor `(c, m)` with `m : ℤ` exists
  against the trivial character of `GL_1`.

The only supercuspidal input is the new helper theorem
`SupercuspidalPadic.exists_isEssentialVector` of
[`SupercuspidalPadicEssentialExistence`](SupercuspidalPadicEssentialExistence.md). For
a generic supercuspidal `π` of `GL_(n+2)(K)` and any `IsJacquetNormalization`, it gives an
essential vector in every nonzero Whittaker model.

## Proof

After introducing the binders, the proof installs the canonical topology, valuative
relation and local-field structure of `K` with `let`. Then it splits on the rank.

**Rank one (`n = 0`).** The published `conductorExponent_rankOne_of_localTate` (module
`Langlands.Representation.Conductor.RankOneTateReduction`) gives the conclusion for every
generic `π` of `GL_1`. It is applied to the published `GodementJacquet.localTateConductor`
(module `Langlands.Representation.GodementJacquet.LocalTateConductorProof`), which is
Tate's local theory. Supercuspidality is not needed here.

**Rank `k + 2` (`n = k + 1`).** This is the proof of the published
`Conductor.conductorExponentStatement_of` (module
`Langlands.Representation.Conductor.EssentialConductorReduction`). Its general existence
hypothesis is replaced by `exists_isEssentialVector`, used only for `π` and for its
inverse-transpose dual. Both of these are supercuspidal. The proof of
`essentialVectorLevelStatement_of` is inlined.

1. Give `GL_(k+1)`, `N_(k+1)` and `N_(k+1) \ GL_(k+1)` their Borel σ-algebras. Then
   `h : IsJacquetNormalization q ψ abv ϖ (unipotentQuotientHaar K.Carrier k)` is built
   from the statement's hypotheses and the published `unipotentQuotientHaar_isCompatible`
   (module `Langlands.Representation.RankinSelberg.UnipotentQuotient`).
2. `trivialCharacterEpsilon` gives `(c, m)` with `m : ℤ` and the epsilon relation `hε`.
   `hπ.2.2` gives a nonzero Whittaker functional `ℓ`. `exists_isEssentialVector` gives
   an essential vector `w` of the model of `ℓ`. The vector `w` is the unique essential
   vector, by the published `IsEssentialVector.eq_of_mirabolicRestrictionInjective` and
   mirabolic restriction injectivity.
3. The dual side uses these results:
   - `h.scaleNegOne`, a normalization for `ψ.scale (-1)` (module
     `Langlands.Representation.Conductor.EssentialDualSetup`);
   - `isGeneric_inverseTransposePullback` and `scaledDualFunctional_ne_zero` (same
     module);
   - `GeneralLinear.isSupercuspidal_comp_inverseTranspose` (module
     `Langlands.Representation.Classification.SupercuspidalInverseTranspose`).
   These give that `inverseTransposePullback π` is generic and supercuspidal, with the
   nonzero functional `scaledDualFunctional ψ π ℓ`. So `exists_isEssentialVector`
   gives a dual essential vector `w'`.
4. `essentialDualComparison`, applied to `w`, to `w'` and to `hε`, gives a constant `C`
   with `dualFunction (k + 1) w g = C · w'(g · rankInclusion 1 (scalar (ϖ^m)))` for
   every `g`. The essential vectors `w` and `w'` are fixed by the integral Jacquet
   mirabolic subgroup, by the published
   `IsEssentialVector.right_jacquet_invariant` (module `EssentialConductorReduction`;
   it uses mirabolic restriction injectivity and `essentialIntegralLastRowSupport`). The
   published `right_level_toNat_invariant_of_dual_comparison` (module
   `Langlands.Representation.Conductor.JacquetDualInvariance`) then gives `0 ≤ m`. It is
   applied together with `hasJacquetDualComparison_of_rankInclusion_scalar` and
   `right_invariant_central_translate` (module `EssentialDualSetup`). Write `m = a` with
   `a : ℕ`. This is JPSS 1981, (5.1)(i).
5. The published `mem_levelFixedVectors_of_rankInclusion_dual_comparison` (module
   `EssentialDualSetup`) shows that `w` is fixed at level `a`. Its inputs are the same
   comparison and `IsEssentialVector.mem_jacquetFixedVectors`. This is (5.1)(ii), first
   clause.
6. Let `P` be the L-polynomial of `w`. Minimality, at `P` and `(c, a)`, says that no
   nonzero vector is fixed at a level `b < a`. It also says that every level-`a` fixed
   vector satisfies a scaled Jacquet identity. By uniqueness of `w`, the published
   `exists_eq_smul_of_mem_levelFixedVectors` (module
   `Langlands.Representation.Conductor.EssentialScaledUniqueness`) makes each such vector
   a multiple of `w`. So `IsLevelLine (modelRepresentation π ℓ) a w` holds.
7. The published `isNewvectorConductor_and_finrank_of_essential` (module
   `Langlands.Representation.Conductor.EssentialConductorAssembly`) transfers the level
   line from the model to `π`. This gives `IsNewvectorConductor π a` and
   `finrank (levelFixedVectors π a) = 1`. The witnesses are `(c, a)`.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
