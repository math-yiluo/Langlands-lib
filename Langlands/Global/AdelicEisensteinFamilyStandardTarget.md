# The target parabolic in standard position

Module `Langlands.Global.AdelicEisensteinFamilyStandardTarget` proves
`FamilyRegularComparison.exists_standardTarget`, which moves the target parabolic `Q` of the
family comparison (module `Langlands.Global.AdelicEisensteinFamilyRegularComparison`) to a
standard parabolic of a given standard family.

## Statement

Assume `RootPresentationRegularityComparisonStatement` (module
`Langlands.Global.AdelicEisensteinRegularityPresentationComparisonStatement`). Let `fam` be a
standard parabolic family of `G` with a standard index `I`, and let `q : Q → G` be a parabolic
with Levi `l'`, Levi projection `π'` (`l' ≫ π' = 𝟙`), geometric unipotent radical `iV` and an
arbitrary root presentation `r'`. Let `(w, c)` be a Weyl conjugation from `P_I` to `Q`, and let
`K` have Iwasawa coverage for `P_I` and `Q`. Then there are a standard index `J`, a rational
point `s`, `c₃ : M_J → M_I`, a Levi projection `proj : P_J → M_J` with `l_J ≫ proj = 𝟙` and
Iwasawa coverage of `K` for `P_J` such that `(s w, c₃)` is a Weyl conjugation from `P_I` to
`P_J`, and the family comparison for `(P_I, P_J, proj, s w, c₃)` with the standard
presentations implies the family comparison for `(P_I, Q, π', w, c)` with `r'`.

## Proof

1. **Conjugating `Q` to standard position.** The presentation `r'` is realized by a standard
   cocharacter `ζ` of its own torus: `Q` and `M'` are the dynamic parabolic and centralizer of
   `ζ`. By `exists_simultaneousStandardConjugate_of_dynamicRealization` (module
   `Langlands.GroupScheme.Rational.SimultaneousStandardConjugation`), with
   `smoothMaximalSplitTorusConjugacy` and the relative root system `relativeRootSystem` of the
   torus of `fam`, there are a rational point `g` and a set `J` of simple roots such that
   `g Q g⁻¹` and `g M' g⁻¹` have the images of the standard parabolic and Levi of `J`, and are the
   dynamic parabolic and centralizer of a standard cocharacter `ζ₁` for `J`.
2. **Identifications.** Closed subgroups with the same image are isomorphic over `G`
   (`IsClosedSubgroup.sourceIsoOfRangeEq`): `eQ : P_J ≅ Q` over `G` after conjugation by `g`,
   and `eMQ : M' ≅ M_J` compatible with the Levi inclusions. The radical of `g Q g⁻¹` has the
   image of the standard unipotent subgroup of `J`
   (`Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer`, `standardCocharacter`).
   Put `s = g`, `c₃ = eMQ⁻¹ ≫ c` and `proj = eQ ≫ π' ≫ eMQ`; then `l_J ≫ proj = 𝟙`, `(g w, c)` is a
   Weyl conjugation to `g Q g⁻¹` and `(g w, c₃)` one to `P_J`. Iwasawa coverage passes to
   `g Q g⁻¹` (`eisensteinConjugateParabolicHeight`) and then to `P_J`
   (`IsIwasawaCompact.of_range_eq`).
3. **Change of target presentation.** The transported parameters correspond along `eQ`:
   `weylParameter l_I c₃ proj λ = eQ^*(weylParameter l_I c π' λ)`. The regularity comparison
   statement, applied to the conjugated presentation `r'.compAmbientIso (G.innerIso g)` of
   `g Q g⁻¹` and the standard presentation of `P_J`, gives comparable thresholds.
   `FamilyRegularComparison.of_targetRange` (module
   `Langlands.Global.AdelicEisensteinFamilyTargetRange`) moves the comparison from `P_J` to
   `g Q g⁻¹`.
4. **Conjugating back.** `FamilyRegularComparison.of_conjugateTarget` (module
   `Langlands.Global.AdelicEisensteinFamilyConjugateTarget`) moves the comparison from
   `(g Q g⁻¹, g w)` to `(Q, w)`.

## Source

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, take `Q` standard. Every parabolic
with a Levi is rationally conjugate to a standard parabolic with its standard Levi; this module
carries the comparison along such a conjugation and the change of presentation it entails.
