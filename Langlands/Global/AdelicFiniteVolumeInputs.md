# Finite volume of the norm-one rational quotient from its remaining inputs

This module reduces the finite-volume target
`Langlands.Global.AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement` (Library
module `Langlands.Global.AdelicFiniteVolumeStatement`) to seven separate Prop-valued
statements. It proves the implication and proves none of the seven inputs, so it does not
prove the target itself. A proof of the target is obtained by applying
`normOneFiniteVolumeInputsStatement` to proofs of the seven inputs.

## Statement

`NormOneFiniteVolumeInputsStatement` is the Prop-valued implication, at universe `u`,

    CharacteristicZeroLeviDecompositionStatement →
      PerfectFieldUnipotentSplitStatement →
        SplitUnipotentAffineTorsorStatement →
          AdelicGoodSiegelReductionStatement →
            PositiveTorusUnipotentModulusStatement →
              RelativeRootNegationStatement →
                RelativeCharacterRootComplementStatement →
                  NormOneRationalQuotientFiniteVolumeStatement

and `normOneFiniteVolumeInputsStatement` proves it. All eight propositions are existing
Library declarations, used unchanged:

* `Langlands.GroupScheme.CharacteristicZeroLeviDecompositionStatement`
  (`GroupScheme.Reductive.CharacteristicZeroLeviStatement`): every smooth connected affine
  finite-type group scheme `G` over a field of characteristic zero has homomorphisms
  `p : G ⟶ L`, `j : L ⟶ G` with `j ≫ p = 𝟙 L`, `L` connected reductive, and
  `GroupScheme.kernel p` smooth, connected and unipotent.
* `Langlands.GroupScheme.PerfectFieldUnipotentSplitStatement`
  (`GroupScheme.Unipotent.PerfectFieldSplitStatement`): every smooth connected affine
  unipotent group over a perfect field is split unipotent (`RelativeRoot.IsSplitUnipotent`:
  a finite normal series with one-dimensional vector quotients).
* `Langlands.GroupScheme.SplitUnipotentAffineTorsorStatement`
  (`GroupScheme.SplitUnipotentAffineTorsorStatement`): every fpqc torsor under the pullback
  of a smooth affine split-unipotent group over a field has a section over every affine
  scheme over that field.
* `Langlands.Global.AdelicSiegelFactors.AdelicGoodSiegelReductionStatement`
  (`Global.AdelicSiegelFiniteVolume`): every connected reductive group over a number field
  has an actual algebraic Siegel setup, compact factor data with maximal compact Iwasawa
  data, and a parameter `t` such that the rational left translates of the weak Siegel
  product `S(t)` are exactly the norm-one group: `G(F) · S(t) = G(𝔸_F)¹` (`IsSiegelCover`;
  the cover is of `G(𝔸_F)¹`, not of all of `G(𝔸_F)`, as in Getz–Hahn, Theorem 2.7.2). The
  parabolic part of the compact subgroup also commutes with the positive torus
  (`IsPositiveTorusCompatible`).
* `Langlands.Global.AdelicSiegelFactors.PositiveTorusUnipotentModulusStatement`
  (`Global.AdelicSiegelMeasureReduction`): for every actual algebraic Siegel setup of a
  connected reductive group over a number field, the Haar modulus of conjugation by a point
  `a` of the positive torus `A_{T₀}` on the closed subgroup `N(𝔸_F)` is
  `∏_{β > 0} |β(a)|^{m_β}`, the product over the positive relative roots with `m_β` the
  dimension of the `β`-weight space.
* `Langlands.GroupScheme.RelativeRootNegationStatement`
  (`GroupScheme.Rational.RelativeRootNegationStatement`): the relative roots of a maximal
  split torus in a connected reductive group over a field are stable under negation.
* `Langlands.GroupScheme.RelativeCharacterRootComplementStatement`
  (`GroupScheme.Rational.RelativeCentralDirectionsStatement`): for a maximal split torus in a
  connected reductive group over a field, the relative root span and the restrictions of the
  group's rational characters are complementary in the character space, over `ℚ` and `ℝ`.
* The target asserts finiteness of `normOneRationalQuotientHaarMeasure F G` for every affine
  finite-type `G` over a number field `F` with `G.X.hom` smooth and `G.X.left` connected.

The module changes no convention and adds no hypothesis to the target. The quotient measure
is the one fixed in the target: the quotient of the Haar measure on `G(𝔸_F)¹` by counting
measure on the principal subgroup.

## Proof

`normOneFiniteVolumeInputsStatement` composes published Library theorems:

1. `unipotentRationalQuotientCompact_of_split` (`Global.SplitUnipotentRationalQuotientCompact`)
   turns the split and torsor statements into `UnipotentRationalQuotientCompactStatement`
   (compactness of `G(F) \ G(𝔸_F)` for smooth connected unipotent affine finite-type `G`
   over a number field). Call this `hunip`.
2. `simpleRootBoxCompactStatement_of_rootComplement` (`Global.SimpleRootBoxCompact`) turns the
   negation and complement statements into `SimpleRootBoxCompactStatement` (compact
   simple-root boxes in `A_{T₀}`).
3. `siegelProductFiniteMeasureStatement_of_inputs` (`Global.AdelicSiegelMeasureReduction`)
   turns `hunip`, the modulus statement and the box statement into
   `SiegelProductFiniteMeasureStatement` (finite Haar measure of the trace on `G(𝔸_F)¹` of the
   weak Siegel products).
4. `connectedReductiveFiniteVolumeStatement_of_siegel` (`Global.AdelicSiegelFiniteVolume`)
   turns the good Siegel reduction statement and step 3 into
   `ConnectedReductiveFiniteVolumeStatement` (finite volume for connected reductive groups).
5. `isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_levi`
   (`Global.AdelicFiniteVolumeReduction`) applied to the Levi statement, `hunip` and step 4
   gives finiteness of `normOneRationalQuotientHaarMeasure F G` for each `F` and `G`
   quantified in the target.

`hunip` is used twice: for the unipotent radical `N` of the standard minimal parabolic in
step 3, and for the unipotent kernel of the Levi decomposition in step 5.

## Provenance

The reduction is internal to this project. It assembles published Library results and adds
no mathematics of its own. It follows the standard route to Borel–Harish-Chandra finite
volume: a Levi decomposition `G = U ⋊ L` reduces to the reductive case, and the reductive
case follows from Siegel-set reduction theory together with the finite Haar measure of
Siegel sets. The sources of the seven inputs are cited in their own modules: Milne,
*Algebraic Groups* (2017), 25.48–25.49 for the Levi decomposition and 16.24 for splitness of
unipotent groups over perfect fields; Conrad–Gabber–Prasad, *Pseudo-reductive groups*, for
the torsor statement; Getz–Hahn (2024), §2.7 for Siegel reduction and Section 3.6 for the
modulus formula; Kaletha–Prasad (2023) for negation stability of the relative roots;
Borel–Tits (1965), Theorem 5.3 and Corollary 5.8, for the root/character complement. The
target is Getz–Hahn's Theorem 2.6.3
over number fields, as recorded in the Markdown of `AdelicFiniteVolumeStatement`. Getz–Hahn
do not prove the theorem through this route, and this file attributes the route to no
particular source.
