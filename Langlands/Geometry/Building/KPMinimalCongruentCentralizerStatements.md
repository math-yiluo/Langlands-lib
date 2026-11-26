# Statements on the minimal congruent centralizer filtration

The propositions in this module refer to the subgroup family constructed
in `KPMinimalCongruentCentralizer`. The ground field is any
nonarchimedean local field `F`, with `K = inertiaFixedField F`, and
`P : ParahoricBuildingData G` supplies the maximal split torus `S` of
the connected reductive group `G` and its centralizer `Z`. The depths
are finite nonnegative reals. §13.5 chooses the minimal congruent
filtration on tori, so all statements about the constructed family use
`minimalCongruentPoints` in the torus term of the §9.8 construction.

## Order, zero and choices

- `MinimalCongruentCentralizerOrderStatement` asserts decreasingness and
  trivial intersection for the actual subgroups of `Z(F)`. The order
  properties give the two proof fields of the supplied-filtration package.
  The source is the decreasing separated filtration in the opening of
  KP Proposition 13.2.5, applied to `Z_K` and pulled back under
  injective extension of points. The torus prerequisite is the
  decreasing separated family of Appendix B, Definitions B.5.2 and
  B.10.2 and Corollary B.10.13.
- `MinimalCongruentCentralizerZeroStatement` asserts `Z(F)_0 = Z(F)^0`.
  The construction module proves this equality for each `P` as
  `minimalCongruentCentralizerPoints_zero`. It uses the original
  `P.centralizerZero` of Definition 2.6.23(2).
- `MinimalCongruentMoyPrasadApartmentIndependenceStatement` compares two
  presentations of an arbitrary reduced building point over `K` for a
  given group `H`. Each uses the centralizer torus of its maximal split
  torus. `IsSameBuildingPoint` expresses the same-point condition via
  the existing `IntegerValuationBuildingData.buildingComparison`.
  The comparison transports the first normalized apartment along
  `Int(g)` for an element `g` carrying its split torus onto the second.
  Acting by `g⁻¹` afterward identifies the reduced buildings along the
  identity of `H(K)`. The equality of the two points under this
  identification is precisely the Lean premise. This is the transport
  of Proposition 6.2.6 used in `integerValuationBuildingSameGroupComparison`.
  Proposition 7.6.4(2) gives transitivity on the apartments through the
  point, and Proposition 7.3.17 gives invariance of the constant-depth
  subgroup under the connected point stabilizer. This accounts for
  changing the maximal `K`-split torus, its centralizer torus and their
  apartment coordinates. For `H = Z_K`, the equality is upstairs in
  `Z(K)` before taking either inverse image.
- `MinimalCongruentCentralizerIndependenceStatement` quantifies over
  every special-torus lift of the unique point of `B(Z)` and asserts
  equality of its inverse image with the selected `Z(F)_r`. Here the
  domain point is specified by `centralizerBuildingPoint`. The
  `ApartmentLift` supplies its compatibility with unramified descent.

## Properties for the supplied-filtration API

`MinimalCongruentCentralizerAxiomsStatement` and
`MinimalCongruentCentralizerDoubleRootStatement` use
`P.SatisfiesApartmentAxioms` and take the stated order properties as a
proof argument. `MinimalCongruentCentralizerOpenStatement` uses the
order properties for the same packaging and says each subgroup is
open for the Library's rational-point topology of `Z(F)`.
Corollary 7.3.14 gives openness for the finite constant function over
`K`, and restriction to `Z(F)` is a continuous inverse image.

`SatisfiesFiltrationAxioms` is the existing conjunction of ordinary
commutator friendliness, normalizer stability, commutator filtration
and root compatibility. The ordinary friendliness is Lemma 9.8.1
using Lemma 7.2.3. Normalizer stability follows from point covariance
and the independence of the Levi component from the point of `A(S)`.
The commutator filtration comes from the constant-depth commutator
property over `K`. Root compatibility uses the root-group
intersection of Proposition 9.8.3(1). Its target is the block with
both `a` and `2a` at depth `r + s`, as in Definition 7.3.3(1).

The double-root statement asks for `z ∈ Z(F)_{2r}` when an opposite-root
pair of depth sum `r > 0` has a factor in a double root group. The
quasi-split `SU(3)` calculation in the proof of Proposition 7.1.1
then has centralizer coordinate given by `γ = 1 + ββ'`, with
`ω(γ − 1) = 2r` in sum-of-opposite-depth normalization. The inducing
torus in that computation has the geometric-character bound at `2r`
by Corollary B.10.13. Functoriality of the minimal congruent filtration
takes its image into the centralizer torus at the same depth.
The descent argument of §9.8 uses the constant-depth groups of `G_K`
and Levi intersection. Translate the downstairs apartment point so
that the factor opposite the doubled root has depth zero. Axiom V 4
puts the doubled factor at depth `2r` for its own root. Normality of
the upstairs depth `2r` group in the depth-zero group gives the
commutator bound. The positive-depth factorization extracts the
centralizer factor, and Lemma 8.5.19 identifies the Levi term.

This sharper condition is derived from the source computations and
descent, as in `KPMoyPrasadDoubleRootStatement`. The ramified
`SU(3)` counterexample for supplied filtrations in
[`moy-prasad-supplied-filtration-counterexample.md`](../../../notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md)
uses the subgroup generated only by the components forced by ordinary
friendliness. In that example the maximal torus is induced. The
minimal congruent filtration on it contains the required double-root
components by its character formula. The double-root Proposition
13.2.5 results use the sharper condition explicitly.

## Standard filtration comparison

`MinimalCongruentCentralizerWeaklyInducedStatement` uses
`IsWeaklyInducedTorus F` on the actual maximal torus of `Z_K` in a
special-torus lift. Corollary B.10.13 identifies its two torus
subgroups at every depth. The same generator construction and the
same inverse image then give the standard `Z(F)_r`. Independence
allows this comparison with the chosen centralizer family.

`MinimalCongruentStandardCentralizerComparisonStatement` takes the
same weakly induced premise and `P.SatisfiesApartmentAxioms`. It
compares with the published ambient-group route to the standard
filtration. For every special-torus lift of `P` and every point
`x` of its apartment, it takes the inverse image of the standard
`G(K)_{e(x),r}` in `G(F)` and the inverse image of that subgroup
under `Z(F) → G(F)`. This is the subgroup expression used by
`IsRationalMoyPrasadFamily.centralizerFiltration` for the standard
group family. Its equality with the direct construction on `Z`
is the Levi comparison of Lemma 8.5.19 used in §9.8.

`MinimalCongruentCentralizerStatements` is the conjunction of the nine
proposition definitions. The mathematical obligations beyond the zero
equality are stated here for subsequent proofs.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
  Proposition 7.1.1 and Axiom V 4 in Definition 6.1.2 give the
  double-root calculation and normalization. See PDF pp. 269–271
  for the computation, pp. 276–284 for §7.2 and Propositions
  7.3.12 and 7.3.17, p. 296 for Proposition 7.6.4, p. 350 for
  Lemma 8.5.19, and pp. 405–407 for §9.8 and Proposition 9.8.3.
  Proposition 13.2.5 appears on PDF p. 500, the choice of the
  minimal congruent torus filtration at the start of §13.5 on
  PDF p. 505, and Corollary B.10.13 on PDF p. 723.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
  PDF p. 33 gives the Chapter 7 standing apartment hypothesis and
  the additional clause of Proposition 7.3.12. PDF p. 41 corrects
  the domain of the projection in Lemma 9.8.1. PDF p. 50 clarifies
  Definition B.10.8 and supplies the corrected Galois scope. The
  Chapter 13 errata on PDF p. 49 concern other propositions and
  sections.
