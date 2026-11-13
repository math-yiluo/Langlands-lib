# Finiteness of the depth-zero reductive quotient of supplied KP models

This module proves that the residue-field points `\bar G_x(f)` of a supplied
finite-type quotient form a finite group when the residue field is finite. The
radical preimage in `G^0(R)` then has finite index, and over a Henselian base
this index is `|\bar G_x(f)|`. For the valuation ring of a nonarchimedean
local field, the module also proves that the reduction kernel is open in
`G^0(𝒪)` for the canonical topology.

## Provenance

The construction is derived; KP state no finiteness result here. It
specializes the depth-zero reduction of Kaletha–Prasad, *Bruhat–Tits Theory: A
New Approach* (2023), 13.2.6 (printed p. 470 / PDF p. 501), to a finite
residue field. There KP identify `P_{x,0}/P_{x,0+}` with `\bar G_x(f)`. The
registered original is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
KP's Chapter 13 (printed p. 466 / PDF p. 497) assumes only that `o` is a
Henselian discretely valued ring with perfect residue field `f`. It does not
assume `f` finite, and 13.2.6 does not state finiteness. Finiteness holds
because a scheme of finite type over a finite field has finitely many rational
points. The index formula then follows from the first isomorphism theorem in
`Langlands.BruhatTits.IntegralModels.DepthZeroReduction`.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, do not
amend 13.2.6. Their Chapter 13 corrections (PDF p. 49) concern only
Proposition 13.5.2, 13.6.2 and Theorem 13.8.5.

## Setting

The data are those of `DepthZeroReduction`. `R` is a domain in universe `u`
with fraction field `K`, and `G` is a group scheme over `Spec K`.
`D : RelativeComponentModelData R K G` and `Q : SpecialFibreQuotientData D`
are supplied. `D.neutral.integralPoints` plays the role of KP's
`P_{x,0} = G_x^0(o)`. `Q.positivePoints.subgroupOf D.neutral.integralPoints`
plays the role of `P_{x,0+}`. `rationalPoints Q.quotient` plays the role of
`\bar G_x(f)`. Nothing identifies `D.neutral` with a Bruhat–Tits parahoric
group scheme. The radical preimage `Q.positivePoints` is not compared with the
Moy–Prasad subgroup; that comparison is KP Corollary 8.4.12. The structure
`SpecialFibreQuotientData` already makes `Q.quotient` affine over the residue
field.

## Declarations

A general finiteness fact:

- `Langlands.GroupScheme.finite_rationalPoints`: a group scheme `G` over
  `Spec k`, with `k` a finite commutative ring, has finitely many `k`-points.
  Its structure morphism must be affine (`IsAffineHom`) and locally of finite
  type. The coordinate ring `AffineCoordinateRing k G.X` is then a
  finite-type `k`-algebra. The published lemma
  `Langlands.AlgebraicGeometry.LangWeil.CurvePlane.finite_algHom_of_finiteType`
  (module `Langlands.AlgebraicGeometry.LangWeil.AffineCurvePlaneComparison`)
  says that algebra maps from a finite-type algebra to a finite ring are
  finite in number. It gives finitely many `k`-algebra maps from the
  coordinate ring to `k`. The proof transports this finiteness along
  `rationalPointEquiv`, `affineSchemePointEquiv` and `AlgPoint.algHomEquiv`,
  which together identify `k`-points with these algebra maps. No new
  algebra-map finiteness lemma is declared.

In namespace `Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData`,
for a local domain `R` with finite residue field
(`[IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]`):

- `finite_quotientPoints`: if `Q.quotient` is locally of finite type, then
  `rationalPoints Q.quotient` is finite.
- `finite_quotientPoints_of_isConnectedReductive h`: the same conclusion from
  `h : IsConnectedReductive Q.quotient`. Its smoothness clause gives finite
  type.
- `finiteQuotientGroup` (the unit's selected definition): the finite group
  `\bar G_x(f)`, defined as `FiniteGrp.of (rationalPoints Q.quotient)` for a
  quotient locally of finite type.
- `ker_parahoricReduction_finiteIndex`: the kernel of `Q.parahoricReduction`
  has finite index in `D.neutral.integralPoints`, because its range lies in a
  finite group.
- `positivePoints_subgroupOf_finiteIndex hQ`: under the fppf-quotient
  hypothesis `hQ`, `Q.positivePoints.subgroupOf D.neutral.integralPoints` has
  finite index. It rewrites with `ker_parahoricReduction hQ`.

For a Henselian local domain with finite residue field
(`[HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)]`). The
residue field is then perfect by Mathlib's instance for finite fields:

- `index_positivePoints_subgroupOf hrad hQ`: the index of
  `Q.positivePoints.subgroupOf D.neutral.integralPoints` in
  `D.neutral.integralPoints` equals `Nat.card (rationalPoints Q.quotient)`.
  This is `[P_{x,0} : P_{x,0+}] = |\bar G_x(f)|` for the supplied data. The
  proof uses `ker_parahoricReduction hQ`, `Subgroup.index_ker` and
  `parahoricReduction_surjective hrad hQ`. Here `hrad` says that the radical is
  the represented unipotent radical, and `hQ` that the projection is its fppf
  quotient. Connected reductivity of the quotient is not used.

For a nonarchimedean local field `F` with valuation ring `𝒪[F]`, and
`D : RelativeComponentModelData 𝒪[F] F G`:

- `localField_index_positivePoints_subgroupOf hrad hQ`: the index formula
  above, with no further instance arguments. Finiteness of `𝓀[F]` is Mathlib's
  instance. Henselianity is the published `henselianLocalRing_integer`.
- `localField_isOpen_ker_parahoricReduction`: if `G` is affine and locally of
  finite type, and `G(F)` has the canonical topology `rationalPointTopology F
  G.X`, then the kernel of `Q.parahoricReduction` is open in `G^0(𝒪)`. It
  applies the published `isOpen_ker_parahoricReduction`, with the openness of
  the level-one congruence subgroup obtained from the published proof
  `LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof`.

## Scope

This module supplies no models, radicals, quotients or building points, and
no instances of them. It does not compare `Q.positivePoints` with the
Moy–Prasad filtration, and it does not prove compactness of `G^0(𝒪)` or of
the kernel.
