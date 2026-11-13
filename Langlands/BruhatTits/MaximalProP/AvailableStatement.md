# Maximal open pro-`p` subgroups on available Bruhat–Tits data

`Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement` is a
proposition target. It states Kaletha–Prasad Proposition 13.5.2, as corrected
on 1 November 2024, for every assignment for which Bruhat–Tits theory is
available (corrected KP Definition 4.1.26). This is Matsumoto's
characterization of Iwahori subgroups. The pro-unipotent radical `P_{x,0+}` of
a parahoric subgroup is an open pro-`p` subgroup of `G(F)^0`. It is maximal
exactly at chambers. Every maximal one has this form, and its normalizer in
`G(F)^0` is the Iwahori subgroup. The module supplies no proof.

## Declarations

The module is in namespace `Langlands.BruhatTits.MaximalProP`.

- `IsMaximalOpenProPIn p A H`, for subgroups `A` and `H` of a topological
  group `X`, says four things. `H ≤ A`. `H` is open in `X`.
  `H` satisfies the Library's `Langlands.Cohomology.IsProPSubgroup p`. Finally,
  every open pro-`p` subgroup `H'` of `X` with `H ≤ H' ≤ A` equals `H`. This is
  maximality among the open pro-`p` subgroups of `X` contained in `A`. The
  published `IsProPSubgroup p H` requires `p` to be prime and `H`, with the
  subspace topology, to be compact and totally disconnected. Its quotients by
  open normal subgroups must be `p`-groups.
- `facetPositiveSubgroup D Fa`, for `D : KPBuildingDatum G` and a facet
  `Fa : BuildingFacet D.base.toValuationBuildingData` of the reduced building,
  is `(D.quotients.quotient Fa).positivePoints`. It is the image in `G(F)` of
  the integral sections of the neutral model of `Fa` whose reduction lies in
  the residue-field points of the supplied radical of the special fibre. This is
  the group `G(k)^{0+}_F` of KP Axiom 4.1.22(7).
- `facetZeroFixer D Fa` is `BuildingModelFamily.zeroFixer D.base
  (BuildingModelIndex.ofFacet Fa)`. That is the pointwise fixer of `Fa` in
  `B(G)`, intersected with `D.base.zeroSubgroup`, so `G(F)^0_F`. For a chamber
  it is the Iwahori subgroup of KP Definition 7.4.5(2).
- `MaximalProPConclusions D` is a conjunction of four clauses. It places the
  point topology `rationalPointTopology F G.X` on `rationalPoints G` and uses
  `p := ringChar 𝓀[F]`, the residue characteristic.
  1. For every facet `Fa`, `facetPositiveSubgroup D Fa ≤ D.base.zeroSubgroup`.
     The subgroup is open, and it satisfies `IsProPSubgroup p`.
  2. For every facet `Fa`,
     `IsMaximalOpenProPIn p D.base.zeroSubgroup (facetPositiveSubgroup D Fa)`
     holds if and only if `D.base.IsChamber Fa.val`.
  3. For every subgroup `H` with
     `IsMaximalOpenProPIn p D.base.zeroSubgroup H`, there is a facet `C` with
     `D.base.IsChamber C.val` and `H = facetPositiveSubgroup D C`.
  4. For every facet `C` with `D.base.IsChamber C.val`,

     ```text
     Subgroup.normalizer (facetPositiveSubgroup D C) ⊓ D.base.zeroSubgroup
       = facetZeroFixer D C.
     ```
- `AvailableMaximalProPStatement` (entry declaration) takes every universe-`u`
  nonarchimedean local field `F`, with its valuation relation and topology, and
  every connected reductive `F`-group `G` (proof `hG`). It also takes every
  `𝔅 : KPBuildingAssignment.{u}` with `𝔅.IsAvailableFor F G hG`. Its
  conclusion is `MaximalProPConclusions (𝔅.datum F G hG)`.

Only availability for `G` over `F` is assumed, not `𝔅.IsValid`. There is no
restriction on characteristic, residue characteristic, rank, splitness or
ramification.

## Relation to the source

KP Proposition 13.5.2 (printed pp.476–477) assumes that `k` is a local field.
It states:

1. for every `x ∈ B(G)`, `P_{x,0+}` is an open pro-`p` subgroup of `G(k)`; it
   is maximal if and only if `x` lies in a chamber, that is, `P_{x,0}` is an
   Iwahori subgroup;
2. every maximal open pro-`p` subgroup of `G(k)^0` equals `P_{x,0+}` for an
   Iwahori subgroup `P_{x,0}`, and `P_{x,0}` is the normalizer of `P_{x,0+}` in
   `G(k)^0`.

The 2024 corrections (PDF p.49) replace `G(k)` with `G(k)^0` in (1).
Clauses 1 and 2 above are corrected part (1), with maximality in `G(F)^0`.
Clauses 3 and 4 are part (2).

The translation makes the following identifications.

- **`P_{x,0+}` is the facet radical preimage.** KP 13.2.6 (printed p.470)
  identifies the kernel of `P_{x,0} = 𝒢_x^0(𝔬) → 𝖦_x(𝔣)` with `P_{x,0+}`, by
  Corollary 8.4.12 (printed p.306). Here `𝖦_x` is the maximal reductive
  quotient of the special fibre. Equivalently, `P_{x,0+}` is the preimage of
  `R_u(𝒢_x^0 ⊗ 𝔣)(𝔣)` under reduction. This is `G(k)^{0+}_F` of Axiom 4.1.22(7)
  for the facet `F` of `x`. On supplied data the Library proves the same kernel
  identification, `SpecialFibreQuotientData.ker_parahoricReduction` in
  `Langlands.BruhatTits.IntegralModels.DepthZeroReduction`. It needs only that
  the supplied quotient is the fppf quotient by the radical, which is part of
  Axiom 4.1.22 (`FacetAxiomClauses.reductive_quotients`).
- **Why not the Moy–Prasad filtration declaration.** The Library's
  `KPMoyPrasadFiltration` builds `P_{x,r}` from a supplied filtration of
  `Z(F)`. Its Markdown records that `P_{x,0+}` there is not identified with
  `positivePoints`. KP Remark 13.2.2 notes that `P_{x,r}` depends on the
  filtration of `Z(k)`, while `P_{x,0}` and `P_{x,0+}` depend only on the facet.
  A supplied filtration is not tied to the available data. The supplied group
  `Z(F)_{0+}` need not be pro-`p`, and `Z(F)^0/Z(F)_{0+}` need not have order
  prime to `p`. So the statement for an arbitrary supplied filtration would be
  false. The facet radical preimage has no such freedom.
- **Points and facets.** KP quantifies over points `x`. `P_{x,0}` and
  `P_{x,0+}` depend only on the facet of `x` (Remark 13.2.2), and every point
  lies in a unique facet. The statement therefore quantifies over the facets
  `BuildingFacet` of the reduced building. "`x` lies in a chamber" becomes
  `D.base.IsChamber Fa.val`: `Fa` is a `G(F)`-translate of a chamber of the
  apartment.
- **The Iwahori subgroup.** For a chamber `C`, KP's `P_{x,0} = G(k)_{x,0}` is
  `G(k)^0_C` (Definition 7.4.5(2)). Under Axiom 4.1.20 it is the group of
  integral points of the neutral model of `C`. The statement uses the fixer
  `facetZeroFixer D C` directly. Its normalizer clause is intersected with
  `D.base.zeroSubgroup`, as in "normalizer in `G(k)^0`".
- **Maximality.** "Maximal open pro-`p` subgroup of `G(k)^0`" is read as
  maximal among open pro-`p` subgroups of `G(F)` contained in `G(F)^0`. The
  topology is the Library's point topology on `G(F)`, and `p` is the residue
  characteristic.

This is a faithful formulation on available data. The KP proof uses only
consequences of the axioms of Definition 4.1.26 and the local compactness of
`F`. It does not assert that available assignments exist.

## Expected proof route

KP's proof (printed pp.476–477) uses the following steps. The facet-level
inputs are the clauses of Axiom 4.1.22 recorded in `FacetAxiomClauses`.

1. *Clause 1.* Integral points of the smooth neutral model are open and compact
   in `G(F)`. The reduction kernel is pro-`p`, and `R_u(𝔣)` is a finite
   `p`-group. Openness of the preimage follows because `𝔣` is finite.
2. *Non-chambers are not maximal.* If `Fa` is not a chamber, Axiom 4.1.22(5)
   (`parabolic_order`) gives a proper parabolic of the reductive quotient; see
   KP Remark 4.1.23. The preimage of the residue points of its unipotent
   radical is a strictly larger open pro-`p` subgroup of `G(F)^0`.
3. *Every maximal `H` is a chamber radical.* `H` is compact, so it fixes a
   point by the fixed-point theorem (KP Corollary 4.2.14). It fixes pointwise a
   maximal `H`-fixed facet `F` (KP Proposition 1.5.13(3)). `H` normalizes
   `G(F)_{F,0+}`, so maximality gives `G(F)_{F,0+} ≤ H`. The image of `H` is a
   `p`-Sylow subgroup of `𝖦_F(𝔣)`, the residue points of the unipotent radical
   of a Borel subgroup. Axiom 4.1.22(4),(5) moves `H` into `G(F)^0_C` for a
   chamber `C ≻ F`, and maximality of `F` forces `F = C`. By Axiom 4.1.22(6)
   (KP Theorem 8.4.10) the reductive quotient at a chamber is a torus, whose
   residue points have order prime to `p`. Hence `H = G(F)_{C,0+}`.
   `G(F)^0`-conjugacy of chambers (Axiom 4.1.9) gives maximality at every
   chamber.
4. *Normalizer.* The normalizer of `G(F)_{C,0+}` in `G(F)^0` is compact open
   (KP Proposition 2.2.16) and contains `G(F)^0_C`. So it is a parabolic
   subgroup of the Tits system, `G(F)^0_F` for a face `F` of `C`. Normality of
   the image of `G(F)_{C,0+}` in `𝖦_F(𝔣)` forces `F = C`.

## Sources and provenance

The formulation is derived. KP state the proposition for the Bruhat–Tits
building they construct. Here it is stated for every assignment satisfying
corrected Definition 4.1.26. `P_{x,0+}` is read through 13.2.6 and Axiom
4.1.22(7), and points are replaced by facets.

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023). Axiom
  4.1.20 and Axiom 4.1.22, printed pp.163–164 / PDF pp.194–195. Remark 4.1.23,
  printed p.164 / PDF p.195. Definition 4.1.26, printed p.165 / PDF p.196.
  Definition 7.4.5, printed p.256 / PDF p.287. Corollary 8.4.12, printed
  p.306 / PDF p.337. Definition 13.2.1, Remark 13.2.2 and 13.2.6, printed
  pp.468–470 / PDF pp.499–501. Proposition 13.5.2 and proof, printed
  pp.476–477 / PDF pp.507–508. Source ID
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024. PDF p.27 has
  the corrected axiom list of Definition 4.1.26. PDF p.49 replaces `G(k)` with
  `G(k)^0` in Proposition 13.5.2(1). Source ID
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
