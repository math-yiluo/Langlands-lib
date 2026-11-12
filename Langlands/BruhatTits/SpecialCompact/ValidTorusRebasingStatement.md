# Rebasing a valid corrected KP assignment at a prescribed maximal split torus

`Langlands.BruhatTits.SpecialCompact.ValidAssignmentTorusRebasingStatement` is a
proposition target. It says that a valid corrected Kaletha–Prasad assignment can
be replaced by another valid assignment whose data for a chosen group are based
at any prescribed maximal split torus. The declaration states this; it supplies
no proof. It does not assert that a valid assignment exists.

## The statement

The statement takes an assignment `𝔅 : KPBuildingAssignment.{u}` together with
the proposition `𝔅.IsValid`. This is the full corrected KP Definition 4.1.26
(Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and
4.1.22) for every connected reductive group over every nonarchimedean local
field in universe `u`. It includes the comparisons between groups in Axioms
4.1.1 and 4.1.17.

It then takes every universe-`u` nonarchimedean local field `F` (with its
valuation relation and topology), every connected reductive `F`-group `G`, and
every commutative group scheme `S` with a homomorphism `i : S → G` that
satisfies `IsMaximalSplitTorus i`. There is no restriction on characteristic,
residue characteristic, rank, splitness, quasi-splitness or ramification.

The conclusion asks for an assignment `𝔅'` such that

- `𝔅'.IsValid` holds, and
- the data `(𝔅'.datum F G hG).base` of `𝔅'` for `G` have torus `S`, as an
  equality of commutative group schemes, and inclusion `i`, as a heterogeneous
  equality `HEq (𝔅'.datum F G hG).base.i i`. The heterogeneous equality is
  needed only because the type of the inclusion depends on the torus.

Nothing is said about the data of `𝔅'` for other groups, and no relation
between `𝔅` and `𝔅'` is required.

## Why this is expected to hold

A `KPBuildingDatum G` fixes one maximal split torus `S₀ → G` with its
apartment, root groups, valuations, integral models and quotients. By
Borel–Tits, Théorème 4.21, the images of maximal split tori are conjugate
under `G(F)`. Thus the chosen inclusion can be transported to `i` using an
inner automorphism of `G` and an isomorphism of its torus with `S`.

The intended route transports the entire datum, including the building
action. With the action pulled back along `Int(g⁻¹)`, the map `y ↦ g · y`
from the transported building to the original building is equivariant for
the identity map on `G(F)`: its defining identity is
`g · ((g⁻¹kg) · y) = k · (g · y)`. The raw translation on a building with its
unchanged action is not the equivariant comparison being used here.

The single-group axioms must be transported with the root groups, valuations
and model data. The published comparison predicates in Axioms 4.1.1 and
4.1.17 assert existence of equivariant building isomorphisms, so the intended
route transports their witnesses by composition. Constructing this transport
and a valid replacement assignment is a separate proof obligation. This
explanation records derived provenance and supplies no proof.

## Role

The published conditional statements on valid or available data
(`AvailableSimultaneousStandardBasisStatement`, `Iwasawa.AvailableIwasawaStatement`,
`Plancherel.RenardCartan.AvailableRenardCartanStatement`) speak about the
assignment's own torus `(𝔅.datum F G hG).base.i`. Existence targets such as
`JointSpecialCompactBasisExistenceStatement` fix an arbitrary maximal split torus
`i` in advance. This statement connects the two. It is one of the premises of
`JointBasisReductionStatement`.

## Sources and provenance

The statement is derived. Kaletha and Prasad do not state it, because their
building contains an apartment for every maximal split torus. The Library's
`KPBuildingDatum` instead singles out one torus, so a change of base torus has to
be stated separately.

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Definition
  4.1.26, printed p.165/PDF p.196; Axiom 4.1.1, printed pp.157–158/PDF
  pp.188–189; Axiom 4.1.4(A2), printed p.159/PDF p.190; Axiom 4.1.17,
  printed p.162/PDF p.193. Source ID
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024, PDF p.27: the
  corrected ten-axiom list of Definition 4.1.26. Source ID
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
- Borel–Tits, *Groupes réductifs* (1965), Théorème 4.21, printed p.93/PDF p.40:
  maximal split tori are conjugate over `k`. Source ID
  `borel-tits-1965-groupes-reductifs`, SHA256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
