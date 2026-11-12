# Special vertices in the apartment of available corrected KP data

`Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexExistenceStatement`
is a proposition target. Whenever Bruhat–Tits theory is available for a group in
an assignment, the apartment of the assigned data should contain a special
vertex. The declaration states this; it supplies no proof. It does not assert
that available data exist.

## The statement

The statement takes every universe-`u` nonarchimedean local field `F` (with its
valuation relation and topology), every connected reductive `F`-group `G`, and
every assignment `𝔅 : KPBuildingAssignment.{u}` with `𝔅.IsAvailableFor F G hG`.
This premise is the corrected KP Definition 4.1.26 for `G` over `F` in `𝔅`, with
its ten axioms. Only availability for `G` is assumed, not validity of the whole
assignment. There is no restriction on characteristic, residue characteristic,
rank, splitness, quasi-splitness or ramification.

Write `B := (𝔅.datum F G hG).base`. These are the data of `𝔅` for `G`, with
torus `B.S`, maximal split torus inclusion `B.i` and apartment data
`B.apartment : KPApartmentData B.i (localFieldOrder F)`. The conclusion is that
some point `x : B.Apartment` satisfies `B.apartment.IsSpecialApartmentVertex x`.

`IsSpecialApartmentVertex x` is the conjunction of

- `AffineRootSystem.IsSpecialPoint B.apartment.affineRoots x`: for every affine
  root `ψ` there is an affine root vanishing at `x` whose hyperplane is parallel
  to that of `ψ` (KP Definition 1.3.39(1)); and
- `AffineRootSystem.IsVertex B.apartment.affineRoots x`: the facet of `x` is
  `{x}`.

Here `B.apartment.affineRoots` is the set `Ψ` of KP Definition 6.3.4, made of
affine functionals on the reduced apartment. The apartment is an affine space
over `V(S)` modulo the annihilator of the relative roots. So when `G` has
relative rank zero the apartment is a single point, which is then a special
vertex.

## Why this is expected to hold

Under Axiom 4.1.6 (AS 3), `Ψ` is an affine root system on `A(S)` whose set of
derivatives is the relative root system. KP Proposition 1.3.43(1) shows that extra special points
exist. Parts (2) and (3) show that an extra special point is special and that a
special point is a vertex. The formal proof is a separate obligation. In
particular it must identify the Library's `IsVertex` and `IsSpecialPoint` with
KP's notions on this `Ψ`.

## Role

The published conditional statements `AvailableSimultaneousStandardBasisStatement`,
`Iwasawa.AvailableIwasawaStatement` and
`Plancherel.RenardCartan.AvailableRenardCartanStatement` quantify over every
special vertex of the apartment. This target supplies one such vertex. It is
one of the premises of `JointBasisReductionStatement`.

## Sources and provenance

The statement is KP Proposition 1.3.43(1)–(3), specialised to the affine root
system of the apartment of available corrected data. This specialisation is
derived: KP prove the proposition for abstract affine root systems.

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023): Definition
  1.3.39, printed p.29/PDF p.60; Proposition 1.3.43(1)–(3), printed p.30/PDF
  p.61; Axiom 4.1.6, printed pp.159–160/PDF pp.190–191; Definition 4.1.26,
  printed p.165/PDF p.196; Definition 6.3.4 (the affine roots), printed
  p.218/PDF p.249. Source ID `kaletha-prasad-2023-bruhat-tits-new-approach`,
  SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024, PDF p.27: the
  corrected ten-axiom list of Definition 4.1.26 and the addition of the
  identity to the AS3 filtration groups. Source ID
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
