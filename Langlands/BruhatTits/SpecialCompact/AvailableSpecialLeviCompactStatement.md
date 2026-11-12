# The Levi part of a special compact subgroup is special compact in the Levi

`Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactStatement` is a
proposition target. It is the geometric content of Renard, Théorème V.5.1(5),
for valid corrected Kaletha–Prasad assignments. At a special vertex of the
apartment of the data for `G`, the preimage of `K_0` in an actual standard Levi
`M_J(F)` should be the special compact subgroup, at a special vertex, of
available data for `M_J` based at the same torus. The declaration states this;
it supplies no proof.

## The statement

The statement takes every universe-`u` nonarchimedean local field `F` (with its
valuation relation and topology), every connected reductive `F`-group `G`, and
every assignment `𝔅 : KPBuildingAssignment.{u}` with `𝔅.IsValid`. This is the
full corrected KP Definition 4.1.26 for every connected reductive group over
every nonarchimedean local field in universe `u`. There is no restriction on
characteristic, residue characteristic, rank, splitness, quasi-splitness or
ramification.

Write `B := (𝔅.datum F G hG).base`, with torus `B.S`, inclusion `B.i` and
apartment data `B.apartment`. The statement takes every generic cocharacter
`ν` of `B.S` (`IsGenericCocharacter B.i ν`, which fixes the positive system and
the minimal parabolic), every `x : B.Apartment` with
`B.apartment.IsSpecialApartmentVertex x`, and every set `J ⊆ simpleRelativeRoots B.i ν`.
Let `M_J := Standard.leviScheme B.i ν J` be the actual closed standard Levi, with
inclusion `Standard.leviHom B.i ν J : M_J → G` and torus inclusion
`Standard.leviTorusHom B.i ν J : B.S → M_J`.

The conclusion asks for

1. a proof `hM` that `M_J` is connected reductive;
2. an assignment `𝔅M : KPBuildingAssignment.{u}` with
   `𝔅M.IsAvailableFor F M_J hM`, i.e. Definition 4.1.26 for `M_J` alone;
3. the equalities `(𝔅M.datum F M_J hM).base.S = B.S` and
   `HEq (𝔅M.datum F M_J hM).base.i (Standard.leviTorusHom B.i ν J)`, so that
   the data of `𝔅M` for `M_J` are based at the ambient torus with its actual
   inclusion into the Levi; and
4. a point `xM` of the apartment of those data that is a special vertex
   (`IsSpecialApartmentVertex`) and satisfies

   ```text
   (𝔅M.datum F M_J hM).base.apartment.specialCompactSubgroup xM
     = B.apartment.specialCompactLeviSubgroup ν J x.
   ```

The left side is `M_J(F)^1 ∩ Stab(xM)` for the data of `𝔅M`. The right side is
the preimage of `K_0 = G(F)^1 ∩ Stab(x)` under the actual Levi inclusion on
rational points; its image in `G(F)` is `K_0 ∩ M_J(F)`.

`𝔅M` is existential and need not be `𝔅`. The statement does not ask `𝔅M` to be
valid, nor does it relate `xM` and `x` beyond the equality of compact subgroups.

## Comparison with `SpecialLeviInheritance`

The published predicate `SpecialLeviInheritance`, a conclusion of
`AvailableSimultaneousStandardBasisStatement`, provides bare apartment data
`DM : KPApartmentData (Standard.leviTorusHom B.i ν J) _` and a point `xM` with
the same compact equality. It does not say that `DM` is the apartment of data
for which Bruhat–Tits theory is available. This target asks for exactly that.
With it, statements that assume availability, such as
`Iwasawa.AvailableIwasawaStatement`, can be applied to the Levi at the compact
subgroup `K_0 ∩ M_J(F)`.

## Why this is expected to hold

The published `IsValid` structure has no field asserting this Levi
conclusion. The intended geometric route uses the following source facts:

- KP Lemma 6.7.1(1)–(4) restricts an equipollence class of valuations for
  `(G, S)` to one for `(M_J, S)`, preserves compatibility with the field
  valuation and identifies the reduced Levi apartment with the quotient by
  the appropriate central directions.
- KP Proposition 6.2.6 identifies compatible valuations up to equipollence.
  Comparing with available Levi data based at the same torus therefore
  requires both this uniqueness fact and a transport of the chosen data.
- KP §6.7.2 states that the projection preserves special points and that
  their images are vertices. This supplies the source-level special-vertex
  comparison.

A proof must additionally compare the actual building actions and the
rational-character norm kernels to obtain the exact subgroup equality in the
conclusion. Restriction of valuations alone does not supply that equality
or the full availability predicate. These comparisons and the existential
assignment packaging are retained proof obligations. This is a provenance
route, not a proof of the target.

## Role

This target is one of the premises of `JointBasisReductionStatement`. There it
supplies the Levi Iwasawa products of `JointSpecialCompactBasisExistenceStatement`
at the common `K_0`.

## Sources and provenance

The statement is derived from Renard V.5.1(5) and the Levi restriction of
Kaletha–Prasad. Renard does not state this assignment-level formulation: his theorem
asserts the properties of one adapted compact subgroup, without the
Library's chosen-data or availability predicates. The requirement here for
every special vertex of valid data, with an existential available Levi
assignment at the prescribed torus, is a derived geometric formulation. It
supplies neither a proof of Renard V.5.1(5) in full nor a construction of a
valid ambient assignment.

- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026,
  Théorème V.5.1(5), printed p.122/PDF p.128: `K_0 ∩ M` satisfies (1)–(4) for
  `P_∅ ∩ M`. Source ID
  `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023): Proposition
  1.3.43, printed p.30/PDF p.61; Definition 4.1.26, printed p.165/PDF p.196;
  Proposition 6.2.6, printed p.216/PDF p.247; Lemma 6.7.1(1)–(4) and
  §6.7.2, printed pp.233–234/PDF pp.264–265. Source ID
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024, PDF p.27: the
  corrected ten-axiom list of Definition 4.1.26; PDF p.32: Chapter 6
  corrections (including the clarification at Definition 6.3.4). Source ID
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
