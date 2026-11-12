# Affine roots and special points under restriction to a standard Levi

`Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement` is a
Prop-valued `def` at every universe `u`. It states Kaletha–Prasad §6.7.2
for the actual standard Levi subgroups of a connected reductive group over a
nonarchimedean local field, at the same maximal split torus. Pulled back
along the restriction of valuations, the affine roots of the Levi are affine
roots of the group, and the restriction of a special point is a special
point and a vertex. The module supplies no proof.

## Statement

The proposition quantifies over the same data as
`LeviApartmentRestrictionStatement`:

- every nonarchimedean local field `F`, of either characteristic, with its
  normalized valuation `ω = localFieldOrder F`;
- every group scheme `G` over `Spec F` with `hG : IsConnectedReductive G`;
- every `i : S.toGrp ⟶ G` with `hi : IsMaximalSplitTorus i`;
- every cocharacter `ν` of `S` with `IsGenericCocharacter i ν`, and every
  `J ⊆ simpleRelativeRoots i ν`;

together with the actual standard Levi `M_J = Standard.leviScheme i ν J`,
its inclusion `j = Standard.leviHom i ν J` and the same torus
`iM = Standard.leviTorusHom i ν J`, with the published instances. It then
quantifies over every `D : KPApartmentData i (localFieldOrder F)` for
`(G, S)` and every `DM : KPApartmentData iM (localFieldOrder F)` for
`(M_J, S)`.

Its premise is that some point of `DM` is the restriction of a point of `D`:
`∃ x xM, IsLeviRestriction j x xM`. Here `IsLeviRestriction` is the published
relation `xM_a(m) = x_a(j m)` for all relative roots `a` of `(M_J, S)` and all
`m ∈ M_J(F)` (KP Lemma 6.7.1). Since both apartments are equipollence classes,
the premise makes `DM` the class of restrictions of the points of `D`.

The conclusion has three parts:

1. for every `ψM ∈ DM.affineRoots` there is `ψ ∈ D.affineRoots` with
   `ψ x = ψM xM` for all `x`, `xM` with `IsLeviRestriction j x xM`;
2. the same for the extended affine roots: for every
   `ψM ∈ DM.extendedAffineRoots` there is `ψ ∈ D.extendedAffineRoots` with
   `ψ x = ψM xM` for all such `x`, `xM`;
3. for all `x : D.Apartment` and `xM : DM.Apartment` with
   `IsLeviRestriction j x xM`, if
   `AffineRootSystem.IsSpecialPoint D.affineRoots x`, then
   `AffineRootSystem.IsSpecialPoint DM.affineRoots xM` and
   `AffineRootSystem.IsVertex DM.affineRoots xM`.

`D.affineRoots` and `D.extendedAffineRoots` are the published sets `Ψ ⊆ Ψ′`
of KP Definition 6.3.4 on the reduced apartment `D.Apartment`. An element of
`Ψ′` is an affine functional `ψ` with derivative a relative root `a` such that
`U_{ψ+} ≠ U_ψ`. An element of `Ψ` satisfies the stronger condition
`U_ψ ⊄ U_{ψ+} · U_{2a}(F)`, with `U_{2a}(F) = {1}` when `2a` is not a root.
`IsSpecialPoint Ψ x` says that every `ψ ∈ Ψ` has a parallel `ψ' ∈ Ψ` with
`ψ'(x) = 0` (KP Definition 1.3.39(1)). `IsVertex Ψ x` says that the facet of
`x` is `{x}`.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
§6.7.2 "Hyperplanes and special points", printed pp.233–234 /
PDF pp.264–265, with the definitions of §6.7 and Lemma 6.7.1 on printed
p.233. KP state that the projection `A(S, G) → A(M, S)` induces an inclusion
of dual spaces `A(M, S)* → A(S, G)*`, under which `Ψ(M, S) ⊂ Ψ(S, G)` and
`Ψ′(M, S) ⊂ Ψ′(S, G)`, "clear from Definition 6.3.4". For `α ∈ Ψ(M, S)` the
hyperplane `H_α ⊂ A(S, G)` is the preimage of `H_α ⊂ A(M, S)`. Hence "if
`x ∈ A(S, G)` is a special point, then its image under (6.7.1) is also a
special point. In particular, it is a vertex. The same is also true for extra
special points." KP add that the image of a vertex need not be a vertex.
The "in particular" uses KP Proposition 1.3.43(3) (printed p.30 /
PDF p.61): a special point is a vertex.

The standing hypotheses of Chapter 6 (printed p.195 / PDF p.226) are a
Henselian field with a discrete valuation normalized by `ω(k^×) = ℤ` and a
connected reductive `G`. The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, list no
change to §6.7. Their Chapter 6 entries (PDF p.32) include the
clarification `a = ψ̇` above Remark 6.3.5, which the published
`affineRoots` follows: the root in its defining condition is the derivative
of `ψ`.

Clauses 1 and 2 are the inclusions `Ψ(M, S) ⊂ Ψ(S, G)` and
`Ψ′(M, S) ⊂ Ψ′(S, G)`: the inclusion of dual spaces sends `ψM` to
`ψM ∘ π`, where `π` is the restriction map of Lemma 6.7.1. Clause 3 is the
special-point assertion with its "in particular" consequence.

## Derived scope and provenance

This is a derived formulation, not a literal transcription.

- **Field and Levi subgroups.** As in `LeviApartmentRestrictionStatement`,
  the statement covers nonarchimedean local fields with their normalized
  valuation, and the standard Levi subgroups `M_J` at the same torus. It
  does not cover other Levi subgroups containing `S`.
- **The map.** The Library has no function `A(S, G) → A(M, S)`. The
  statement uses the relation `IsLeviRestriction` in its place. By KP
  Lemma 6.7.1 this relation is the graph of the restriction map once `DM`
  contains one restriction, which is the premise. The inclusions of affine
  roots are expressed through the pullback values `ψ x = ψM xM` on that
  graph.
- **Not formalized.** The preimage description of the hyperplanes `H_α` is
  not stated separately. It follows from clause 1 by taking zero sets. The
  sentence on extra special points (the Library's
  `AffineRootSystem.IsExtraSpecialPoint`) and the remark that images of
  vertices need not be vertices are not formalized here.

The route expected for a proof follows KP. For a root `a` of `(M_J, S)` the
filtration subgroups `U_ψ`, `U_{ψ+}` and the groups `U_{2a}(F)` of `M_J` map
under `j` onto those of `G` for the pulled-back functional. Hence an affine
functional with derivative in `Φ(M_J, S)` is in `Ψ(M_J, S)` (resp. `Ψ′`)
exactly when its pullback is in `Ψ(S, G)` (resp. `Ψ′`). If `x` is special
and `ψM ∈ Ψ(M_J, S)`, the pullback of `ψM` has a parallel affine root of
`G` vanishing at `x`. Its derivative is a rational multiple of a root of
`(M_J, S)`, so it is again a root of `(M_J, S)`, and the affine root
descends to one vanishing at `xM`. For vertexhood: every root of `(M_J, S)`
or its double is the derivative of an affine root of `M_J` (axiom V 0
supplies a finite value of a valuation on each root group). Hence the
derivatives of the affine roots vanishing at a special point span the dual
of the translation space of the reduced apartment, which is the argument of
KP Proposition 1.3.43(3). No existence of apartment data or of any building
is asserted.
