# `G(k) = G(k)^♮ · Z_G(S)(k)`

`Langlands.GroupScheme.SimplyConnectedCentralizerProductStatement` is Kaletha–Prasad,
Fact 2.6.22 (printed p.104/PDF p.135), for the minimal Levi subgroup `M = Z_G(S)` of a
maximal split torus `S`, the case to which the source proof reduces.

It quantifies over a field `k`, a commutative group scheme `S`, group schemes `G`, `Z`,
`C`, `D` over `k` and morphisms `i : S → G`, `j : Z → G`, `d : D → G`, `π : C → D`. It
assumes

* `IsSimplyConnectedDerivedCover d π`: `G` is connected reductive, `d` is its derived
  subgroup and `π : C → D` a simply connected central cover;
* `IsMaximalSplitTorus i`;
* `(torusCentralizer i).IsRepresentedBy j`, so `j : Z → G` is the centralizer `Z_G(S)`.

It asserts that every `g ∈ G(k)` is a product `g = (π ≫ d)(c) · j(z)` with `c ∈ C(k)`
and `z ∈ Z(k)`, that is, `G(k) = G(k)^♮ · Z(k)` where `G(k)^♮` is the image of
`G_sc(k) → G(k)` (KP Definition 2.6.20).

## Provenance

KP Fact 2.6.22 states `G(k) = G(k)^♮ · M(k)` for every Levi subgroup `M ⊂ G`; its proof
first reduces to a minimal Levi subgroup `M = Z_G(S)` and then uses the Bruhat
decomposition [Borel, *Linear Algebraic Groups*, IV.21.15] and the equality of the
relative Weyl groups `N_G(S)(k)/Z_G(S)(k)` of `G` and `G_sc`. The formalized statement is
the minimal case; the general Levi case follows from it because every Levi subgroup
contains a minimal one.

In the source the fact sits in §2.6(e), where `k` is a discretely valued Henselian field
with perfect residue field (the convention stated before §2.6(d), printed p.102/PDF
p.133). The proof uses neither the valuation nor the residue field: the Bruhat
decomposition `G(k) = ⋃ U(k) n Z(k) U(k)` over `n ∈ N_G(S)(k)` holds over every field,
the central isogeny `G_sc → D(G)` restricts to isomorphisms of the root groups, so
`U(k) ⊆ G(k)^♮`, and the relative Weyl groups of `G` and `G_sc` agree over every field.
The statement is therefore formalized over an arbitrary field `k`, which generalizes
the source's setting. This file states the proposition; it does not prove it.

Sources:

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition 2.6.20 and
  Fact 2.6.22, printed p.104/PDF p.135. Registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
