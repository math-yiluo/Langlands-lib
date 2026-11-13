# Chamber stabilizers of simply connected groups over the maximal unramified extension

This module states that, for a simply connected group over the maximal unramified extension
of a nonarchimedean local field, an element that maps a chamber of the building onto itself
fixes that chamber pointwise. It also proves the easy converse. The main statement is not
proved here; a separate proof task will follow publication.

## The statement

`MaximalUnramified.SimplyConnectedChamberStabilizerStatement.{u}` is the proposition: for

- every nonarchimedean local field `F : Type u`, with `K = inertiaFixedField F` its maximal
  unramified extension;
- every group scheme `G` over `Spec K` with affine structure morphism
  (`[IsAffineHom G.X.hom]`) such that `IsSimplyConnected G`;
- every supplied building datum `C : BuildingData F G`, that is,
  `IntegerValuationBuildingData (MaximalUnramified.valuation F) G` for the normalized
  integer-valued valuation of `K`;
- every chamber `Y` of the reduced building `C.ReducedBuilding` (`C.IsChamber Y`);
- every `g : rationalPoints G` (an element of `G(K)`) with `(g • ·) '' Y = Y`,

we have `g ∈ C.pointwiseFixer Y`, so `g • y = y` for every `y ∈ Y`.

The Library objects used are as follows.

- `IsSimplyConnected G` is the CGP definition in `Langlands.GroupScheme.SimplyConnected.Basic`.
  `G` is semisimple, and every central isogeny `H → G` from a semisimple `K`-group `H` is an
  isomorphism. The definition only tests isogenies defined over `K`. By the published theorem
  `isSimplyConnectedFieldExtension`, the condition passes to every field extension, in
  particular to an algebraic closure of `K`. So `G` is simply connected in the geometric
  sense used by Kaletha–Prasad.
- `C.ReducedBuilding` is the reduced building `B(G)` of KP Remark 7.6.5, the quotient (7.6.2)
  of `G(K) × A(S)` built from the apartment `A(S)` of `C`.
- `C.IsChamber Y` says that `Y = g₀ · Ca` for some `g₀ ∈ G(K)` and some chamber `Ca` of the
  apartment for the affine roots `Ψ` of `C`, a `G(K)`-translate of an apartment chamber
  (KP Proposition 7.6.3 and Remark 7.6.5).
- `C.pointwiseFixer Y` is the subgroup of `G(K)` fixing every point of `Y`.

`G` is an arbitrary simply connected `K`-group, not necessarily the base change of an
`F`-group. A `K`-group is the more general setting and the more natural one for the source
results below. In Task 6208 the statement is applied to `baseChanged F K G₀` for a simply
connected `F`-group `G₀`. Simple connectedness passes to that base change by the published
field-extension theorem `isSimplyConnectedFieldExtension`.

## Also in this module

- `IntegerValuationBuildingData.smul_image_eq_of_mem_pointwiseFixer` is proved without
  hypotheses. For any integer-valuation building datum `B`, any subset `Y` of its reduced
  building and any `g ∈ B.pointwiseFixer Y`, it gives `(g • ·) '' Y = Y`. The proof unfolds
  the pointwise fixer with `KPApartmentData.mem_pointwiseFixer` and checks both inclusions
  pointwise.
- `MaximalUnramified.smul_image_eq_iff_mem_pointwiseFixer` assumes the statement. For a
  simply connected `K`-group `G`, any `C : BuildingData F G`, any chamber `Y` and any `g`, it
  gives `(g • ·) '' Y = Y ↔ g ∈ C.pointwiseFixer Y`. The forward direction is the statement
  and the reverse direction is the previous lemma. So under the statement the stabilizer of
  a chamber is exactly its pointwise fixer.

## Source

The statement is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), for a chamber
over the field `k = K`.

- **4.1.12(1)** (printed p. 161, PDF p. 192): "The group G(k)^0_F is the stabilizer, as well
  as the pointwise stabilizer, of F in G(k)^0." Here `F` is a facet of `B(G)`.
- **Remark 4.1.13** (same page): "Axiom 4.1.9 and the identities G_sc(k)^0 = G_sc(k) and
  B(G) = B(G_sc) imply the following. If Ω is a subset of a facet of B(G), the stabilizer of
  Ω in G(k)^♮ fixes Ω pointwise." For a simply connected `G` we have `G = G_sc` and
  `G(k)^0 = G(k)^♮ = G(k)`, so the stabilizer of a chamber in `G(k)` fixes it pointwise.
- **9.3.26** (printed p. 344, PDF p. 375) proves the same fact in the unramified-descent
  chapter: "Assume that G is semi-simple and simply connected. … Since G(k)^0 = G(k), the
  stabilizer of F in G(k) is … hence the stabilizer of F in G(k) fixes F and F pointwise."

Chapter 4 of Kaletha–Prasad is an axiomatic summary. Its setting (printed p. 157, PDF
p. 188) is a field `k` with a discrete valuation whose ring of integers "is Henselian and the
residue field f is perfect". `K = inertiaFixedField F` is such a field: it is an algebraic
extension of the complete field `F`, so it is Henselian, its valuation is discrete, and its
residue field is an algebraic closure of a finite field. The book states that the axioms are
established in Chapters 6–9.

The Library statement is a specialization: only chambers (not arbitrary facets or subsets of
facets) and only the field `K`. The source facet `F` corresponds to `Y`, the source
stabilizer to the condition `(g • ·) '' Y = Y`, and the pointwise stabilizer to
`C.pointwiseFixer Y`.

The authors' corrections of 1 November 2024 (source `kaletha-prasad-2024-corrections`)
list no entry for 4.1.12, Remark 4.1.13 or 9.3.26. They do correct Axiom 4.1.9, from which
4.1.12 is derived (PDF p. 27): "(B(G) as in Axiom 4.1.1)" is added, and "is precisely the"
parabolic subgroup becomes "is a" parabolic subgroup. Neither change affects 4.1.12(1).

## Scope: arbitrary supplied building data

The statement quantifies over every `C : BuildingData F G`. Such a datum supplies a maximal
split torus `S`, an apartment `A(S)` (an equipollence class of valuations of the root datum
of `(G, S)` for the order of `MaximalUnramified.valuation F`), the centralizer `Z = Z_G(S)`,
and the ω-compatibility of every valuation in `A(S)` together with Axiom V 6 on `Z(K)`. It
asserts no building axiom.

Kaletha–Prasad prove the stabilizer result for their own apartment of `G` over `k`. A
proof of the Library statement for arbitrary `C` therefore has to identify the apartment of
`C` with the Kaletha–Prasad apartment, or reprove the result directly from the data in `C`.
The expected route uses uniqueness, up to equipollence, of root-datum valuations that are
ω-compatible on `S(K)` and satisfy V 6 on `Z(K)` (compare `KPApartmentData.exists_eq_orbit`
with `IsSplitTorusCompatible`, and `IntegerValuation.IsOmegaCompatible`). Without that
uniqueness the statement is not a direct citation. This is recorded in the context of
Task 6208 ("Arbitrary `C` and `D`"). The companion `UnramifiedParahoricModelStatement` also
quantifies over arbitrary building data in the same way.

The statement is an interface: nothing here constructs a valuation, an apartment, a
building or an integral model, or proves that `BuildingData F G` is inhabited.
