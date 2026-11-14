# An invariant metric and semilinear action on the unramified building

This is a derived statement motivated by Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Sections 4.2, 7.6, 7.9 and 9.2.1, with the corrections
of 1 November 2024. Worker 214 designed this interface in the shared Task
6196 draft revision 3; Worker 250 checked the original source passages and
current Library definitions for its publication in Task 6460. It isolates geometric input for the simultaneous
torus-unit and Galois fixed-point construction. The module defines a proposition;
it does not prove that proposition.

## Exact interface

Write `K = inertiaFixedField F`, `G_K = baseChanged F K G` and
`v = MaximalUnramified.valuation F`. For every nonarchimedean local field
`F : Type u`, every connected reductive group scheme `G` over `Spec F`, and
every supplied `C : MaximalUnramified.BuildingData F G_K`, the proposition
requires the following witnesses on the exact existing type
`C.ReducedBuilding`.

1. A metric `m`, complete and nonpositively curved in the KP midpoint sense
   `Langlands.Geometry.Metric.KP.IsNonpositivelyCurved`.
2. `IsIsometricSMul` for the existing action of `rationalPoints G_K`.
3. A group homomorphism
   `ρ : (K ≃ₐ[F] K) →* Equiv.Perm C.ReducedBuilding` satisfying
   `ρ σ (g • z) = rationalConjugate F K G σ g • ρ σ z` for every `σ`, `g`
   and `z`.
4. Isometry of every `ρ σ` and finiteness of every orbit
   `Set.range (fun σ => ρ σ z)`.

The homomorphism provides both the identity and composition laws. All metric
properties refer to the same existential metric, and both actions refer to
the same supplied quotient. The isometric group-action class refers to its
existing multiplication action, rather than an additional chosen action.
The field, coefficient automorphisms and coefficient conjugation are the
Library's actual objects. The private instance only infers the affineness of
the base change from that of `G`; it adds no hypothesis.

The statement is unrestricted in universe and characteristic. It prescribes
no metric normalization, comparison with a topology, continuous orbit maps,
or compatibility of `ρ` with chosen apartment charts. It assumes no maximal
split torus over `F`, stable apartment over `F`, special torus, smooth model,
or fixed point. `C` already supplies a maximal split torus over `K`, an
apartment class and full integer-valued V6 centralizer compatibility. Existence
of such a `C` is a separate issue; the present universal statement does not
itself assert its existence.

## Original-source provenance

The registered book is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered correction document is `kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

The book's Proposition 7.6.3 and Remark 7.6.5, printed pp.264–266 / PDF
pp.295–297, identify the affine apartment realization of the building and its
quotient by the normalizer and point fixers. This is the construction modeled
by the supplied integer-valued apartment quotient. Chapter 9's opening,
printed p.323 / PDF p.354, supplies the applicability of Bruhat–Tits theory
over the actual maximal unramified extension. The extra AS5 hypothesis
specified by the corrections, PDF p.33, must be discharged: the group over
`K` is quasi-split. It is not permissible to treat arbitrary apartment data
as already carrying all building axioms.

Section 4.2, especially Propositions 4.2.1, 4.2.3 and 4.2.7 and Theorem
4.2.10, printed pp.168–173 / PDF pp.199–204, constructs the metric, proves
nonpositive curvature and proves completeness. Corrections PDF pp.27–29
add Axiom 4.1.6 to the Section 4.2 hypotheses, require group invariance of the
metric, and repair the apartment-comparison argument. The completeness proof
uses discrete affine-root and normalizer geometry. It does not require local
finiteness or a finite residue field, and therefore applies to `K`, which is
not a local field.

Proposition 7.9.5, printed p.276 / PDF p.307, constructs building maps from
field and group isomorphisms through the correspondence of parahoric facets.
Section 9.2.1, printed pp.325–326 / PDF pp.356–357, applies this to
`Gal(K/F)` and gives the displayed semilinearity. Its apartment action is
affine. For the required simultaneous isometries, compare the image of a fixed
apartment under each coefficient automorphism with that apartment by a
rational-point conjugator. On the reduced translation space the resulting
linear transformations permute the finite spanning root system; together
with the Weyl group they lie in its finite automorphism group. Average any
positive definite inner product over the subgroup they generate. The
Weyl-invariant result defines the compatible system of apartment metrics
of Section 4.2 and is also invariant under those coefficient linear maps.
The affine coefficient maps are therefore isometries on each apartment.
The uniqueness assertion of Proposition 4.2.1 makes the whole coefficient
action isometric for the same group-invariant building metric. This
argument does not require one apartment to be stable under all coefficient
automorphisms. Thus the statement asks for a compatible metric
choice; it does not claim invariance of every arbitrary scaling of irreducible
root factors.

The replacement paragraph on corrections PDF p.39 proves finite orbits as
follows. For any point, choose an apartment containing it and a finite Galois
subextension over which the corresponding maximal `K`-split torus is defined
and split. The associated open subgroup of `Gal(K/F)` fixes that apartment
pointwise. The full Galois group need not stabilize the chosen apartment.
The additional fixed-point paragraph on the same page is a downstream use;
no bounded-subgroup fixed-point result is a premise of the present statement.

## Why the quantifier includes every supplied datum

This quantifier is a derived interface choice rather than a verbatim source
statement. Full V6 identifies the apartment equipollence class, as in book
Proposition 6.2.6, printed p.216 / PDF p.247; the corrections PDF p.32 do
not change that proposition. The published Library theorem
`integerValuationBuildingSameGroupComparison` works over any integer-valued
field. For two full `IntegerValuationBuildingData` on the same reductive
group it supplies a quotient equivalence intertwining the identical
rational-point action, without requiring a local-field instance on `K`.

Consequently one may construct a genuine KP datum `C₀` with its metric and
coherent coefficient action, then transport both through one such
`G_K(K)`-equivariant equivalence `e : C₀.ReducedBuilding ≃ C.ReducedBuilding`.
Pull the metric across `e` and conjugate the entire homomorphism by `e`.
Completeness and nonpositive curvature are preserved by the resulting
isometry; equivariance preserves rational-point isometry and semilinearity;
conjugation preserves the action laws; and the image of a finite orbit is
finite. Choosing separate equivalences for separate automorphisms would
leave coherence unproved and is not this argument.

## Intended consumer and related interface

Worker 214's private finite-orbit reduction for Task 6196 first builds a
datum adapted to the scalar extension of a prescribed split torus, using
unramified quasi-splitness and `quasiSplitIntegerApartmentExistence`. Published
`torusUnitApartmentFixation` gives a torus-unit-fixed apartment point.
Semilinearity and coefficient stability of the character-valuation kernel
make its finite Galois orbit pointwise fixed by those units. The published
complete NPC bounded-set-stabilizer theorem then supplies a simultaneous
fixed point. This is a conditional consumer, not a proof in this module.

The published `UnramifiedBuildingMetricStatement` and its proof Task 6395
(`e8990485-dc94-4c38-ab46-6b90618a9844`) instead begin with a torus over `F`
whose base change is maximal split and a stable apartment, and require
isometry of the coefficient action already defined from that input. Those
premises are unavailable before the special-torus construction. The present
statement supplies an existential coherent action without them. Its metric
geometry overlaps that proof task and should be shared where possible.

The focused proof successor of this statement is intended to feed the proof
successor of Q1 Task 6412 (`47b6a973-b540-4c42-a3eb-9012b58b50ed`),
which targets `UnramifiedTorusUnitGaloisFixedPointStatement`. These
fixed-point and special-torus statements are downstream consumers. No proof
of this metric/action statement may depend on
`SpecialTorusBoundedModelStatement`, `SpecialTorusIntegralModelStatement`,
`SpecialTorusExistenceStatement`, `UnramifiedSpecialApartmentStatement`,
`ValuationApartmentAxiomsExistenceStatement`, or
`UnramifiedTorusUnitGaloisFixedPointStatement`, directly or indirectly.
