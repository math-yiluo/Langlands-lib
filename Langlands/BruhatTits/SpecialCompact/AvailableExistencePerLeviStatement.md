# Existence of a special maximal compact subgroup for available Bruhat–Tits data, with an assignment for each standard Levi: statement target

This module states the proposition
`Langlands.BruhatTits.SpecialCompact.AvailableSpecialMaximalCompactExistencePerLevi`.
It is a proposition-valued definition, not a proof.

It corrects the published target `AvailableSpecialMaximalCompactExistence` (module
`Langlands.BruhatTits.SpecialCompact.AvailableExistenceStatement`). The two have the same
quantifiers and the same ambient clauses. They differ in one place: here each standard Levi
clause has its own assignment `𝔅M`, while the published target uses the ambient assignment
`𝔅` for every Levi. The published target has no known proof; the section
[Why the published target is replaced](#why-the-published-target-is-replaced) explains why. It
stays published unchanged.

## Statement

For every universe level `u`, the target quantifies over:

- a nonarchimedean local field `F : Type u`, with
  `[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`.
  Both mixed and equal characteristic are included, with no tameness,
  residue-characteristic or splitness restriction;
- a group scheme `G` over `Spec F` with `hG : IsConnectedReductive G`;
- a commutative group scheme `S` with `i : S.toGrp ⟶ G` and
  `hi : IsMaximalSplitTorus i`, the chosen maximal split torus;
- `ν : cocharacterLattice S` with `IsGenericCocharacter i ν`. This chooses the positive
  system, and so the minimal parabolic `P_∅` and its simple roots `simpleRelativeRoots i ν`.

The instances `IsAffineHom G.X.hom` and `Mono i.hom.hom.left` come from `hG.isAffineHom`
and `hi.isSplitSubtorus.mono`, as in `AvailableSpecialMaximalCompactExistence`.

The conclusion is that there are an assignment `𝔅 : KPBuildingAssignment.{u}` and apartment
data `D : KPApartmentData i (localFieldOrder F)` with the following properties.

1. `𝔅.IsAvailableFor F G hG`: Bruhat–Tits theory is available for `G` over `F` in `𝔅`.
   All ten axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and
   4.1.22 of the corrected KP Definition 4.1.26 hold for `G`, as formalized by
   `Langlands.Geometry.Building.KPBuildingAssignment.IsAvailableFor`.
2. The data `𝔅.datum F G hG` are based on the given torus and on `D`:
   `(𝔅.datum F G hG).base.S = S`, `HEq (𝔅.datum F G hG).base.i i` and
   `HEq (𝔅.datum F G hG).base.apartment D`.

There is also a point `x : D.Apartment` such that the following hold.

3. `D.IsSpecialApartmentVertex x`: `x` is a special point and a vertex of the affine root
   system of the reduced apartment (KP Definition 1.3.39).
4. `SpecialCompactProperties F i ν (D.specialCompactSubgroup x)`. The subgroup
   `K_0 = D.specialCompactSubgroup x` unfolds to
   `D.compactStabilizer (D.apartmentMap x) = G(F)^1 ∩ G(F)_x`. It is algebraically
   bounded, open and maximal among bounded subgroups. It is compact, open and maximal among
   compact subgroups. Every element of the relative Weyl group `N(F)/Z(F)` has a
   representative in `N(F) ∩ K_0`. For every `J ⊆ simpleRelativeRoots i ν`, the identity
   `K_0 ∩ P_J = (K_0 ∩ M_J)(K_0 ∩ U_J)` holds literally in `G(F)`.
5. Let `J ⊆ simpleRelativeRoots i ν`, and let `M_J = Standard.leviScheme i ν J` be the actual
   standard Levi with the torus `Standard.leviTorusHom i ν J : S → M_J`. Its instances are
   `IsAffineHom M_J.X.hom` from `Standard.isClosedSubgroup_leviHom` and
   `Mono (Standard.leviTorusHom i ν J).hom.hom.left` from
   `Standard.isMaximalSplitTorus_leviTorusHom`. Then there are
   `hM : IsConnectedReductive M_J`, an assignment `𝔅M : KPBuildingAssignment.{u}` and
   `DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)` such that:
   - `𝔅M.IsAvailableFor F M_J hM`, so Bruhat–Tits theory is available for `M_J` in `𝔅M`;
   - `(𝔅M.datum F M_J hM).base.S = S`,
     `HEq (𝔅M.datum F M_J hM).base.i (Standard.leviTorusHom i ν J)` and
     `HEq (𝔅M.datum F M_J hM).base.apartment DM`;
   - there is a point `xM : DM.Apartment` with `SpecialLeviRestriction F ν D x J DM xM`.
     That is, `xM` is a special vertex of the apartment `DM` and is restricted from `x`
     (KP Lemma 6.7.1). Its compact stabilizer has the properties of item 4 for
     `(M_J, S, ν)`. It is the preimage of `K_0` in `M_J(F)`, whose image in `G(F)` is
     `K_0 ∩ M_J(F)`.

The same `𝔅`, `D` and `x`, and hence the same `K_0`, serve every `J`. The assignment `𝔅M`
may depend on `J`, and need not be `𝔅`.

The predicates `SpecialCompactProperties` and `SpecialLeviRestriction` are documented in
`Langlands.BruhatTits.SpecialCompact.Properties`. The subgroup `specialCompactSubgroup` and
the predicate `IsSpecialApartmentVertex` are defined in
`Langlands.Geometry.Building.SpecialCompact`.

## Why the published target is replaced

`AvailableSpecialMaximalCompactExistence` asks for one assignment `𝔅` whose datum at `G` has
the torus inclusion `i`, and whose datum at each `Standard.leviScheme i ν J` has the torus
inclusion `Standard.leviTorusHom i ν J`. The datum `𝔅.datum F G hG` of an assignment
depends only on the field with its instances and on the group term `G`. Its other arguments,
the instance `IsAffineHom G.X.hom` and the proof of `IsConnectedReductive G`, are
propositions. So two group terms that are equal get the same datum. The module
`Langlands.BruhatTits.SpecialCompact.AvailableExistenceCoincidence` proves in Lean the two
consequences of this:

- `heq_leviTorusHom_of_availableSpecialMaximalCompactExistence`: the published target implies
  that if `Standard.leviScheme i ν J₁ = Standard.leviScheme i ν J₂` as terms, for
  `J₁, J₂ ⊆ simpleRelativeRoots i ν` and generic `ν`, then
  `HEq (Standard.leviTorusHom i ν J₁) (Standard.leviTorusHom i ν J₂)`;
- `heq_torusHom_of_eq_leviScheme_of_availableSpecialMaximalCompactExistence`: the published
  target implies that if `G = Standard.leviScheme i ν J` as terms, for
  `J ⊆ simpleRelativeRoots i ν` and generic `ν`, then `HEq i (Standard.leviTorusHom i ν J)`.

The first proof takes the Levi clauses at the two coinciding group terms; the second takes
the ambient clause and the Levi clause. Each composes the resulting heterogeneous
equalities with the lemma `heq_datum_base_i_of_eq` (equal group terms give heterogeneously
equal torus inclusions).

These conclusions are out of reach. `Standard.leviScheme i ν J` is the cut group scheme
`Corepresented.intersectionScheme`, the spectrum of a quotient of the coordinate ring of
`G`. An equation between such a term and another group-scheme term, such as the arbitrary
`G`, is an equation between structures whose fields are types (carriers of schemes,
quotient rings). Lean cannot refute such equations in general, because type formers such
as quotients and spectra are not provably injective, and in general it cannot prove them
either. When
such an equation is assumed, nothing in the Library relates the two torus inclusions: each
of `i` and `Standard.leviTorusHom i ν J` is a morphism into its own term, and
`Standard.leviTorusHom i ν J` is `i` factored through the closed inclusion
`Standard.leviHom i ν J`. So no proof of either consequence is known, and none of the
published target. A proof would also have to build a single assignment from separately
chosen data for `G` and for every `M_J`, and that construction meets the same coincidences.

The per-Levi form avoids them: each Levi has its own `𝔅M`, so its datum is never compared
with the datum of `G` or of another Levi. This is the shape of the published
`AvailableSpecialLeviCompactStatement` (module
`Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactStatement`), whose Levi
assignment `𝔅M` is also existential. The Levi clause still says that the preimage of `K_0` in
`M_J(F)` is the compact stabilizer of a special vertex of available data for `M_J` based at
`S`, which is the content of Renard V.5.1(5). Neither Renard nor KP requires the data for
`M_J` and for `G` to come from one assignment.

## Formulation choices

- **Matching the torus.** In `KPBuildingDatum G`, the maximal split torus `S`, its inclusion
  `i` and the apartment `A(S)` are fields of `base : ParahoricBuildingData G`. The target
  names `i` and `D` explicitly and requires the data to have exactly this torus and
  apartment. The type of `base.i` depends on `base.S`, and the type of `base.apartment` on
  `base.i`, so these are stated as `base.S = S` and heterogeneous equalities. With them,
  `K_0` and `xM` are the subgroup and the point of the available data themselves.
- **Levi reductivity.** `𝔅M.datum` takes a proof that the group is connected reductive, and
  clause 5 asserts it with the existential `hM`. (The Library proves it separately, as
  `standardLevi_isConnectedReductive`.) `IsConnectedReductive` is a proposition, so the data
  do not depend on the choice of `hM`.
- **The assignments.** `𝔅` and each `𝔅M` assign data to every connected reductive group over
  every nonarchimedean local field in universe `u`. The target asks for availability only
  at `G` in `𝔅` and at `M_J` in `𝔅M`, as in KP's phrase "Bruhat–Tits theory is available for
  `G` over `k`". The global condition `IsValid` is not required. `𝔅` may depend on
  `(F, G, S, i, ν)`, and `𝔅M` also on `J`.
- **Levi data.** The relation of the Levi data to `G` is `SpecialLeviRestriction`, which
  compares valuations through the restriction of KP Lemma 6.7.1 and compares compact
  stabilizers inside `M_J(F)`. The target does not state that the building of `M_J` embeds
  in that of `G`.

## Relation to other targets

- `AvailableSpecialMaximalCompactExistence` (`AvailableExistenceStatement`): identical
  except that its Levi clauses use the ambient `𝔅`. As explained above, it has no known
  proof.
- `SpecialMaximalCompactExistence` (`ExistenceStatement`) asks only for `KPApartmentData`
  with `SatisfiesApartmentAxioms` and Axiom 4.1.2, without availability. The published
  module `Langlands.BruhatTits.SpecialCompact.AvailableExistenceReduction` derives it from
  `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`.
- The same module proves
  `availableSpecialMaximalCompact_perLevi_of_bruhatTitsAvailability`, whose conclusion, for
  fixed `F, G, hG, S, i, hi, ν`, is the body of this target. So this target follows from
  `BruhatTitsAvailabilityStatement` (the availability part of KP Theorem 9.2.7). That
  premise is not proved in the Library.
- Renard V.5.1(1) (Iwasawa) and (4) (Cartan) are not stated here.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Definition 1.3.39 (PDF page 60); Definition 2.2.1 and Fact 2.2.3 (PDF page 101);
  Axioms 4.1.1–4.1.22 and Definition 4.1.26 (PDF pages 188–196); Theorem 4.2.15(1) and its
  proof (PDF pages 204–205); Lemma 6.7.1 and §6.7.2 (PDF pages 264–265);
  Definition 7.4.1(4) (PDF page 286); Theorem 9.2.7 (PDF page 360) and its proof in §9.5
  (PDF pages 394–395).
- Corrections `kaletha-prasad-2024-corrections`, 1 November 2024, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`: the corrected list
  of axioms in Definition 4.1.26 (PDF page 27) and the corrections to §4.1 and §4.2 (PDF
  pages 27–29).
- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
  `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: Théorème V.5.1,
  printed page 122, PDF page 128.

Given available data, KP Theorem 4.2.15(1) gives the properties of `K_0` at a special
vertex; its bounded form is the source form, and the compact form follows over a local field
by Fact 2.2.3. Renard V.5.1 gives (2), (3) and (5). The assignment formulation, with an
available assignment for each standard Levi, is derived: neither source states it in these
terms. It transcribes the source results for the published objects and does not prove them.

## Scope

`K_0` is `G(F)^1 ∩ G(F)_x`. It is not the full reduced fixer and not the parahoric
`P_x = Z(F)^0 · G(F)^♯_x` (KP Definition 7.4.1(4)), which may be strictly smaller. The rank-zero
case is included: for `J = ∅` the Levi `M_∅ = Z_G(S)` has no relative roots, and the
apartment axioms use the rank-zero form of AR 1, which admits an empty affine root system on a
one-point apartment.
