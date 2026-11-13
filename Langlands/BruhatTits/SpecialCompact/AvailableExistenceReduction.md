# Special maximal compact subgroups from a valid corrected KP assignment

This module proves conditional results only. It reduces two existence targets for
a special maximal compact subgroup to the unproved published proposition
`Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`. That proposition
says that some `KPBuildingAssignment` is valid in the sense of corrected
Kaletha–Prasad Definition 4.1.26 (the availability part of KP Theorem 9.2.7). The
module does not prove that proposition, so none of its results is an
unconditional existence theorem.

The record entry is the definition
`specialMaximalCompactExistenceOfBruhatTitsAvailability`. Its type is the
implication

```lean
BruhatTitsAvailabilityStatement.{u} → SpecialMaximalCompactExistence.{u}
```

where `SpecialMaximalCompactExistence` is the published supplementary target of
module `Langlands.BruhatTits.SpecialCompact.ExistenceStatement`. The entry is the
theorem `specialMaximalCompactExistence_of_bruhatTitsAvailability`, restated as a
`def` so that the record has a definition entry. It adds no hypothesis and no new
mathematical notion.

## Declarations

- `exists_based_apartment`. Let `V : ValuationBuildingData G` and `i : S → G`, with
  `V.S = S` and `HEq V.i i`. Then there are a centralizer datum `C` and apartment
  data `D` for `i` with `HEq V.apartment D`, `D.SatisfiesApartmentAxioms C` and
  `D.HasBoundedOpenStabilizers`, given that `V` satisfies the corresponding
  axioms. Any special vertex of `V`'s apartment also gives a special vertex of
  `D`. The proof takes `V` apart into its fields, substitutes the torus equality and
  the heterogeneous equality of the inclusions, and then uses `V`'s own fields as
  `C` and `D`.
- `exists_specialLeviRestriction_of_valid`. Fix a valid assignment, a maximal
  split torus `i` of `G`, a centralizer datum `C`, `ω`-compatible apartment data
  `D` whose affine roots have every relative root as a derivative, a generic
  cocharacter `ν`, a set `J` of simple relative roots, and a special vertex `x` of
  `D`. Then every `ω`-compatible apartment `DM` of the actual standard Levi
  `M_J = Standard.leviScheme i ν J`, at the torus `Standard.leviTorusHom i ν J`,
  has a point `xM` with `SpecialLeviRestriction F ν D x J DM xM`.
- `specialMaximalCompact_of_based_valid` (the core theorem). Let `𝔅` be a valid
  assignment whose datum for `G` has torus `S` and inclusion `i` (as an equality and
  a heterogeneous equality). For a generic `ν` it constructs the following.
  First, `C` and `D` with `HEq (𝔅.datum F G hG).base.apartment D`, the apartment
  axioms and Axiom 4.1.2. Second, a special vertex `x` of `D` with
  `SpecialCompactProperties F i ν (D.specialCompactSubgroup x)`. Third, for every
  `J ⊆ simpleRelativeRoots i ν`, a proof `hM` that `M_J` is connected reductive, a
  valid assignment `𝔅M` and `CM`, `DM` with the following properties. The datum of
  `𝔅M` for `M_J` has torus `S` and inclusion `Standard.leviTorusHom i ν J`, and
  `DM` is its apartment. `DM` satisfies the apartment axioms for `CM` and Axiom
  4.1.2, and some `xM` satisfies `SpecialLeviRestriction F ν D x J DM xM`.
- `specialMaximalCompactExistence_of_bruhatTitsAvailability`: the implication
  displayed above.
- `availableSpecialMaximalCompact_perLevi_of_bruhatTitsAvailability`. From
  `BruhatTitsAvailabilityStatement` it gives the conclusion of the published
  `AvailableSpecialMaximalCompactExistence`, with one change: each Levi clause uses
  its own assignment `𝔅M`, not the ambient `𝔅`. The ambient part is exactly as in
  that target. It gives `𝔅.IsAvailableFor F G hG`, the torus `S`, the inclusion `i`,
  the apartment `D`, and a special vertex `x` of `D` with the special compact
  properties. For every `J` it gives `hM`, an assignment `𝔅M` available for `M_J`
  whose datum for `M_J` has torus `S`, inclusion `Standard.leviTorusHom i ν J` and
  apartment `DM`, and some `xM` with `SpecialLeviRestriction F ν D x J DM xM`.
- `specialMaximalCompactExistenceOfBruhatTitsAvailability`: the record entry.

## Implemented proofs

`exists_specialLeviRestriction_of_valid` works as follows. The published
`prescribedLeviSpecialVertex` projects the ambient special point `x` to a special
vertex `xM` of the prescribed Levi apartment `DM`. It also gives the literal
valuation restriction `IsLeviRestriction (Standard.leviHom i ν J) x xM`. The Levi
is connected reductive by `standardLevi_isConnectedReductive`. The cocharacter `ν`
stays generic for the Levi torus by `isGenericCocharacter_leviTorusHom`. The
published `availableSpecialCompactProperties_of_omegaCompatibleApartment`, applied
once to `M_J, DM, xM` and once to `G, D, x`, gives the special compact properties of
both compact stabilizers. The published
`standardLeviSpecialCompactSubgroup_le_of_compatible` puts the Levi stabilizer at
`xM` inside the preimage `D.specialCompactLeviSubgroup ν J x` of the ambient one.
That preimage is compact by `isCompact_specialCompactLeviSubgroup_of_isCompact`,
since the actual Levi inclusion is a closed immersion. The Levi stabilizer is
maximal among compact subgroups, so the inclusion is an equality.

`specialMaximalCompact_of_based_valid` works as follows. The valid assignment is
available for `G` (`IsValid.isAvailableFor`). Availability gives the apartment
axioms (through `IsAvailableFor.satisfiesPartialBuildingAxioms`) and Axiom 4.1.2
(the field `boundedSubgroups`). The published `availableSpecialVertexExistence`
gives a special vertex. `exists_based_apartment` moves all of these to apartment
data at the given torus `i`. `availableSpecialCompactProperties_of_omegaCompatibleApartment`
gives the special compact properties at `x`. For each `J`, the published
`validAssignmentTorusRebasing` turns `𝔅` into a valid assignment `𝔅M` whose datum for
`M_J` has torus `S` and inclusion `Standard.leviTorusHom i ν J`.
`exists_based_apartment` applied to that datum gives `CM` and `DM`, and
`exists_specialLeviRestriction_of_valid` gives `xM`. The derivative-root hypothesis
is the field `derivativeRoots_affineRoots` of the ambient apartment axioms.

The two final theorems first obtain a valid assignment from
`BruhatTitsAvailabilityStatement`. They rebase it at `(G, i)` with
`validAssignmentTorusRebasing` and apply the core theorem. Then they forget the
data that the target does not ask for: the centralizer data, and the assignments
for `SpecialMaximalCompactExistence`. Validity gives the required availability.

## Relation to `AvailableSpecialMaximalCompactExistence`

The published target asks for one assignment `𝔅` whose datum for `G` has the torus
`i`, and whose datum for each `Standard.leviScheme i ν J` has the torus
`Standard.leviTorusHom i ν J`. An assignment's datum depends only on the field and
on the group term; its other arguments are propositions. Suppose two of these
groups are equal as terms. This can be `G` and some `M_J`, or `M_{J₁}` and
`M_{J₂}` with `J₁ ≠ J₂`. Then the target forces the corresponding tori to be
heterogeneously equal. No Lean argument for that is available, so this module does
not prove that target, even conditionally. It proves the variant in which each
Levi clause has its own available assignment, as the published
`AvailableSpecialLeviCompactStatement` does. The ambient datum, the apartment `D`,
the special vertex `x`, the subgroup `K_0` and the relation
`SpecialLeviRestriction` are the same as in the published target.

## Provenance and scope

This is derived content. It composes published Library results for the published
statements `BruhatTitsAvailabilityStatement` and `SpecialMaximalCompactExistence`,
and for the per-Levi-assignment variant of `AvailableSpecialMaximalCompactExistence`
written out in the theorem. Mathematically, it implements the following route.
Bruhat–Tits theory is available for every connected reductive group over a
nonarchimedean local field (KP Theorem 9.2.7). By KP Theorem 4.2.15(1), the
compact stabilizer `K_0` of a special vertex is then a special maximal compact
subgroup. Renard, Théorème V.5.1 (printed p.122 / PDF p.128) gives its properties
(2), (3) and (5). The Library's proof of the compact properties uses its own route
(compact cores in `ω`-compatible apartments and compact maximality in the standard
Levis). It does not follow the text of the sources.

The single building premise is `BruhatTitsAvailabilityStatement`. Every other input
is a published Library proof. There is no restriction on characteristic, residue
characteristic, rank, splitness, quasi-splitness or ramification. All results hold
at an arbitrary universe `u`.

Sources:

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Theorem 4.2.15(1) (PDF pages 204–205) and Theorem 9.2.7 (PDF page 360).
- Renard, *Représentations des groupes réductifs p-adiques*,
  `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
  Théorème V.5.1, printed page 122, PDF page 128.
