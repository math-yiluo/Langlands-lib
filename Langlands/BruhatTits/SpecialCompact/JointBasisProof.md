# One geometric witness for the special compact and simultaneous basis: proof

`Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` proves
exactly `JointSpecialCompactBasisExistenceStatement.{u}` (module
`Langlands.BruhatTits.SpecialCompact.JointBasisStatement`) for an arbitrary
universe `u`. [Statement](JointBasisStatement.md)

The scope is the full scope of the statement: every nonarchimedean local field
`F : Type u` of either characteristic and any residue characteristic, every
connected reductive group scheme `G` over `Spec F`, every maximal split torus
`i : S.toGrp ⟶ G` and every generic cocharacter `ν` of `S`. The theorem has no
hypotheses; it adds no rank, splitness, quasi-splitness, tameness or
residue-characteristic condition. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The Lean term is one application:

```
jointSpecialCompactBasisExistence_of_availability_and_basis
  Langlands.Geometry.Building.bruhatTitsAvailability
  availableSimultaneousStandardBasis
```

- `jointSpecialCompactBasisExistence_of_availability_and_basis`
  (`JointBasisFinalAssembly`) derives the target from
  `BruhatTitsAvailabilityStatement` and
  `AvailableSimultaneousStandardBasisStatement`.
  [Assembly](JointBasisFinalAssembly.md)
- `Langlands.Geometry.Building.bruhatTitsAvailability`
  (`Langlands.Geometry.Building.BruhatTitsAvailabilityProof`) proves
  `BruhatTitsAvailabilityStatement.{u}`: one `KPBuildingAssignment` satisfies
  `IsValid`, which contains all ten axioms of corrected Kaletha–Prasad
  Definition 4.1.26 for every connected reductive group over every
  nonarchimedean local field in universe `u`.
  [Availability](../../Geometry/Building/BruhatTitsAvailabilityProof.md)
- `availableSimultaneousStandardBasis` (`AvailableBasisProof`) proves
  `AvailableSimultaneousStandardBasisStatement.{u}`: at every special vertex
  of the apartment of a valid assignment, and for every generic cocharacter,
  the special compact properties, standard-Levi inheritance and the
  simultaneous standard basis hold for the same compact stabilizer.
  [Basis](AvailableBasisProof.md)

## Where the common witnesses come from

The proof of the assembly, which this theorem applies, constructs all
witnesses from one valid assignment and so proves every conjunct at one
`D`, `x`, `Z`, `j`, `s` and `h`:

1. From the valid assignment given by `bruhatTitsAvailability`, published
   `validAssignmentTorusRebasing` gives a valid assignment `𝔅` whose datum for
   `G` has torus equal to the given `S` and inclusion heterogeneously equal to
   the given `i`.
2. Write `V` for the valuation-building data of `(𝔅.datum F G hG).base`.
   Published `joint_of_valuationBuildingData` (`JointBasisReductionProof`)
   takes `D := V.apartment`, the represented centralizer `V.centralizer` with
   its closed inclusion `j`, factorization `s` and restriction-evaluation
   bijection `h`, and a special vertex `x` of `D` given by published
   `availableSpecialVertexExistence`. It substitutes the torus equalities of
   step 1, so that `D : KPApartmentData i (localFieldOrder F)` for the original
   `i`.
3. At this one `D` and `x`, with `K0 = D.specialCompactSubgroup x`:
   - `availableSimultaneousStandardBasis` gives `SpecialCompactProperties`,
     `SpecialLeviInheritance` and `SimultaneousStandardBasisAt`;
   - published `Iwasawa.availableIwasawa` gives the ambient
     `Iwasawa.ParabolicPointProductFamily`;
   - published `validSpecialCompactRenardCartanComparison`
     (`JointBasisCartanAssembly`) gives both
     `SpecialCompactRenardComparison D x ν j s h` and
     `SpecialCompactStandardLeviCompatibility D x ν s h j`, with the same
     centralizer witnesses `Z`, `j`, `s`, `h`;
   - for every `J ⊆ simpleRelativeRoots i ν`, published
     `availableSpecialLeviCompact` gives available data for the actual
     standard Levi, with the prescribed torus and a special vertex whose
     special compact subgroup is exactly `D.specialCompactLeviSubgroup ν J x`;
     `Iwasawa.availableIwasawa` applies there, and
     `parabolicPointProductFamily_of_heq` transports it to
     `Standard.leviTorusHom i ν J`, using `isGenericCocharacter_leviTorusHom`
     for genericity of `ν` in the Levi.

## Structural prerequisites used

The only building input is the valid corrected KP assignment supplied by
`bruhatTitsAvailability`; its own proof applies
`bruhatTitsAvailabilityReduction` to `groupAxiomsExistence`, which supplies
the one-group axioms (parahoric building data, root-group action, Iwahori
decomposition and integral models). The proof uses no partial interface
(`KPApartmentAxioms`, `ValuationBuildingAxioms`) as a hypothesis and no
proposition target as a premise. `K0` is the character-kernel stabilizer
`G(F)^1 ∩ Stab(D.apartmentMap x)` of the statement; compactness, openness and
maximality of `K0` are proved conclusions, coming from
`SpecialCompactProperties`.

## Provenance

The statement formalizes Renard, *Représentations des groupes réductifs
p-adiques*, V.5.1–V.5.2, at one geometric special vertex; its Markdown gives
the source tuples. The building input is the corrected Definition 4.1.26 part
of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 9.2.7,
with the axiom list of the authors' 1 November 2024 corrections. This proof is
an internal composition of the published Library theorems named above.
