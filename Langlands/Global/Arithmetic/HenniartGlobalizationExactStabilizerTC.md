# Henniart's relative globalization over a totally complex base

This supporting module adapts the Library's relative globalization proof.
`Langlands.Global.RelativeGaloisGlobalizationTC` records that the global
base `F` is totally complex. For an arithmetic relative Weil class family `c`
and a map `q` from the absolute Galois group of a p-adic field `K` to a
finite group, it gives a Galois extension `E/F`, a finite place `v` of `F`
of the same residue characteristic as `K`, and a `ℚ_p`-algebra isomorphism
`K ≃ F_v`. With compact adele quotient for
`F`, every unitary Weil lattice element supported on classes factoring
through `q` is realized by the restriction of the exact class of some
element of `weilImage F E c v`. The number fields and class family are in
universe `0`. The field `K`, quotient, Weil representation carriers and
cuspidal presentations have independent universes `uK`, `uQ`, `uW` and
`uP`. [Library globalization statement](HenniartGlobalizationStatement.md)

`henniartGlobalizationExactStabilizerTC_of_inputs` proves this variant given
the exact-stabilizer datum realization and Proposition 4.8, the totally
complex form of Théorème 2.4, common-closure reciprocity, local induced
restriction, associated central-character comparison and local transfer
reciprocity. The datum realization supplies a Hecke character with a
prescribed restriction to units at the distinguished place and Harris's
exact Weil stabilizer at the auxiliary place. Proposition 4.8 supplies its
weak cuspidal automorphic induction. Théorème 2.4 supplies the local
parabolic induction presentation by unitarizable supercuspidals.
[Datum realization statement](HenniartHarrisDatumExactStabilizerStatement.md),
[Proposition 4.8 statement](HarrisProposition48ExactStabilizerStatement.md),
[Théorème 2.4 statement](../../Automorphic/AssociatedFactorTCStatement.md)

## Implemented proof

1. `exists_witnessedGenerator_realizeExactTC` chooses an irreducible and
   admissible local presentation of the cuspidal class and lifts it to
   universe `uP`. `isWeaklyAssociated_of_isWeaklyAssociatedClass` gives the
   association of that presentation with the relative Weil representation
   `S`. `hasUnitaryCentralCharacter_of_associatedCentralCharacter` gives
   the unitary central character. Over the totally complex base the
   induction hypothesis now supplies the data for
   `WitnessedGenerator.ofUnitaryInduction`. `localUnitaryExpansion_spec`
   identifies its Weil element with the exact local restriction of `S`.
   [Witnessed generator construction](HenniartWitnessedGenerator.md)
2. `exists_witnessedGenerator_inducedReciprocityTC` uses
   `weakInductionAssociation_of_local` to associate the induced relative
   Weil representation of the Hecke character with the weak automorphic
   induction. Relative regularity and the conjugate-inverse identity give
   irreducibility and unitarity through the published induced-reciprocity
   theorems. The geometric reciprocity existence theorem and the local
   relative Weil map input give the map at `v`. Where there is a single
   place `u` of `E'` above `v`,
   `continuousRestrict_inducedReciprocityRepresentation_class` computes
   the local restriction as induction of the reciprocity character at `u`.
   `exists_witnessedGenerator_unramifiedTwist` allows any unramified
   modulus-one twist of that class using the local transfer input.
   [Induced-reciprocity generator](HenniartInducedGenerator.md)
3. `exists_weilImage_realizeExact_continuousInduceTC` uses
   `exists_conj_completionWeilMap_range` and
   `continuousInduce_characterClass_eq_along_conj` to transport the
   prescribed Weil character to the distinguished completion of `E'`.
   It uses `Harris.finitePlacesAbove_subsingleton` for uniqueness of the
   place above `P.v`. Geometric reciprocity converts the transported Weil
   character to a field character, and the completion isomorphism gives
   `χ₀` on `F'ˣ`. The exact-stabilizer realization constructs the datum
   from `χ₀` and the normalized common-closure reciprocity family. The
   application of Proposition 4.8 to that datum supplies the cuspidal
   induction for step 2. The datum's unit agreement and
   `discreteValuation_eq_one_of_valued_eq_one` give equality on local
   units. `exists_weilCharacter_eq_mul_unramified` expresses the remaining
   difference as one unramified twist. The proof takes the inverse twist
   in step 2, then commutes it with induction and cancels it on the
   character class. `witnessed_weil_mem` puts the resulting element in
   the Weil image. [Local generator construction](HenniartGeneratorRealization.md)
4. `exists_weilImage_realizeExact_generatorTC` identifies the completion
   used for step 3 with the common completion at `v₀`.
   `completion_ringHom_ext` identifies the two maps because they are
   continuous and agree on the dense base field. The proof uses
   `localRelativeWeilMapExistence` and
   `cuspidalAllLocalIrreduciblePresentationExistence` to supply the local
   map and presentation inputs to step 3.
   [Common-place generator](HenniartGlobalizationReduction.md)
5. `henniartGlobalizationExactStabilizerTC_of_inputs` takes the fixed
   field `M` of an open normal Galois subgroup whose Weil preimage lies in
   `factoringKernelClosure K q`. `henniartCommonBaseRealization` supplies
   the common CM field `F₀` and the paired-place configurations for the
   subextensions of `M`. `finite_extension_le` makes the family finite,
   and `familyGaloisOverfield` contains all its `E'` over `F₀`.
   `NumberField.IsCMField.isTotallyComplex` supplies the witness for the
   returned base. `realizeExact_includeUnitary_mem_map_span` expresses
   the transported exact class in the Brauer span. For each generator,
   `exists_extension_eq` supplies the relevant subextension of `M`,
   and `norm_eq_one_of_trivial_on_finiteIndex` gives modulus one for its
   character. Step 4 realizes each generator in the image of the Weil
   lattice. Closure under the integral span then gives the asserted
   covering property. [Relative globalization proof](HenniartGlobalizationReduction.md)

The paired-place and Brauer steps follow Henniart, *Une preuve simple des
conjectures de Langlands pour GL(n) sur un corps p-adique*, Invent. Math.
139 (2000), `henniart-2000-simple-proof`, Théorèmes 2.4 and 3.1 and
§§3.3–3.7 (pp. 445–451). The use of weak automorphic induction and the
auxiliary condition comes from Harris, *The local Langlands conjecture
for GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998),
`harris-1998-local-langlands`, Proposition 4.8 (p. 201) and (4.12) in the
proof of Lemma 4.7 (p. 204).
[Registered originals](../../../notes/henniart/sources.md)
