# Proof: standard-Levi split components realize selected-root annihilators

Author: Worker 3895.

`standardLeviCentralDirections` proves the published proposition
`Langlands.GroupScheme.StandardLeviCentralDirectionsStatement.{u}` at an arbitrary
universe `u`. Its type is exactly that Library statement, with no added hypothesis.
The statement covers every field `k`, every connected reductive `G` over `k`, every
maximal split torus `i : T → G`, every generic cocharacter `ν`, every subset `J` of
the actual simple relative roots, every closed representative `j : L → G` of the
choice-free `standardLevi i ν J`, and every split component `a : A → L`.

## Implemented proof

The theorem applies the published conditional assembly
`standardLeviCentralDirections_of_standard_dynamic_characterRestriction`
(module `Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsAssembly`).
That assembly proves every conjunct of the target from four structural propositions.
Here each of the four is discharged by a published proof with no hypotheses:

1. `StandardCocharacterStatement`, by `standardCocharacter`
   (`Langlands.GroupScheme.Rational.StandardCocharacterProof`). It gives a standard
   cocharacter for every subset of the simple relative roots and identifies the
   choice-free standard parabolic, Levi and unipotent functors with its dynamic ones.
2. `DynamicCentralizerReductiveStatement`, by `dynamicCentralizerReductive`
   (`Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`).
3. `DynamicLieStatement`, by `dynamicLie` (`Langlands.GroupScheme.Dynamic.LieProof`).
4. `CharacterRestrictionStatement`, by `characterRestriction`
   (`Langlands.GroupScheme.Rational.CharacterRestrictionProof`). For a split component
   of a connected reductive group, restriction of rational characters is injective and
   has finite-index image.

The proof adds nothing beyond this application. The assembly's own route is as follows.
Standard cocharacters for all faces make the actual simple roots finite and linearly
independent. Rank-nullity for simultaneous evaluation on the real cocharacter space then
gives the codimension formula
`finrank ℝ (rootAnnihilator T J) + Nat.card J = splitTorusRank T`. The
standard-cocharacter comparison identifies the supplied representative's subgroup functor
with a dynamic centralizer, so dynamic reductivity makes `L` connected reductive. The
published containment theorem supplies a closed compatible map `f : A → T`. It is
injective on real cocharacters, and its image contains the selected-root annihilator.
The forward-image theorem, which uses the dynamic Lie statement, gives the reverse
containment. The rank identities follow from injectivity and the codimension formula.
The rational-character identity `rationalCharacterRank L = splitTorusRank A` follows from
integral injectivity and finite index of restriction to `a`.

## Scope

Every object is the published construction: the actual group schemes, maximal split
torus, character and cocharacter lattices, rational-point Weyl quotient, real torus spaces,
the all-test standard-Levi representative and the supplied split component. The proof
keeps arbitrary fields, nonreduced relative roots, empty selections and rank zero, and
it assumes no basis, rank, complement, embedding or realization statement. The real image
equality does not assert equality of integral lattices. The proof composes existing Library
results and relies on no further literature assertion. The source locators and the
derivation of the arbitrary-field formulation are in the target's paired Markdown.
