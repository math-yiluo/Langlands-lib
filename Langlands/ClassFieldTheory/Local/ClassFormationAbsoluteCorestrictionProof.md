# Simultaneous local class formation

The theorem
`Langlands.ClassFieldTheory.Local.localAbsoluteCorestrictionCompatibleClassFormation`
proves the published proposition
`Langlands.ClassFieldTheory.Local.LocalAbsoluteCorestrictionCompatibleClassFormationStatement.{u}`
(module `ClassFormationAbsoluteCorestrictionStatement`) with no hypotheses: for every prime `p`
there is a raw local invariant family `I : InvariantFamily.{u,u} p` satisfying
all fifteen conclusions listed there. These are arithmetic normalization, the
continuous invariant properties, the finite relative class-formation axioms,
relative conjugacy, relative corestriction, the five fundamental-class laws,
Tate isomorphisms in every integer degree, positive Tate inflation, Tate
transfer compatibility, ordinary inflation, and absolute corestriction.

The mathematics is Serre, *Local Fields*, Chapter XIII (local class formation),
§§3–4, together with Chapter XI, §3 (consequences of the class-formation axioms)
and Chapter IX, §8 (Tate's theorem). This module only assembles published
results. Each one is cited by its Lean name below, and its own module explains
its proof.

## Conditional assembly

`localAbsoluteCorestrictionCompatibleClassFormation_of` takes Tate's theorem
`hTate : Langlands.Tate.TateCupIsomorphism.{u}` and unramified `H²` exhaustion
`hEx : UnramifiedH2Exhaustion.{u}` as arguments. For a prime `p` it uses the
witness `I := localInvariantFamily hEx p` (module `LocalInvariantFamily`) and
proves the fifteen conclusions in this order:

1. **Continuous invariant properties.** `localInvariantFamilyContinuous hEx p`
   (module `LocalInvariantFamilyContinuousProof`).
2. **Relative class formation.** `I.RelativeClassFormation` has four parts:
   - relative `H¹` vanishing, by `finiteRelativeH1Vanishing F.Carrier L`
     (module `RelativeH1Proof`);
   - relative images, by `localInvariantFamilyRelativeImages hEx p`;
   - inflation compatibility, by `localInvariantFamilyInflation hEx p`;
   - restriction compatibility, by `localInvariantFamilyRestriction hEx p`.

   Each comes from the module of the same name with suffix `Proof`.
3. **Relative conjugacy.** `invariantRelativeConjugacy p I` applied to the
   inflation and restriction parts of step 2 (module
   `InvariantRelativeConjugacyProof`).
4. **The five fundamental-class laws.** `relativeFundamentalClassConsequences p I`
   applied to steps 2 and 3 (module `FundamentalConsequencesProof`) returns
   `FundamentalClasses`, `FundamentalInflation`, `FundamentalRestriction`,
   `FundamentalCorestriction` and `FundamentalConjugacy`.
5. **Positive Tate inflation and ordinary inflation.**
   `classFormationInflationLaws p I` applied to step 2 (module
   `ClassFormationInflationLawsProof`).
6. **The witness.** The tuple consists of:
   - arithmetic normalization, `localInvariantFamilyArithmetic hEx p` (module
     `LocalInvariantFamilyArithmeticProof`);
   - steps 1–4;
   - relative corestriction, `invariantRelativeCorestriction p I` from the
     relative-images and restriction parts (module
     `InvariantRelativeCorestrictionProof`);
   - Tate isomorphisms, `classFormationTateIsomorphisms hTate p I` (module
     `ClassFormationTateIsomorphismsProof`), the only place `hTate` is used;
   - the step 5 laws;
   - Tate transfer compatibility, `classFormationTransferLaws p I` (module
     `ClassFormationTransferLawsProof`);
   - absolute corestriction, `invariantAbsoluteCorestriction p I` from the
     absolute-isomorphism and absolute-restriction parts of step 1 (module
     `InvariantAbsoluteCorestrictionProof`).

`hEx` is used only to build the family and its five family laws (steps 1, 2
and the arithmetic normalization). All other conclusions are generic
consequences for any family that satisfies the class-formation axioms.

## Removing the hypotheses

`localAbsoluteCorestrictionCompatibleClassFormation_of_exhaustion` takes only
`hEx`. It applies the conditional assembly to the published Tate theorem
`Langlands.Tate.tateCupIsomorphism` (module
`Langlands.Cohomology.Tate.TateTheoremProof`).

The main theorem `localAbsoluteCorestrictionCompatibleClassFormation` has
exactly the type
`LocalAbsoluteCorestrictionCompatibleClassFormationStatement.{u}`, for an
arbitrary universe `u`, and takes no hypotheses. It applies
`localAbsoluteCorestrictionCompatibleClassFormation_of_exhaustion` to the
published exhaustion theorem `unramifiedH2Exhaustion` (module
`UnramifiedH2Proof`). That theorem proves `UnramifiedH2Exhaustion.{u}`: every
class in the actual absolute `H²` of a `p`-adic field comes by inflation from a
finite unramified Galois extension (Serre, *Local Fields*, XII.1 Theorem 1 and
XII.3 Proposition 3). So the witness is `localInvariantFamily
unramifiedH2Exhaustion p`, and the proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
