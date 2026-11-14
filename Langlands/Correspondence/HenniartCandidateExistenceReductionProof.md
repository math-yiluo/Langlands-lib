# Proof of Henniart's candidate existence from its open global inputs

This module proves the published statement
`Langlands.Henniart.CandidateExistenceReductionStatement` (module
`Langlands.Correspondence.HenniartCandidateExistenceReductionStatement`) as the theorem

```lean
theorem Langlands.Henniart.candidateExistenceReduction :
    CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}
```

with all five universe parameters free. The statement and its source correspondence are
explained in its own Markdown. In short: from Harris (1998) Proposition 4.8, Henniart's
Théorème 2.4, local relative class formation, the certified pole comparisons of Henniart's
Lemme 2.8 and the composite-map transport of his 3.8, every finite Galois quotient `q` of a
p-adic field `K` has a candidate (`CandidateExistenceStatement.{uK, uW, 0, uE, uQ}`). The
five inputs remain hypotheses; the proof uses no other unproved Library statement.

## The implemented proof

Write `hHarris`, `hasi`, `hlcf`, `hpole`, `hcomp` for the five hypotheses, in the order of
the statement. Fix a prime `p`, a p-adic field `K` and `q : Gal(K̄/K) → Q` with `Q` finite.

1. **An arithmetic fundamental class family.** `hlcf` gives, for every prime, an invariant
   family satisfying relative class formation and the arithmetic normalization (`choose`).
   The proved `globalFundamentalClassStatement.{0}`
   (`Langlands/ClassField/Global/FundamentalClassProof.lean`) turns this family into a
   fundamental class family `c`, and the triple is the witness of
   `RelativeWeilGroup.IsArithmeticClassFamily c`.
2. **Globalization.** The proved `henniartGlobalization_of_inputs`
   (`Langlands/Global/Arithmetic/HenniartGlobalizationReduction.lean`) is applied with the
   proved inputs `LocalClassField.commonClosureReciprocityExistence`,
   `RelativeWeilGroup.localInducedRestriction`,
   `RelativeWeilGroup.associatedCentralCharacter` and
   `RelativeWeilGroup.localTransferReciprocity`, together with `hasi` and `hHarris`, at
   `c`, `p`, `K` and `q`. It returns number fields `F`, `E : Type` with `E/F` Galois, a
   finite place `v` of `F` with residue characteristic `p` (proof `h`), an isomorphism
   `f : K ≃ F_v` over `ℚ_p`, and the covering property `hcov`: for every unitary Weil
   class `x` of `K` that factors through `q` there is `y` in the relative Weil image
   `weilImage F E c v` whose restriction along the induced map of Weil groups equals `x`
   in the exact Grothendieck group of `W_K`. This is Henniart 2000, §2.7 step 1 and
   Théorème 3.1.
3. **The pole pairing.** `F` has compact adele quotient (`compactSpace_adeleQuotient`,
   `Langlands/Global/AdeleQuotientCompactProof.lean`). Take for `ψ` the standard finite
   additive component of `F` at `v`
   (`HeckeFunctionalEquation.standardFiniteAdditiveComponent`,
   `Langlands/Automorphic/AssociatedAdditiveInputs.lean`). `hpole F E c _ v ψ` gives the
   certified pole comparisons, and the proved `relativePolePairing`
   (`Langlands/Global/Factors/RelativePolePairingProof.lean`) gives an isometry `T` with
   `RelativeGeneratedPositiveIsometry` (Henniart's Théorème 2.5 through Lemme 2.8).
4. **The candidate.** The candidate is `henniartCompositeMap F E c v h K f T`. Its 3.8
   properties are `hcomp F E c _ v ψ _ T hT p h K f` (Henniart's §§3.7–3.8). Its domain
   contains every class factoring through `q`: given such a class `x`, `hcov` gives `y` in
   the relative image whose transport is `x`, and
   `continuousRestrict_completionWeilTransport_eq_iff`
   (`Langlands/Global/Factors/HenniartCompositeMapStatement.lean`) converts this equation
   into `completionWeilLatticeEquiv v h K f y = x`, which is the membership of `x` in the
   domain of the composite map required by `CandidateExistenceStatement`.

## Repair of a duplicate Library declaration

Before this candidate, the name
`Langlands.Automorphic.OperatorRealization.evaluate_toContinuous_smul` was declared, with
the same statement, in both `Langlands/Automorphic/CuspidalAdmissible/Reproduction.lean`
and `Langlands/Automorphic/OperatorScalarCentralCharacter.lean`. Step 2 imports the first
(through `HenniartGlobalizationReduction`) and uses `associatedCentralCharacter`, whose
module imports the second, so the proof module could not be built.

The candidate moves the lemma into the new module
`Langlands/Automorphic/OperatorRealizationEvaluation.lean`, which imports only
`Langlands.Automorphic.OperatorRealization`. Both old copies are deleted, and both modules
import the new one. The name, namespace and statement are unchanged, so every consumer
still compiles: `Reproduction.lean` (in a `simp only`), `OperatorScalarCentralCharacter.lean`
and `IrreducibleCentralCharacterProof.lean`. None of the edited files is imported by the
target statement module. The Markdown of the two edited modules now points to the new
module.

## Provenance

The route follows Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
un corps p-adique*, Invent. Math. 139 (2000), registered as `henniart-2000-simple-proof`
(PDF page = printed page − 438): §2.7 step 1, p.447 (PDF 9); Théorème 2.5 and Lemme 2.8,
pp.446–448 (PDF 8–10); Théorème 3.1, p.448 (PDF 10); §§3.7–3.8, p.451 (PDF 13). The choice
of `ψ` and of the arithmetic class family are Library-specific: the Library's relative Weil
groups need a fundamental class family, and its pole comparisons are stated for every
nontrivial `ψ`, so one convenient global choice suffices.
