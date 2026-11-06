# Henniart's extension argument, conditional on its deep inputs

This module proves the published proposition
`Langlands.Correspondence.FullCharacterizationExtendsStatement.{uF, uP, uA} F`
(Henniart 2002, Corollary 1.6; proof in Section 3.4) **from three explicit
hypotheses**, labelled H1, H2 and H4 (the labels of the extension task, where
H3, H5, H6 and the Langlands-epsilon comparison were inputs since discharged).
It is a conditional reduction, not a proof of the target: the theorem
`fullCharacterizationExtends_of_inputs` takes each of the three inputs as an
argument. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## The bundled inputs (`FullCharacterizationExtendsInputs`)

`FullCharacterizationExtendsInputs.{uF, uP, uA} F : Prop` is the conjunction
`H1 ∧ H2 ∧ H4` of the three hypotheses listed next, with exactly the universe
instantiations used below. It is an internal definition. Henniart's §3.4 proof
(printed p. 598) uses Theorem 1.6(a), Theorem 1.6(b) and Theorem 1.4. Here
Theorem 1.6(a) is the proved input H5 below and Theorem 1.6(b) is H2. The
appeal to Theorem 1.4 is replaced by the local converse theorem (H1), together
with uniqueness of the local-constant system (H4), which identifies the epsilon
factors attached to the two correspondences. The theorem
`FullCharacterizationExtendsInputs.fullCharacterizationExtends` derives the
target from it. Once H1, H2 and H4 are proved, the target follows by applying
this theorem to the triple of the three proofs.

## Inputs

Published Library statements (none of them is proved yet):

- H1 `RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA}`: the
  local converse theorem for supercuspidals, with epsilon tests against
  supercuspidals of ranks `1, …, n - 1` (Henniart 1993).
- H2 `RankinSelberg.SupercuspidalLFactorCharacterizationStatement.{uF, uA, uA}`:
  Henniart 2002, Theorem 1.6(b). An irreducible admissible representation of
  `GL(n + 2)` is supercuspidal iff its Langlands pair L-polynomial against every
  irreducible supercuspidal representation of rank `r + 1 ≤ n + 1` is `1`.
- H4 `∀ eC : ReciprocityFamily F, NonabelianSystem.Unique.{uF, uP} F eC`:
  uniqueness of local-constant systems for one reciprocity family. This is the
  `F`-instance of the all-field `LocalFactor.NonabelianSystemUniquenessStatement`
  (published in `Langlands/LocalFactor/NonabelianUniquenessStatement.lean`,
  which reduces it to the unproved degree-zero generation statement
  `CommonClosureDegreeZeroGenerationStatement`). Its proof is the subject of
  task `3c5513a4-268f-4bf2-9d47-354e4e4e41ec`.

Proved inputs (imported):

- H3, uniqueness of the normalized common-closure reciprocity family:
  `LocalClassField.commonClosureReciprocityUniqueness` in
  `Langlands/ClassFieldTheory/Local/ReciprocitySystemUniquenessProof.lean`
  (proof candidate `55840d2a-451c-4014-92d1-d49b6fe2b172` of task
  `0fbeee3f-f26c-48f6-adbe-8a6fc8c84c5f`, published at Library commit `8fb2236b`). It proves
  `LocalClassField.CommonClosureReciprocityUniqueness`, which earlier draft
  revisions took as a hypothesis.
- H5, the lower-rank parameter criterion `L = 1`:
  `arithmeticPairLFactor_weilPairClass_eq_one` in
  `Langlands/Correspondence/LowerRankWeilFactor.lean` (Worker 1684's candidate
  `4e4fbf12-71c6-4d28-8367-1fd3b5c23337`, published at Library commit
  `86cf8f89`). For continuous irreducible Weil classes `σ` of rank `r + 1` and
  `σ'` of smaller rank `t + 1`, the arithmetic pair L-factor of their
  zero-monodromy pair classes is `1` (Henniart 2002, Section 3.1). Earlier
  draft revisions took it as the hypothesis `LowerRankWeilPairLFactorTrivial`.
- `RankinSelberg.IsLanglandsPairEpsilonFactor.isPadicSymmetricEpsilonFactor_of_isSupercuspidal`
  in `Langlands/Representation/RankinSelberg/SupercuspidalLanglandsEpsilon.lean`
  (Worker 1699's candidate `e28e8836-93e1-43df-995c-1eb8dc060917`, published
  at Library commit `86cf8f89`). On a pair of supercuspidal representations, an epsilon factor
  defined through square-integrable Langlands data is the symmetric JPSS
  epsilon factor (`IsPadicSymmetricEpsilonFactor`) of the pair. Earlier draft
  revisions assumed this as a seventh hypothesis.
- H6, existence of zero-monodromy classes: `exists_zeroMonodromyParameter` in
  `Langlands/Correspondence/IrreducibleZeroMonodromy.lean` (Worker 1684's
  candidate `de171588-6cff-40dc-9d60-974faca4cc21`, published at Library commit
  `8b3ba080`). Every continuous irreducible Weil class `σ` of rank `n` has a
  zero-monodromy parameter class `D` (`IsZeroMonodromyOf F σ D`); this is the
  classical fact that an irreducible Weil representation is
  Frobenius-semisimple. Earlier draft revisions took it as the hypothesis
  `ZeroMonodromyExistence`.

## Helper lemmas

- `parameterForget_injective` and `IsZeroMonodromyOf.unique` are imported from
  Worker 422's published module `Langlands.Correspondence.ZeroMonodromyExtension`
  (Library commit `8fb2236b`): a Weil class has at most one zero-monodromy
  parameter class. Earlier draft revisions carried local copies of them.
- `IsZeroMonodromyOf.parameterForget_eq`: the pair class underlying a
  zero-monodromy parameter class of `σ` is `weilPairClass F σ`.
- `isZeroMonodromyOf_of_rankOne`: in rank one, a Weil class and a parameter
  class given by the same scalar character are related by zero monodromy.
- The rank-one existence and class-uniqueness lemmas are reused directly
  from `Langlands.Correspondence.RankOneComparison`. Its explicitly named
  topology instance permits the combined import with `ArithmeticFactors`.
- `reciprocityHom_eq_of_isBaseReciprocity`: two candidates that are base
  components of one reciprocity family have the same reciprocity homomorphism.
  The base Weil subgroup is the fixing subgroup of `⊥`, which is `⊤`.
- `rankOne_eq_of_weilCharacter_eq`: if two candidates have the same Weil
  characters, `c0` is rank-one compatible for one of them and `τ` for the
  other, then `τ 1 D = c0 1 σ` whenever `D` is the zero-monodromy class of `σ`.

## The implemented proof (`extendsSupercuspidal_of_inputs`)

Unpack `IsSupercuspidalCorrespondence F c0` into rankwise bijectivity of `c0`,
a candidate `e0` with rank-one compatibility, a reciprocity family `eC0` and a
system `ε0` with base `e0`, and the supercuspidal pair-factor compatibility.
Unpack `FullFactorCompatibilityAt F e ψ τ` into L compatibility and a family
`eC`, system `ε` with base `e`, and epsilon compatibility.

1. **Same family, system and characters.** `commonClosureReciprocityUniqueness`
   (H3) applied to the two normalized families gives `eC = eC0`; H4 then gives `ε = ε0`. Both `e` and `e0` are base
   components of the same family, so they have equal reciprocity homomorphisms
   and equal Weil characters. A self-dual measure `ν` for `ψ` comes from the
   supercuspidal compatibility (`exists_selfDualMeasure`).
2. **Induction.** By strong induction on `m`, prove for rank `m + 1`: if
   `IsZeroMonodromyOf F σ D`, then `τ D = c0 σ` (as automorphic classes).
3. **Rank one** is `rankOne_eq_of_weilCharacter_eq`.
4. **Lower-rank tests.** For `r < m` and any supercuspidal `B` of rank `r + 1`,
   surjectivity of `c0` gives `σ'` with `c0 σ' = [B]`, H6
   (`exists_zeroMonodromyParameter`) gives its
   zero-monodromy class `D'`, and the induction hypothesis gives `τ D' = [B]`.
5. **Supercuspidality (Step A).** Choose a representative `A` of `τ D` and lift
   it to `J` with carrier in `max uF uA` (`SmoothRep.universeLift`). Apply H2
   to `J`. A test supercuspidal `ρ` of rank `r + 1` with carrier in
   `max uF uA` has a small realization `S` with carrier in `uA`
   (`padicIrreducibleSmoothSmallRealization`). Step 4 for `S` gives `D'`. L
   compatibility of `τ` gives a polynomial `P` with arithmetic factor `P⁻¹`.
   By `parameterForget_eq` and H5 (`arithmeticPairLFactor_weilPairClass_eq_one`,
   applied with `r + 1 < k + 2`) that factor is `1`, so `P = 1`. Transport
   the L-polynomial relation from the automorphic classes to `J` and `ρ`
   (`isAutomorphicPairLPolynomial_iff`, `IsLanglandsPairLPolynomial.congr_equiv`).
   Hence `J`, and so `A`, is supercuspidal.
6. **Equality (Step B).** Apply H1 to the supercuspidal `A` and `c0 σ`. For a
   test class `[B]` of rank `r + 1 ≤ m`, Step 4 gives `σ'` and `D'`. The
   supercuspidal compatibility gives an epsilon factor `e1` of
   `(c0 σ, [B])` matching the arithmetic epsilon factor of the system `ε0` on
   `(σ, σ')`. The epsilon compatibility of `τ` gives `e2` for `(τ D, τ D')`
   matching the arithmetic factor of the same system on the same pair classes
   (by `parameterForget_eq`). Uniqueness of arithmetic epsilon factors gives
   `e1 = e2`. On the `τ` side, `isAutomorphicPairEpsilonFactor_iff`
   transports `e2` to a Langlands-datum epsilon factor of the lifted pair.
   `isPadicSymmetricEpsilonFactor_of_isSupercuspidal`, applied to the
   supercuspidal lifts, turns it into a symmetric JPSS factor, which is transported back to
   `(A, B)` and restricted to the one-sided relation
   (`isPadicSymmetricEpsilonFactor_of_le`). On the `c0` side,
   `isSupercuspidalPairEpsilonFactor_iff_class` gives the same relation. H1
   concludes that the two supercuspidal classes are equal.
7. **Conclusion.** For every rank `n = m + 1` and Weil class `σ`, H6
   (`exists_zeroMonodromyParameter`) supplies
   `D`, and step 2 gives `τ D = c0 σ`. This is `ExtendsSupercuspidal F c0 τ`.

`fullCharacterizationExtends_of_inputs` discards the unused hypothesis
`IsGeometricReciprocity F e` and applies `extendsSupercuspidal_of_inputs`.
`FullCharacterizationExtendsInputs.fullCharacterizationExtends` splits the
bundled conjunction and applies `fullCharacterizationExtends_of_inputs`.

## Status

This module proves only the conditional theorems above, not the target
statement itself. An unconditional proof of the target still needs proofs of
H1 (task `76ef879c-d009-4d6a-8ead-0667c5bab317`), H2 (task
`99282d49-8140-483c-8dfc-8411be315345`) and H4 (task
`3c5513a4-268f-4bf2-9d47-354e4e4e41ec`). Worker 422's zero-monodromy helper
lemmas were used in earlier revisions of this module and are now imported.
