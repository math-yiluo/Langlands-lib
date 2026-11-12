# Irreducible induced twists from exclusion and persistence

Author: Worker 5120.

This module proves one theorem,
`Langlands.Renard.AlgebraicFamily.irreducibleInducedTwistExistence_of_quotientExponentStatements`.
It takes `InducedTwistQuotientExponentStatements.{u,v}` (exclusion and persistence of
the inducing exponent, from `InducedTwistQuotientExponentStatements`) as hypothesis and
concludes the published `IrreducibleInducedTwistExistenceStatement.{u,v}` at the same
universes. The hypothesis is a proof target, not a theorem. This module does not prove the
existence statement unconditionally.

## Proof

Fix the data of the existence statement and an irreducible admissible `ρ` of `M(k)`.

1. `splitComponentStatement` (Renard V.2.1, proved in
   `Langlands.GroupScheme.Rational.SplitComponentProof`) applied to the connected reductive
   group `M` supplies a split component `a : A_M ⟶ M`.
2. Exclusion and persistence for `a` and `ρ` give nonzero polynomials `f_C` and `f_B`.
   The product `f_C f_B` is nonzero. By `Plancherel.dense_rationalUnramifiedPrincipalOpen`,
   its principal open locus is dense, so it contains a character `ψ`. The unramified
   characters form a subgroup, so the space is nonempty. By
   `mem_rationalUnramifiedPrincipalOpen` and `MvPolynomial.eval_mul`, both `f_C` and
   `f_B` are nonzero at `ψ`. So `ψ` lies in both principal open loci.
3. Write `I = i_P^G(ρψ)`. The twist `ρψ` is irreducible (`SmoothRep.isIrreducible_twist_iff`),
   so its carrier is nontrivial
   (`CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible`). Then
   `nontrivial_leviInduction` shows that `I` is nontrivial. A nonzero vector of `I` lies in `⊤`
   but not in `⊥`, so `⊥ ≠ ⊤` in the lattice of subrepresentations.
4. Irreducibility is `IsSimpleOrder` of that lattice. Suppose an invariant subspace `S`
   is neither `⊥` nor `⊤`. Persistence at `S ≠ ⊤` gives an exponent `χ` of `ρψ` that is
   also an exponent of `r_P(I / S)`. Exclusion at `S ≠ ⊥` says that `χ` is not an exponent
   of `r_P(I / S)`. This is a contradiction, so `ψ` witnesses the existence statement.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Dependency boundary

The project imports are `InducedTwistQuotientExponentStatements`,
`Langlands.GroupScheme.Rational.SplitComponentProof`,
`Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity`,
`Langlands.Representation.LanglandsClassification.LeviInductionQuotient`
(`nontrivial_leviInduction`), and
`Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`. All the results used
are proved in the Library. No representation-theoretic assertion other than the stated
hypothesis is assumed. The target statement's Lean/Markdown pair is unchanged.
