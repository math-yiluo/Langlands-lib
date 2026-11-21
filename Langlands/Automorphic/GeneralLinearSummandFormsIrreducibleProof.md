# Proof of algebraic irreducibility of the forms attached to a cuspidal summand

`Langlands.Automorphic.GroupSchemeFunctions.generalLinearSummandFormsIrreducible` proves the
published proposition `GeneralLinearSummandFormsIrreducibleStatement.{u}` (module
`Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction`), unchanged. For the
positive-central rational quotient of `GL_{r+1}` and a nonzero closed `πc`-invariant subspace `P`
of the full almost-everywhere cuspidal `L²` space `S`, minimal among such subspaces, every
operator realization `W` whose carrier lies in `summandForms F r T i (P.map S.subtype)` is `⊥` or
has exactly that carrier. This is algebraic irreducibility for the actual finite adelic,
standard archimedean compact and enveloping operators.

## Implemented proof

Assume `W ≠ ⊥` and choose a nonzero stable form `f` in `W`.

1. **A jointly admissible smaller realization.** Let `R₀` be the operator realization generated
   by `f` (`generatedFormOperatorRealization`). It lies in `W`
   (`generatedFormOperatorRealization_le_iff`). It is jointly admissible by the published
   `generatedFormAdmissibility_of_harishChandraFiniteness` applied to `harishChandraFiniteness`.
   No irreducibility of `W` or `R₀` is used.
2. **Class maps.** The forms attached to `P` form the operator realization `V =
   summandRealization …`, using the differential stability proof
   `generalLinearSummandFormsEnveloping`. `summandClassMap` sends each form to its class in `P`,
   and composition with the inclusion of `S` gives `jV`. Restricting to `R₀ ≤ W ≤ V` gives `j₀`.
   Both send each vector to its actual form class.
3. **The closure is `P`.** Let `H₀` be the closure of `range j₀` in quotient `L²`. It lies in
   the closed subspace `P.map S.subtype`. By the proved `generalLinearQuotientFormClassClosure`
   it is invariant under the full bounded adelic action, which on `S` is `πc`. Its preimage `P'`
   in `S` is therefore closed, `πc`-invariant and contained in `P`. It is nonzero: the class of
   `f` is nonzero by `generalLinearFormClass_form_eq` and `isGeneralLinearFormClass_zero`. By
   minimality `P' = P`, so every class in `P`, in particular every value of `jV`, lies in `H₀`.
4. **Recovery.** The proved `generalLinearQuotientJointRecovery`, for the jointly admissible
   `R₀` and for `V`, gives `range jV ≤ range j₀`. For an attached form `h`, choose `x ∈ R₀`
   with `j₀ x = jV h`. Uniqueness of the form represented by a class gives equal continuous
   functions, so `x = h` by injectivity of `V.toContinuous`. Hence `h ∈ R₀ ≤ W`, so `W` has the
   whole carrier.

## Library edits

Importing both the Harish-Chandra finiteness chain and the realization/recovery chain exposed a
name clash between automatically named local `AddCommGroup` instances. These were in
`CuspidalFiniteSlice` and in three modules of the finiteness chain. The anonymous local instances
in `FiniteLevelConstantTermRestriction`, `TwoBlockConstantTermActions` and
`CuspidalAdmissible/FixedFamily` now have explicit names. No statement or proof content changed.
All 13 dependents of these modules lie below `HarishChandraFinitenessProof` and were rebuilt.

## Provenance

Getz–Hahn, *An Introduction to Automorphic Representations*, Springer GTM 300 (2024),
Theorem 9.7.3 and its proof, pp. 265–267 (PDF pp. 277–279), especially (9.40). Theorems 6.6.2
and 6.6.4, pp. 170–172 (PDF pp. 184–186), give the admissibility ingredient for automorphic
forms. The book works with `K`-finite vectors of an irreducible summand. This proof uses the
Library's actual operator realizations, the Borel–Jacquet Harish-Chandra finiteness proof for a
cyclic realization, and the derived closure-invariance and recovery lemmas on the original
quotient.
