# Finite length of actual supercuspidal induction from detection and Jacquet lengths

Author: Worker 4238.

`Langlands.Aubert.General.RationalPointFamily.rationalSupercuspidalInductionFiniteLengthFromInputs`
proves the whole proposition
`RationalSupercuspidalInductionFiniteLengthFromInputsStatement.{u, v}` from
`Langlands.Representation.Aubert.General.RationalSupercuspidalInductionInputsStatement`.
It adds no theorem parameters outside that proposition, and the universes `u`
and `v` stay independent. The statement pair, the target pair
`RationalSupercuspidalInductionFiniteLengthStatement`, the detection pair
`RationalSupportCategoryTargets` and every pair they import are unchanged.

The proposition is an implication. Assume
`RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v}` (`hdet`)
and `RationalAssociatedCuspidalJacquetFiniteLengthStatement.{u, v}` (`hfin`).
The theorem then concludes `RationalSupercuspidalInductionFiniteLengthStatement.{u, v}`.
It proves neither input, so it does not prove the target. What it shows is
that these two inputs are the only representation-theoretic ingredients still
missing.

## Proof

The theorem introduces the target's binders in the order they are stated. As
in the target, it installs `pointTopology` and the finite enumeration
`simpleRelativeRootFintype` of the simple-root labels. Then it takes the
index `I`, an irreducible `σ` on `levi i ν I` with carrier universe `v`, and
inside-Levi cuspidality `hcusp` of `σ`.

1. **Weyl comparisons.** The two inputs also take the point normalizer and
   centralizer comparisons `hN` and `hZ`, but the target does not. The
   published `rationalWeylComparison k G hG T i hi` supplies both for the
   actual maximal split torus.
2. **Carrier lift.** Both inputs live at carrier `max (u + 1) v`. Let
   `σ' = SmoothRep.universeLift.{u + 1} σ`. It is irreducible by
   `SmoothRep.isIrreducible_universeLift_iff`. It is inside-Levi cuspidal by
   `IsCuspidalFor.of_surjective_intertwiner`, applied to the surjective
   intertwiner of the equivalence `SmoothRep.universeLiftEquiv.{u + 1} σ`.
   The Levi's local compactness instance comes from `(hM I).locallyCompactSpace`.
   Let `A` be the actual normalized induction `i_I σ'`, that is,
   `(normalizedInductionFunctor (h I) (hU I)).obj σ'`.
3. **Finite family.** Let `Idx` be the subtype of indices `J` with some
   rational point `n` satisfying `rootAssociation i ν hN hZ I J n`. It is
   finite because the labels are. For `J : Idx`, `F J` is the actual
   normalized Jacquet functor `jacquetFunctor (h J) (hU J)` into smooth
   representations of `levi i ν J`.
4. **Exactness.** Each `F J` maps actual short exact sequences to short exact
   sequences. This is the published `jacquetFunctor_map_isShortExact`, applied
   with the compact-limit property of the radical from the published
   `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
   (using `hStandard`, `hG`, `hi` and `hν`). Its three conclusions are put in
   the order of the published predicate
   `Derivative.Mirabolic.MapsShortExactIntertwiners`. No exactness premise is
   added.
5. **Bounds.** For `J : Idx` with witness `n`, the input `hfin` applied to `I`,
   `J`, `n`, `σ'` and the facts from step 2 says that `F J A` has finite
   length. `Module.length_ne_top_iff` turns this into
   `repLength (F J A) ≠ ⊤`. The bound `bnd J` is the natural-number value
   (`ENat.toNat`) of that length, and `ENat.natCast_toNat` gives
   `repLength (F J A) ≤ bnd J`.
6. **Detection.** The identity point represents the association `I ↦ I`
   (`rootAssociation_one`). So the published
   `isInSupportCategory_cuspidalInduction` places `A` in the actual support
   category `Alg({I})`. Let `D` be an irreducible subquotient of `A`. Then
   `D` is in `Alg({I})` by `IsInSupportCategory.of_isSubquotient`. The input
   `hdet` gives an associated `J` and `n` with `F J D` nontrivial. Its
   Levi-conjugation clause is not used.
7. **Length bound.** The published `Langlands.exactFamilyLengthBound` takes
   the family `F`, the bounds `bnd` and the detection of step 6. It gives an
   actual composition series of `A` with `m` simple factors. By the published
   `repLength_eq_of_hasSimpleFactors`, `repLength A` equals `m`, so it is not
   `⊤`. `Module.length_ne_top_iff` turns this into `A.HasFiniteLength`.
   Finite length of `A` is not assumed.
8. **Descent.** The published `normalizedInduction_universeLift_hasFiniteLength_iff`
   says `i_I σ'` has finite length exactly when `i_I σ` does. This gives the
   target's conclusion at carrier `v`.

## Dependencies

The proof uses these published declarations:

- `rationalWeylComparison`;
- `SmoothRep.universeLift`, `SmoothRep.universeLiftEquiv`,
  `SmoothRep.isIrreducible_universeLift_iff` and
  `normalizedInduction_universeLift_hasFiniteLength_iff`;
- `IsCuspidalFor.of_surjective_intertwiner`;
- `jacquetFunctor_map_isShortExact` and
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`;
- `rootAssociation_one`, `isInSupportCategory_cuspidalInduction` and
  `IsInSupportCategory.of_isSubquotient`;
- `exactFamilyLengthBound` and `repLength_eq_of_hasSimpleFactors`.

The proof uses no geometric lemma, adjunction, Weyl-coset count or
cuspidal-support theorem. These enter only through the two hypotheses. A
proof of `hfin` will need the geometric lemma for the actual standard
families. The detection statement has its own proof task,
`b7887025-20b3-4c11-9fad-0e70bdf59da6`. The final assembly of the target will
apply this theorem to proofs of both inputs.

The `lean_check` diagnostic `b2bdd471-a3f6-4f82-80d4-3ac7dc56f083` reports zero
errors and zero warnings. The only axioms are `propext`, `Classical.choice`
and `Quot.sound`.
