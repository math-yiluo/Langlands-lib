# Assembly of the maximal-cone selection

Author: Worker 23.

This module proves the published proposition
`Langlands.GLMaximalConeJacquetQuotientStatement`
(`Langlands.Representation.Classification.MaximalConeStatement`) from four
published propositions, which are explicit hypotheses of the theorem:

- `hfin : GLDualJacquetFinitenessStatement.{uF, uV}`
  (`Langlands.Representation.Exponents.DualJacquetStatement`); only its first
  clause, finiteness of the set of dual exponents along each block shape, is
  used;
- `hcone : GLBlockConeExistenceStatement`
  (`Langlands.Representation.Classification.ParabolicConeAuxiliaryStatement`),
  existence of a cone coarsening for every real block vector;
- `hfg : Parabolic.OppositeJacquetFiniteGenerationStatement.{uF, uV}`
  (`Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationStatement`);
- `htemp : GLProductLeviDualOppositeTemperedSufficiencyStatement.{uF, uV}`
  (`Langlands.Representation.Classification.ProductLeviTemperedSufficiencyStatement`).

The final proof module applies `glMaximalConeJacquetQuotient_of` to their
published proofs. The argument follows Konno 2003, proof of Theorem 3.5(i)
(pp.396–397), with dominance of positive parts as in the corrected statement.
The quotient is taken of the whole opposite Jacquet module, as the statement
requires, and not as a subrepresentation of an isotypic part as in Konno.

## Declarations

- `MaximalConeAssembly.isCone_of_numerical`: the published numerical cone
  conditions `GLBlockConeNumericalConditions B C r q t` give the structure
  `MaximalConePolygon.IsCone B r C q t`. Their fields are the same six
  conditions.
- `MaximalConeAssembly.precomp q`: precomposition `a ↦ a ∘ q` as a monoid
  homomorphism. It defines the restricted character `χC = χ ∘ precomp q`.
- `PadicField.TopologicalData.exists_irreducible_oppositeJacquet_quotient hfg`:
  the irreducible quotient of the whole opposite Jacquet module (below).
- `PadicField.TopologicalData.prefix_nonpos_of_maximal`: the test condition of
  the tempered sufficiency criterion for the twisted quotient (below).
- `glMaximalConeJacquetQuotient_of hfin hcone hfg htemp`: the target
  proposition.

## Proof of the target

Fix `p`, `F`, `T`, `n > 0` and an irreducible admissible `A`.

1. **Finite family.** For each block shape `B`, let `R B` be the set of real
   parts of the dual exponents of `A` along `B`. It is finite: the exponents form
   a finite set (`hfin`, clause 1), and each has at most one real part
   (`IsRealPartOf.eq`). So `R B` lies in the image of that finite set under a
   chosen real part.
2. **A first cone.** Along the one-block shape `(n)`, the central character is a
   dual exponent (`exists_isDualJacquetExponent_of_length_eq_one`, module
   `MaximalConeExponents`). It has a real part (`exists_isRealPartOf`, module
   `Exponents/RealPartExistence`), and that real part has a cone by `hcone`.
3. **Selection.** `MaximalConePolygon.exists_maximal_cone` (module
   `MaximalConeSelection`) selects `B, r ∈ R B` with a cone `(C, q, t)` that no
   cone of any member of the family strictly dominates. This gives `χ`, `r` and
   all numerical clauses of the target. The final maximality clause is this
   property, restated for exponents and their real parts.
4. **Restriction.** `χC a = χ (a ∘ q)` is a dual exponent along `C`
   (`isDualJacquetExponent_coarsen`). Its real part is `size · t`
   (`isRealPartOf_coarsen` with the cone totals). The containments
   `B.parabolic ≤ C.parabolic` and `B.leviSubgroup ≤ C.leviSubgroup` are the
   published `glBlockCoarseningSubgroups`.
5. **Quotient.** `exists_irreducible_oppositeJacquet_quotient hfg` (below)
   gives an irreducible admissible `S` with scalar character `χC` and a
   surjection from the whole opposite Jacquet module.
6. **Temperedness.** Apply `htemp` to `S' = Rep.of (T.leviRealPowerTwist C (-t) S.ρ)`:
   - `S'` is irreducible (published `isIrreducible_twist_iff`) and admissible
     (published `isAdmissible_twist_iff`, since the real determinant character
     has open kernel).
   - The block scalars act on `S'` by `ω = χC · (c_{-t} ∘ blockScalarLevi)`.
     Its real part is `size · t + size · (-t) = 0`
     (`isRealPartOf_mul_leviRealPowerCharacter`), so `‖ω‖ = 1`.
   - The exponent test is `prefix_nonpos_of_maximal`.

## The opposite Jacquet quotient

`exists_irreducible_oppositeJacquet_quotient hfg hi ha h`, in namespace
`Langlands.PadicField.TopologicalData`. Hypotheses:

- `hfg : Parabolic.OppositeJacquetFiniteGenerationStatement.{uF, uV}`, the
  published finite-generation proposition, assumed here as a hypothesis;
- `A.ρ` is irreducible and, for `T.topology`, admissible;
- `h : T.IsDualJacquetExponent C A χC`.

Conclusion: there is an irreducible admissible `S : Rep.{uV} ℂ (C.Levi F.Carrier)`
with `HasScalarCharacter S.ρ (C.blockScalarLevi F.Carrier) χC` and a surjective
intertwiner from `(CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ` onto
`S.ρ`. These are the corresponding clauses of the target statement.

Proof: apply the generic extraction `MaximalConeQuotient.exists_irreducible_quotient`
(module `MaximalConeQuotient`) with `G = C.Levi F.Carrier` (product topology, a
topological group by `T.leviTopologicalGroup C`) and `z = C.blockScalarLevi F.Carrier`.

- Cofinality of compact open subgroups is the published `T.leviCompactOpenCofinal C`.
- Centrality is the published `blockScalarLevi_mem_center`.
- An irreducible `A` is finitely generated, since a simple module is cyclic. So
  `hfg` gives finite generation of the opposite Jacquet module.
- Its admissibility is the published `Parabolic.standardOppositeJacquetAdmissibility`.
- The definition of `IsDualJacquetExponent` gives a nonzero `φ` in the
  `χC`-eigenspace of the transpose split-centre action on
  `T.splitCentreOppositeJacquet C A`. This module has the same carrier as the
  opposite Jacquet module, with action `oppositeJacquet.ρ ∘ blockScalarLevi`. The
  published `mem_commutativeCharacterSpace_one` turns membership into the
  eigen-equation `φ (ρ (blockScalarLevi a) v) = χC a * φ v`.

The fixed functional `φ` need not descend to `S`. The target statement asks only
for the surjection and the scalar character.

## The exponent test

`prefix_nonpos_of_maximal` takes the following data:

- the maximality property;
- the surjection `f` and the unitary scalar character `ω` of the twist;
- a refinement `D` of `C`, an open-kernel `ψ` with real part `s`, and a nonzero
  eigenfunctional `φ` on the refined opposite Jacquet module of the twist.

It proves `∑_{i' ≤ i} s (j, i') ≤ 0` for every outer block `j` and inner
index `i`.

1. `isDualJacquetExponent_flatten_of_quotient` (module `MaximalConeLifting`)
   gives a dual exponent of `A` along `C.flatten D`. Its real part is
   `r' = s + size · (t ∘ flattenOuter)`.
2. `hcone` gives a cone `(C'', q'', t'')` of `r'`. Maximality says it does not
   strictly dominate `(C, t)`.
3. `sum_fibre_eq_zero_of_unitary` shows that `s` sums to zero over each outer
   block, so the outer block totals of `r'` are `C.size j · t j`
   (`size_eq_sum_flattenOuter`).
4. The polygon comparison `residual_nonpos_of_not_strictlyDominates` (module
   `MaximalConePolygon`), applied to the monotone coarsening `flattenOuter`,
   gives nonpositive partial residuals `∑ (r' k - size_k · t j) ≤ 0` over the
   flattened blocks `k ≤ (j, i)` of the fibre of `j`. On that fibre the residual
   of `r'` is exactly `s`. `sum_filter_flattenOuter_le` rewrites the sum in inner
   coordinates.

## Sources

T. Konno, *A note on the Langlands classification and irreducibility of induced
representations of p-adic groups* (2003), registered as
`konno-2003-langlands-classification`: Lemmas 3.3–3.4 and Theorem 3.5(i),
pp.394–397. The analytic input and finite generation enter through the
published Library propositions named above; admissibility of opposite Jacquet
modules through the published `Parabolic.standardOppositeJacquetAdmissibility`
(Casselman 1995, Theorem 3.3.1).
