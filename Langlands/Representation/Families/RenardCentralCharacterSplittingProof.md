# Proof of Renard VI.8.5 Lemma: filtrations with distinct central characters split

The theorem `Langlands.Renard.AlgebraicFamily.centralCharacterSplitting` proves
the published statement
[`CentralCharacterSplittingStatement.{uk, uG, uV}`](RenardCentralCharacterSplittingStatement.md)
at three independent universes. It adds no hypothesis. The field `k`, the group
`G`, the central subgroup `Z ≤ Subgroup.center G`, the representation `A` and
the filtration are arbitrary. In particular `A` may be infinite-dimensional,
`k` may be finite, and no single element of `Z` needs to separate the
characters `χ i`. Only the standard axioms `propext`, `Classical.choice` and
`Quot.sound` are used.

## Relation to the source

Renard (VI.8.5, the Lemma inside the proof of the Theorem, printed p. 194 /
PDF p. 200) says the result is clear for the restrictions to `Z(G)`. Since `G`
commutes with `Z(G)`, the action of `G` preserves the decomposition into
distinct characters of `Z(G)`. The Lean proof makes the "clear" step explicit.
It builds, for each index `i`, an operator made from the action of `Z` that
projects onto the `χ i`-eigenvectors. Each such operator commutes with `G`
because `Z` is central, which is the source's second step.

## Notation

Write `V_m = s.subrepresentation m` for the steps of the filtration and
`E_i = {v | ∀ y ∈ Z, ρ y v = χ i y • v}` for the `χ i`-eigenvectors
(`charSubrep A hZ (χ i)`). By the hypothesis, `Z` acts on the graded quotient
`V_{i+1} / V_i` through `χ i`.

## Proof route

1. **Products of central operators.** For a list `L` of pairs `(z, a)` with
   `z ∈ Z` and `a ∈ k`, `factorProduct` is the composite of the operators
   `ρ z - a`. It commutes with every `ρ g` because `Z` is central
   (`commute_factorProduct`). On an eigenvector of a character `ψ` it acts by
   the scalar `factorValue ψ L = ∏ (ψ z - a)`
   (`factorProduct_apply_of_eigen`). More generally, let `W` be a submodule
   stable under `Z`, and suppose `ρ y v - ψ y • v ∈ W` for every `y ∈ Z`. Then
   `factorProduct L v - factorValue ψ L • v ∈ W`
   (`factorProduct_sub_smul_mem`). The proof is by induction on `L`.
2. **Separating points.** If `χ i ≠ χ j`, `separatingPoint (χ i) (χ j)` is
   some `z ∈ Z` with `χ i z ≠ χ j z`. Such a point exists for each pair
   separately; no common point is needed. `factorList χ i` lists the pairs
   `(z_j, χ j z_j)` for `j ≠ i`, with `z_j` separating `χ i` from `χ j`. Then
   `factorValue (χ j) (factorList χ i) = 0` for `j ≠ i`: the factor of index
   `j` vanishes. Also `factorValue (χ i) (factorList χ i) ≠ 0`, since every
   factor `χ i z_j - χ j z_j` is nonzero; this uses injectivity of `χ`.
3. **The projection operators.** `proj A χ i` is `factorProduct` of
   `factorList χ i`, divided by the nonzero scalar
   `factorValue (χ i) (factorList χ i)`. By step 1 it commutes with `G`
   (`proj_apply_rho`). It is the identity on `E_i`
   (`proj_apply_of_mem_self`) and zero on `E_j` for `j ≠ i`
   (`proj_apply_of_mem_ne`). Hence it vanishes on `⨆_{j < i} E_j`
   (`proj_apply_of_mem_iSup_lt`). On `V_{i+1}`, `proj A χ i v - v ∈ V_i`
   (`proj_sub_mem`). This applies step 1 with `W = V_i` and `ψ = χ i`. The
   needed congruence `ρ y v - χ i y • v ∈ V_i` is the published
   `CentralEigenspaceSplitting.sub_smul_mem_of_graded`.
4. **The eigenspaces span.** By induction on `m`,
   `V_m ≤ ⨆_{j < m} E_j` (`le_iSup_charSubrep`). For `v ∈ V_{m+1}`, put
   `i = m` and `u = proj A χ i v`. Then `v - u ∈ V_m` by step 3, which lies in
   `⨆_{j < m} E_j` by induction. Also `u ∈ E_i`: for `y ∈ Z`,
   `ρ y u - χ i y • u` is `proj A χ i` applied to `ρ y v - χ i y • v`. That
   vector lies in `V_m ≤ ⨆_{j < m} E_j`, where `proj A χ i` vanishes. At
   `m = n` this gives `⨆_j E_j = ⊤` (`iSup_charSubrep_eq_top`).
5. **Complementary projections.** By induction over the span `⨆_j E_j = ⊤`
   (`Submodule.iSup_induction`), `proj A χ i v ∈ E_i` for every `v`
   (`proj_mem`), and `∑_i proj A χ i v = v` (`sum_proj`).
6. **Position of `E_i`.** `E_i ≤ V_{i+1}` (`charSubrep_le`). Let `v ∈ E_i`
   lie in `V_{j+1}` with `j ≠ i`. Then `proj A χ j v = 0`, so step 3 gives
   `-v ∈ V_j`, hence `v ∈ V_j`. Descending from `V_n = ⊤` through the indices
   `j = n - 1, …, i + 1` gives `v ∈ V_{i+1}`.
7. **`E_i` is equivalent to the `i`th graded quotient.** `gradedHom` is the
   published graded projection `s.gradedProjection i` restricted to
   `E_i ≤ V_{i+1}`. It is an intertwining map (`Rep.hom_comm_apply`).
   It is bijective (`gradedHom_bijective`):
   - Injective: if `v ∈ E_i` maps to zero, then `v ∈ V_i` (published
     `CentralEigenspaceSplitting.gradedProjection_eq_zero_iff`).
     So `v ∈ ⨆_{j < i} E_j` by step 4, and `v = proj A χ i v = 0` by step 3.
   - Surjective: a class represented by `w ∈ V_{i+1}` is the image of
     `proj A χ i w ∈ E_i`, since `proj A χ i w - w ∈ V_i`.

   Mathlib's `IntertwiningMap.ofBijective` turns it into the equivalence
   `gradedEquiv`.
8. **The bicone.** `splittingBicone` is a bicone in `Rep k G` with vertex `A`.
   - Its projections are `projHom` (`proj A χ i` with codomain `E_i`) followed
     by `gradedHom`.
   - Its inclusions are the inverse of `gradedEquiv` followed by the published
     inclusion `CentralEigenspaceSplitting.subrepInclusion`.

   The identity `ι i ≫ π j = δ_{ij}` follows from step 3 on `E_i`. The total
   identity `∑_j π j ≫ ι j = 𝟙 A` (`splittingBicone_total`) follows from
   `sum_proj`, since each summand is `proj A χ j`.
9. **Conclusion.** Mathlib's `isBilimitOfTotal` makes the bicone a bilimit,
   and in particular a colimit cocone. `IsColimit.coconePointUniqueUpToIso`
   with the chosen colimit gives `A ≅ ∐ fun i => s.gradedRepresentation i`.

## Use of the hypotheses

- `Z ≤ Subgroup.center G` makes `E_i` a subrepresentation. It also makes the
  operators commute with the action of `G`.
- Injectivity of `χ` makes the normalizing scalars nonzero.
- The action of `Z` on the graded quotients enters through
  `sub_smul_mem_of_graded` in step 3.
- That `k` is a field is used to divide by the nonzero scalars `factorValue`.

No finiteness, characteristic, topology or smoothness assumption is used.

## Comparison with published modules

The published `Langlands.CentralCharacterSplitting.splitting_of_distinct_centralCharacters`
needs `Infinite k`, since it separates all characters at once with one linear
combination of central elements. It also takes characters of the full centre.
The present proof separates each pair `χ i ≠ χ j` by its own central element and
multiplies the resulting factors. It therefore works over every field and for
every central subgroup `Z`. Of the published
`CentralEigenspaceSplitting` module it reuses only the filtration helpers
`sub_smul_mem_of_graded`, `gradedProjection_eq_zero_iff`, `mem_bot_iff`,
`mem_top` and `subrepInclusion`. Its single-element hypothesis is not used.

## Helper declarations

All helpers are in the namespace
`Langlands.Renard.AlgebraicFamily.CentralCharacterSplittingProof`:
`factorProduct`, `factorValue`, `factorProduct_cons_apply`,
`factorValue_cons`, `commute_factorProduct`, `factorProduct_sub_smul_mem`,
`factorProduct_apply_of_eigen`, `separatingPoint`, `separatingPoint_spec`,
`charSubrep`, `factorList`, `factorValue_factorList_of_ne`,
`factorValue_factorList_self`, `proj`, `proj_apply_of_mem_ne`,
`proj_apply_of_mem_iSup_lt`, `proj_apply_of_mem_self`, `proj_apply_rho`,
`proj_sub_mem`, `le_iSup_charSubrep`, `iSup_charSubrep_eq_top`, `proj_mem`,
`sum_proj`, `charSubrep_le`, `gradedHom`, `gradedHom_apply`,
`gradedHom_bijective`, `gradedEquiv`, `gradedEquiv_symm_apply_gradedHom`,
`projHom`, `splittingBicone` and `splittingBicone_total`. All of them are
intrinsic to this proof. None is claimed as a statement of the source.

## Environment

Environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. Project imports:
`Langlands.Representation.Families.RenardCentralCharacterSplittingStatement`
and `Langlands.Representation.Filtration.CentralEigenspaceSplitting`. The
statement pair and its imports are unchanged.
