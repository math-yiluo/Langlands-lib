# Maximal split tori of pseudo-parabolic subgroups (conditional reduction)

Module `Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureReduction`.

## Content

This module proves the first two clauses of Conrad–Gabber–Prasad, *Pseudo-reductive
groups* (2nd ed., 2015), Proposition C.2.4, together with the maximality observation just
before it (printed pp. 593–595, PDF pp. 619–621). The proof is conditional on one published
but unproved premise: conjugacy of maximal split tori (CGP Theorem C.2.3), the Library
proposition `SmoothMaximalSplitTorusConjugacyStatement`.

Throughout, `k` is an arbitrary field, `G` is a smooth affine group over `k` whose
underlying space is connected, and `i : P ⟶ G` is a pseudo-parabolic subgroup in the
sense of `IsPseudoParabolicSubgroup`. Also `s : S ⟶ P` is a maximal split torus of `P`
(`IsMaximalSplitTorus s`).

- `IsPseudoParabolicSubgroup.parabolic_comp_innerIso_le_range`: let `χ` be a cocharacter
  of `G` with `P_G(χ) ⊆ P` on every relative test, and let `p` be a rational point of
  `P`. Then the dynamic parabolic of the conjugated cocharacter
  `χ ≫ Int(p ≫ i)` is also contained in `P` on every relative test. No hypotheses on `G`
  are needed.
- `IsPseudoParabolicSubgroup.torusCentralizer_le_range` (conditional on
  `SmoothMaximalSplitTorusConjugacyStatement`): the centralizer of the whole torus,
  `torusCentralizer (s ≫ i)`, is contained in `SubgroupFunctor.range i` on every relative
  test. This is "`Z_G(S) ⊆ P`".
- `IsPseudoParabolicSubgroup.isMaximalSplitTorus_comp` (same premise): `s ≫ i` is a
  maximal split torus of `G`.
- `PseudoParabolicTorusCentralizerContainment`: a proposition bundling both
  conclusions. It quantifies over every universe-`u` field `k`, every smooth connected
  affine `G`, every pseudo-parabolic `i : P ⟶ G` and every maximal split torus
  `s : S ⟶ P`, and asserts `IsMaximalSplitTorus (s ≫ i)` and
  `torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range i`. It uses exactly the quantifiers
  and hypotheses of the first two conjuncts of
  `PseudoParabolicMaximalSplitTorusStructureStatement`. It is the conclusion of the
  reduction below and is not asserted to hold unconditionally.
- `pseudoParabolicTorusCentralizerContainment_of_conjugacy`: the implication
  `SmoothMaximalSplitTorusConjugacyStatement.{u} → PseudoParabolicTorusCentralizerContainment.{u}`.

The third clause of C.2.4, the minimality criterion, is not treated here.

## Proofs

**Conjugated parabolics stay in `P`.** Let `c = p ≫ i` be the image of `p` in `G(k)`, and
let `c_T` be its constant point on a test `T`. Since `c` factors through `i`, `c_T` lies in
`range i` on every test, because `range i` is stable under base change. Suppose `g` is a
`T`-point of `P_G(χ ≫ Int(c))`. Set `x = c_T⁻¹ g c_T`. By `Dynamic.mem_parabolic_conj`,
`x` is a `T`-point of `P_G(χ)`, and therefore of `range i`. Then
`g = c_T x c_T⁻¹` is in `range i` because `range i` is a subgroup.

**`Z_G(S) ⊆ P`.** This follows the last paragraph of the CGP proof of C.2.4 and the remark
after it.

1. By `pseudoParabolicSubgroupStructure`, `P` is smooth, connected and affine.
2. By `IsPseudoParabolicSubgroup.exists_cocharacter_le`, there is a cocharacter `χ` of `G`
   with `P_G(χ) ⊆ P` on every test. Its image lies in `P_G(χ)`
   (`Dynamic.range_le_parabolic`), hence in `range i`.
3. The pseudo-parabolic inclusion is a closed immersion
   (`IsPseudoParabolicSubgroup.isClosedSubgroup`), so `i` represents `range i`. Hence `χ`
   factors as `λ ≫ i` for a cocharacter `λ = hrep.factorHom χ _` of `P`.
4. Apply `exists_innerIso_comp_eq_cocharacter` inside `P`, using C.2.3 for `P`. This gives
   a rational point `p` of `P` and a cocharacter `ξ` of `S` with
   `λ ≫ Int_P(p) = ξ ≫ s`.
5. Naturality of inner automorphisms (`comp_innerIso_hom_comp`) turns this into
   `χ ≫ Int_G(p ≫ i) = ξ ≫ (s ≫ i)` in `G`.
6. The centralizer of the whole torus lies in the dynamic centralizer of each of its
   cocharacters (`torusCentralizer_le_dynamicCentralizer`). That centralizer lies in the
   dynamic parabolic (`Dynamic.centralizer_le_parabolic`). So
   `Z_G(S) ⊆ P_G(ξ ≫ (s ≫ i)) = P_G(χ ≫ Int(p ≫ i))`, which lies in `P` by the previous
   lemma.

**Maximality in `G`.** Apply the published criterion
`IsMaximalSplitTorus.comp_of_torusCentralizer_le_range`: a maximal split torus of a
closed subgroup is maximal split in the ambient group if the subgroup contains the whole
ambient centralizer. Its two inputs are closedness of `i` and the containment just proved.
This is the maximality observation that precedes C.2.4 in CGP. The source argues it with
`S' ⊆ Z_G(S) ⊆ P` for a split torus `S' ⊇ S`, which is the argument inside the published
criterion.

**Bundled statement.** `pseudoParabolicTorusCentralizerContainment_of_conjugacy`
introduces the quantified data and pairs the two results above.

## Provenance

The source is CGP 2015, Appendix C.2. The relevant parts are the paragraph before
Proposition C.2.4, the last paragraph of its proof, and the remark after it, on printed
pp. 593–595. The source's move of a cocharacter into `S` by a `P(k)`-conjugate, using
C.2.3 applied to `P`, is step 4. The source's `P = P_G(λ) R_{u,k}(G)` with `λ ∈ X_*(S)`
is replaced by the weaker containment `P_G(λ) ⊆ P`. That containment is enough for
`Z_G(S) ⊆ P`.

The conjugation lemma and the base-change bookkeeping are internal derivations from
published Library lemmas. Only `SmoothMaximalSplitTorusConjugacyStatement` appears as a
hypothesis. No other theorem-valued premise is used.
