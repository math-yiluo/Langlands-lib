# Minimal pseudo-parabolics as centralizer times split radical (conditional reduction)

Module `Langlands.GroupScheme.Rational.MinimalPseudoParabolicCentralizerProduct`.

## Content

This module proves the minimality direction ("only if") of the criterion in
Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd ed., 2015), Proposition C.2.4
(printed p.594, PDF p.620). The direction says: if `P` is a minimal pseudo-parabolic
subgroup of `G` and `S` is a maximal split torus of `P`, then `P = Z_G(S) · R_{us,k}(P)`.
The proof is conditional. Its premises are published but unproved Library propositions,
passed as explicit hypotheses:

- `SmoothMaximalSplitTorusConjugacyStatement` (CGP Theorem C.2.3; only the last theorem
  uses it);
- `PseudoParabolicSplitRadicalProductStatement` (CGP Proposition 2.2.4:
  `P_G(χ) R_{u,k}(G) = P_G(χ) R_{us,k}(G)` as fppf-local products);
- `PseudoParabolicSplitRadicalContainmentStatement` (CGP Corollary 2.2.5, containment
  part: in `P = P_G(χ) R_{u,k}(G)`, both `U_G(χ)` and `R_{us,k}(G)` lie in `R_{us,k}(P)`).

It also uses these proved Library theorems directly, not as hypotheses:

- `smoothConnectedNormalFactorFppfProductExistence` (a smooth connected closed subgroup
  and a smooth connected normal closed subgroup have a represented smooth connected
  product; Milne, *Algebraic Groups*, Theorem 5.82 with Lemma 6.41, for smooth connected
  factors);
- `dynamicSmooth` and `DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic`
  (representatives of `P_G(ψ)` are smooth, and connected when `G` is);
- `SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence` (existence of
  `R_{us,k}(G)`).

Throughout, `k` is an arbitrary field, `G` is a smooth affine group over `k` with
connected underlying space, and `i : P ⟶ G` satisfies `IsMinimalPseudoParabolicSubgroup`.
The first three theorems are in the namespace `IsMinimalPseudoParabolicSubgroup`.

- `isFppfProduct_parabolic` (no theorem-valued premise). Let `r : R ⟶ G` be a ground-field
  unipotent radical (`IsUnipotentRadical r`), and let `ψ` be a cocharacter of `G` with
  `P_G(ψ) ⊆ range i` on every relative test. Then `i` represents the fppf-local product
  `P_G(ψ) · R_{u,k}(G)`, i.e. `(Dynamic.parabolic ψ).IsFppfProduct (range r) i`.
- `isFppfProduct_torusCentralizer_of_parabolic_le` (premises: 2.2.4 and 2.2.5). Let `s : S ⟶ P` be a homomorphism from a split torus `S`
  (only `IsSplitTorus S` is assumed, not maximality and not that `s` is a closed
  immersion). Let `ν` be a cocharacter of `S` such that `P_G(ν ≫ s ≫ i) ⊆ range i` on
  every relative test. Let `j : U ⟶ P` be a split ground-field unipotent radical of `P`
  (`IsSplitUnipotentRadical j`). Then
  `SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i)) (range (j ≫ i)) i`.
- `isFppfProduct_torusCentralizer` (all three premises). The same conclusion for every
  maximal split torus `s : S ⟶ P` (`IsMaximalSplitTorus s`) and every split ground-field
  unipotent radical `j` of `P`. This is the "only if" half of the third conjunct of
  `PseudoParabolicMaximalSplitTorusStructureStatement`, with the same quantifiers and
  hypotheses on `k`, `G`, `P`, `i`, `S`, `s`, `U`, `j`.

The module also packages this result as a proposition and a theorem in the namespace
`Langlands.GroupScheme`:

- `PseudoParabolicCentralizerProductOfMinimality : Prop` (a `def`, universe `u`). For every
  field `k : Type u`, every smooth affine `G` over `k` with connected underlying space, every
  `i : P ⟶ G` with `IsPseudoParabolicSubgroup i`, every `s : S ⟶ P` with
  `IsMaximalSplitTorus s`, and every `j : U ⟶ P` with `IsSplitUnipotentRadical j`: if `i` is
  minimal (`IsMinimalPseudoParabolicSubgroup i`), then
  `SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i)) (range (j ≫ i)) i`. The binders
  and hypotheses are those of `PseudoParabolicMaximalSplitTorusStructureStatement`, and the
  conclusion is the forward implication of its third conjunct. It is the counterpart of
  `PseudoParabolicMinimalityOfCentralizerProduct` (the reverse implication) in
  `Rational/PseudoParabolicMinimalityCriterionReduction`. The proposition is the conclusion
  of a conditional theorem. It is not asserted unconditionally.
- `pseudoParabolicCentralizerProductOfMinimality_of_statements`:
  `SmoothMaximalSplitTorusConjugacyStatement.{u} → PseudoParabolicSplitRadicalProductStatement.{u} → PseudoParabolicSplitRadicalContainmentStatement.{u} → PseudoParabolicCentralizerProductOfMinimality.{u}`.
  It introduces the binders and applies `isFppfProduct_torusCentralizer`.

`IsFppfProduct F₁ F₂ i` means: `i` is a closed immersion, and for every relative scheme
`T` (nonaffine and nonreduced tests included) and every `T`-point `x` of `G`, `x` lies in
the image of `i` if and only if there are an fppf cover `W → T` and points `z` of `F₁`
and `u` of `F₂` over `W` with `z · u` equal to the pullback of `x`.

## Proofs

**`isFppfProduct_parabolic`.** The closed subgroup `Dynamic.Affine.parabolicHom ψ`
represents `P_G(ψ)`; its source is smooth (`dynamicSmooth`) and connected
(`DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic`, using that `G` is
connected). The radical `r` is a smooth connected normal closed subgroup by
`IsUnipotentRadical`. So `smoothConnectedNormalFactorFppfProductExistence` gives
`q : Q ⟶ G` representing `P_G(ψ) · R_{u,k}(G)`. By the definition of
`IsPseudoParabolicSubgroup`, `q` is a pseudo-parabolic subgroup. Its image lies in
`range i`: `P_G(ψ) ⊆ range i` by hypothesis, `R_{u,k}(G) ⊆ range i` by
`IsPseudoParabolicSubgroup.radical_le`, and `IsFppfProduct.le_range` combines the two.
Minimality of `i` (`range_eq_of_le`) gives `range q = range i`. So `i` represents the same
fppf-local product as `q`.

**`isFppfProduct_torusCentralizer_of_parabolic_le`.**

1. `IsSplitTorus.exists_compatible_cocharacter` gives a cocharacter `ζ` of `S` such that,
   for `ψ = ζ ≫ s ≫ i`, we have `Z_G(ψ) = Z_G(S)` (the torus centralizer
   `torusCentralizer (s ≫ i)`) and `P_G(ψ) ⊆ P_G(ν ≫ s ≫ i)`. Hence `P_G(ψ) ⊆ range i`.
2. Pick a presentation radical `r` of `G` from `IsPseudoParabolicSubgroup.presentation`.
   The previous theorem gives `P = P_G(ψ) · R_{u,k}(G)`.
3. Choose `n : V ⟶ G` representing `R_{us,k}(G)`
   (`SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence`). Corollary
   2.2.5 applied to `i` gives `U_G(ψ) ⊆ range (j ≫ i)` and `R_{us,k}(G) ⊆ range (j ≫ i)`.
4. `Z_G(S) = Z_G(ψ) ⊆ P_G(ψ) ⊆ range i` (`Dynamic.centralizer_le_parabolic`).
5. Let `x` be a `T`-point in `range i`. By step 2, `x` is fppf-locally in the product
   `P_G(ψ) · R_{u,k}(G)`. Proposition 2.2.4 (applied to `r` and `n`) turns this into
   fppf-local membership in `P_G(ψ) · R_{us,k}(G)`: on an fppf cover `W → T` the
   pullback of `x` is `p · m` with `p` in `P_G(ψ)` and `m` in `R_{us,k}(G)`.
   Let `z = lim_{t→0} ψ(t) p ψ(t)⁻¹` (`Dynamic.limit`). It is a `W`-point of `Z_G(ψ)`
   (`Dynamic.limit_mem_centralizer`), and `p z⁻¹` lies in `U_G(ψ)`
   (`Dynamic.mul_inv_limit_mem_unipotent`). Then
   `u = z⁻¹ (p z⁻¹) z` lies in `U_G(ψ)` (`Dynamic.conj_mem_unipotent`, since `z⁻¹` is in
   `P_G(ψ)`). Write the pullback of `x` as `z · (u · m)`: here `z` is in `Z_G(S)`, and by
   step 3 `u · m` is in `range (j ≫ i)`. The identity `p · m = z · (z⁻¹ (p z⁻¹) z · m)` is
   closed by `group`.
6. Conversely, a point fppf-locally of the form `z · u'` with `z` in `Z_G(S)` and `u'` in
   `range (j ≫ i)` lies in `range i`. Both factors lie in `range i` (step 4 and
   `SubgroupFunctor.range_comp_le`), and `range i` is fppf-local, so membership descends
   from the cover (`FppfLocallyInProduct.mem_range_of_le` in
   `SubgroupFunctor/FppfProductLaws`).

**`isFppfProduct_torusCentralizer`.** This produces the cocharacter `ν` required above.
It repeats steps 2–5 of `IsPseudoParabolicSubgroup.torusCentralizer_le_range` in
`Rational/PseudoParabolicMaximalSplitTorusStructureReduction`:

- `pseudoParabolicSubgroupStructure` makes `P` smooth, connected and affine.
- `IsPseudoParabolicSubgroup.exists_cocharacter_le` gives `χ` with `P_G(χ) ⊆ P`.
- `χ` factors through `i` as a cocharacter of `P`.
- `exists_innerIso_comp_eq_cocharacter` (C.2.3 inside `P`) and `comp_innerIso_hom_comp`
  give a rational point `p` of `P` and a cocharacter `ξ` of `S` with
  `χ ≫ Int(p ≫ i) = ξ ≫ s ≫ i`.

By `IsPseudoParabolicSubgroup.parabolic_comp_innerIso_le_range`,
`P_G(ξ ≫ s ≫ i) ⊆ range i`. The previous theorem then applies, with `ν = ξ` and
`IsSplitTorus S` taken from `IsMaximalSplitTorus s`.

## Provenance

The source is CGP 2015, Proposition C.2.4 and its proof, printed pp.594–595
(PDF pp.620–621). The Lean route differs from the printed proof. The printed proof reduces
to `P/R_{us,k}(P)`. There, by Corollary B.3.5 the radical `R_{u,k}` is `k`-wound, and by
Proposition B.4.4 it is centralized by `S`. Together with Proposition A.2.5 this gives
`P = Z_P(S) R_{us,k}(P)`. Wound groups, B.4.4 and A.2.5 are not in the Library. This module
instead uses the structure of `P` as a dynamic product:

- a cocharacter `ψ` of `S` with `Z_G(ψ) = Z_G(S)` and `P_G(ψ) ⊆ P` (compare the
  pseudo-reductive criterion in the remark after C.2.4, printed p.595, which also
  compares `Z_G(S)` with the centralizer of one cocharacter);
- minimality, which forces `P = P_G(ψ) R_{u,k}(G)`;
- Proposition 2.2.4 (statement printed p.63, proof p.64; PDF pp.89–90), which gives
  `P = P_G(ψ) R_{us,k}(G)`;
- the dynamic decomposition `P_G(ψ) = Z_G(ψ) ⋉ U_G(ψ)` on points;
- the containment `U_G(ψ) R_{us,k}(G) ⊆ R_{us,k}(P)` from the first paragraph of the
  proof of Corollary 2.2.5 (printed pp.64–65, PDF pp.90–91).

This route, and the conditional theorem `isFppfProduct_parabolic`, are internal
derivations from published Library lemmas. Registered source:
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The three propositions listed under Content are the only theorem-valued premises. The
module does not prove them. It does not prove the converse direction of the C.2.4
criterion, and it does not prove the first two clauses of C.2.4.
