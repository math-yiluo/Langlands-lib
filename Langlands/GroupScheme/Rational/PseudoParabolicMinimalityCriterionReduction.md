# The product criterion implies minimality (conditional reduction)

Module `Langlands.GroupScheme.Rational.PseudoParabolicMinimalityCriterionReduction`.

## Content

This module proves the reverse implication of the minimality criterion in
Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd ed., 2015), Proposition C.2.4
(printed pp. 594–595, PDF pp. 620–621): if `P = Z_G(S) · R_us,k(P)`, then `P` is a minimal
pseudo-parabolic subgroup. The proof is conditional on three published but unproved
premises. They appear only as explicit hypotheses:

- `SmoothMaximalSplitTorusConjugacyStatement`: rational conjugacy of maximal split tori
  (CGP Theorem C.2.3);
- `PseudoParabolicSplitSolvableEnvelopeStatement`: for a pseudo-parabolic `P` with a
  maximal split torus `S` and a split unipotent radical `R_us,k(P)`, there is a split
  solvable closed subgroup `H ⊆ P` that is the fppf-local product
  `S · R_us,k(P)` (the group `H := S ⋉ R_us,k(P)` of the CGP proof of C.2.5);
- `SplitSolvableIntoPseudoParabolicStatement`: a split solvable closed subgroup of `G`
  has a `G(k)`-conjugate inside any given pseudo-parabolic subgroup (CGP Lemma C.2.2).

The module also uses the clauses 1–2 reduction module
`PseudoParabolicMaximalSplitTorusStructureReduction`, which is itself conditional on C.2.3.

Throughout, `k` is a field. In the second part, `G` is a smooth affine group over `k`
whose underlying space is connected.

- `IsClosedSubgroup.range_comp_iso_eq_of_le` (unconditional): let `G` be affine and
  locally of finite type over `k`. Let `i : P ⟶ G` be a closed subgroup and `e : G ≅ G` an
  automorphism of the group. If `range (i ≫ e.hom) ≤ range i` on every relative test,
  then the two ranges are equal. In words, a closed subgroup that contains its image
  under an ambient automorphism equals that image.
- `IsClosedSubgroup.range_comp_iso_eq_of_ge` (unconditional): the same conclusion
  under the reverse hypothesis `range i ≤ range (i ≫ e.hom)`.
- `IsPseudoParabolicSubgroup.isMinimal_of_isFppfProduct` (conditional on the three
  premises): let `i : P ⟶ G` be pseudo-parabolic, `s : S ⟶ P` a maximal split torus of
  `P` and `z : U ⟶ P` a split unipotent radical of `P`
  (`IsSplitUnipotentRadical z`). Suppose `P` is the represented fppf-local product
  `SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i)) (range (z ≫ i)) i`. Then
  `IsMinimalPseudoParabolicSubgroup i`.
- `PseudoParabolicMinimalityOfCentralizerProduct`: a proposition stating this
  implication. It quantifies over every universe-`u` field `k`, every smooth connected
  affine `G`, every pseudo-parabolic `i : P ⟶ G`, every maximal split torus
  `s : S ⟶ P` and every split unipotent radical `j : U ⟶ P`. It asserts that the product
  `IsFppfProduct (torusCentralizer (s ≫ i)) (range (j ≫ i)) i` implies
  `IsMinimalPseudoParabolicSubgroup i`. Its quantifiers and hypotheses are exactly those of
  the reverse direction of the third conjunct of
  `PseudoParabolicMaximalSplitTorusStructureStatement`. It is the conclusion of the
  reduction below and is not asserted to hold unconditionally.
- `pseudoParabolicMinimalityOfCentralizerProduct_of_statements`: the implication from the
  three premises (at universe `u`) to `PseudoParabolicMinimalityOfCentralizerProduct.{u}`.

The forward implication (a minimal `P` is the product) is not treated here.

## Proofs

**A closed subgroup containing its image under an automorphism.** The coordinate ring
`Γ(G, ⊤)` is Noetherian because `G` is affine and locally of finite type over a field.
Let `φ n = e ^ n` in `Aut G`, and let `a n = i ≫ (φ n).hom`, so that
`a (n + 1) = (i ≫ e.hom) ≫ (φ n).hom`. Each `a n` is a closed immersion
(`IsClosedSubgroup.comp_iso`). Applying `SubgroupFunctor.range_comp_mono` to the hypothesis
gives `range (a (n + 1)) ≤ range (a n)` for every `n`.

Take a maximal element, indexed by some `n`, of the set of ideals cut out on the top affine
open by the kernels of the `a m` (`set_has_maximal_iff_noetherian`). The inclusion
`range (a (n + 1)) ≤ range (a n)` gives a factorization `a (n + 1) = f ≫ a n`
(`SubgroupFunctor.factorOfRangeLE`). Hence the kernel ideal sheaf of `a n` is contained in
that of `a (n + 1)` (`Scheme.Hom.le_ker_comp`). By maximality the two ideals are equal, so
the two ideal sheaves on the affine scheme are equal (`IdealSheafData.ext_of_isAffine`).
Then `f` is an isomorphism on the underlying schemes
(`IsClosedImmersion.isIso_of_ker_eq`), and so an isomorphism of group schemes, because
the forgetful functors `Grp → Mon → Over → Scheme` reflect isomorphisms. Factoring
`a n = inv f ≫ a (n + 1)` gives the reverse inclusion, so
`range ((i ≫ e.hom) ≫ (φ n).hom) = range (i ≫ (φ n).hom)`. Cancelling the automorphism
`φ n` (`SubgroupFunctor.range_comp_iso_eq_iff`) yields
`range (i ≫ e.hom) = range i`.

The `_of_ge` version applies the `_of_le` version to `e.symm`. The hypothesis is pushed
through `e.inv` with `range_comp_mono`. The resulting equality is transported back with
`range_comp_iso_eq_iff`.

**The product criterion implies minimality.** Let `j : Q ⟶ G` be a pseudo-parabolic
subgroup with `range j ≤ range i`; we show `range j = range i`.

1. The envelope premise gives a split solvable `h : H ⟶ P` with `H = S · R_us,k(P)`. Its
   composite `h ≫ i` is a closed subgroup of `G`.
2. The C.2.2 premise, applied to `Q` and `h ≫ i`, gives a rational point `g` and a
   factorization `f ≫ j = (h ≫ i) ≫ Int(g)`. Put `j' = j ≫ Int(g)⁻¹`, a pseudo-parabolic
   subgroup by `IsPseudoParabolicSubgroup.comp_iso`. Then `f ≫ j' = h ≫ i`, so
   `range (h ≫ i) ≤ range j'`. Since `H` contains both `S` and `R_us,k(P)`, both
   `range (s ≫ i)` and `range (z ≫ i)` lie in `range j'`.
3. By the clauses 1–2 reduction (`isMaximalSplitTorus_comp`, using C.2.3), `s ≫ i` is a
   maximal split torus of `G`. It lifts through the closed immersion `j'` to a torus
   `s_Q` of `Q` that is maximal split in `Q` (`IsMaximalSplitTorus.exists_lift`), with
   `s_Q ≫ j' = s ≫ i`.
4. The clauses 1–2 reduction for `j'` and `s_Q` (`torusCentralizer_le_range`, using
   C.2.3) gives `Z_G(S) = torusCentralizer (s ≫ i) ≤ range j'`.
5. Since `P` is the fppf-local product of `Z_G(S)` and `R_us,k(P)`, and both factors lie in
   `range j'`, `range i ≤ range j'` (`SubgroupFunctor.IsFppfProduct.range_le`).
6. Conjugating `range j ≤ range i` by `Int(g)⁻¹` gives
   `range j' ≤ range (i ≫ Int(g)⁻¹)`. Together with step 5,
   `range i ≤ range (i ≫ Int(g)⁻¹)`. The Noetherian lemma `range_comp_iso_eq_of_ge` then
   gives `range (i ≫ Int(g)⁻¹) = range i`.
7. Hence `range j' = range (i ≫ Int(g)⁻¹)` by antisymmetry. Cancelling `Int(g)⁻¹`
   (`range_comp_iso_eq_iff`) yields `range j = range i`.

**Bundled statement.** `pseudoParabolicMinimalityOfCentralizerProduct_of_statements`
introduces the quantified data and applies `isMinimal_of_isFppfProduct`.

## Provenance

CGP proves the reverse implication of C.2.4 through the quotient `P/R_u,k(P)`. By Remark
3.5.6, Proposition 3.5.8 and Lemma 2.2.3(1), `P` is minimal if and only if the image of `S`
in `P/R_u,k(P)` is central. By Proposition A.2.5, that is equivalent to
`P = Z_P(S) · R_u,k(P)`. The implemented proof avoids this quotient theory, which the
Library does not yet provide. Instead it mirrors the containment argument of the CGP proof
of Theorem C.2.5 (printed p. 595): the group `H = S ⋉ R_us,k(P)`, Lemma C.2.2 to conjugate
`H` into `Q`, and the maximality observation before C.2.4 (via the clauses 1–2 reduction)
to show that `P` lies in a conjugate of `Q`.

CGP's proof of C.2.5 finishes by the minimality of `Q`. Here the corresponding step is the
Noetherian lemma: a closed subgroup contained in its own conjugate equals it. This lemma
and its proof by an ascending chain of kernel ideals are internal derivations from
Mathlib and published Library lemmas; the same chain argument appears in
`Rational/ParabolicContainsMinimalProof`. C.2.3, Lemma C.2.2 and the envelope
`S ⋉ R_us,k(P)` enter only as the three explicit published premises named above.
