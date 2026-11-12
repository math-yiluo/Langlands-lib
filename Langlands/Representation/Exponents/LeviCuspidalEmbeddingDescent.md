# Descent step of Renard VI.2.1 for actual represented parabolics

Module `Langlands.Representation.Exponents.LeviCuspidalEmbeddingDescent`.

## Purpose and scope

Renard, *Représentations des groupes réductifs p-adiques* (2026 version), VI.2.1,
Corollary and proof (printed p. 139 / PDF p. 145). Let `π` be an irreducible smooth
representation of `G`, and let `P = MN` be minimal among the parabolics with
`r_P^G(π) ≠ 0`. The proof's second step says that `r_P^G(π)` is supercuspidal. Suppose
a proper parabolic `P'` of `M` had `r_{P'}^M(r_P^G(π)) ≠ 0`. Transitivity of Jacquet
functors would then give a parabolic of `G`, strictly contained in `P`, with nonzero
Jacquet module, contradicting minimality.

This module proves that step for arbitrary actual rational parabolics of the group
scheme `G`. It is conditional: it takes two published propositions as hypotheses and
proves neither of them.

- `LeviParabolicExtensionStatement` (module
  `Langlands.Representation.Exponents.LeviParabolicExtensionStatement`): a parabolic
  `P'` of the Levi `M` of `P` extends to a parabolic `R` of `G` with Levi `M'`, with
  `R ⊆ P` and `R ∩ M = P'`.
- `LeviParabolicTransitivityStatement` (module
  `Langlands.Representation.Exponents.LeviParabolicTransitivityStatement`): represented
  transitivity of induction and Jacquet restriction. Only the Jacquet half is used.

The module proves no form of the target `LeviCuspidalEmbeddingStatement`. The assembly
`Langlands.Representation.Exponents.LeviCuspidalEmbeddingProof` applies the theorem to
the published proofs `leviParabolicExtension` and `leviParabolicTransitivity`. It combines
the result with the unconditional steps in
`Langlands.Representation.Exponents.LeviCuspidalEmbeddingSteps`.

## Declaration

`leviJacquet_supercuspidal_of_minimal (hExt : LeviParabolicExtensionStatement.{u})
(hTrans : LeviParabolicTransitivityStatement.{u, v})`, in namespace
`Langlands.Aubert.General.RepresentedParabolic`. Its conclusion is the following
universally quantified statement.

- The hypotheses on `k`, `G` and `G(k)` are those of the target statement. `k` is a
  nonarchimedean local field (`Field`, `ValuativeRel`, `TopologicalSpace`,
  `IsNonarchimedeanLocalField`, `T2Space`). `G` is a connected reductive group scheme over
  `Spec k`. `G(k)` carries the canonical point topology
  `RationalPointFamily.pointTopology` and is locally compact and a nonarchimedean group.
- `π : SmoothRep.{0, u, v} ℂ G(k)` is any smooth representation. No irreducibility or
  nontriviality is assumed.
- `P, M, U, p, l, r, hp, hl, hr, hmul` is an actual parabolic datum:
  - `p : P ⟶ G` is a parabolic subgroup (`IsParabolicSubgroup p`);
  - `l : M ⟶ P` is a rational Levi subgroup (`IsRationalLeviSubgroup l`);
  - `r : U ⟶ P` is a geometric unipotent radical
    (`LeviSubgroup.IsGeometricUnipotentRadical r`);
  - the multiplication `subgroupMultiplication l r` is an isomorphism.
- **Minimality hypothesis.** Let `P₁, M₁, U₁, p₁, l₁, r₁, hp₁, hl₁, hr₁, hmul₁` be any
  actual parabolic datum with `SubgroupFunctor.range p₁ < SubgroupFunctor.range p`. Then
  `(leviJacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj π` is a subsingleton.
- The Levi points `M(k)` carry the Levi point topology `leviPointTopology l hl` and the
  instances `leviPoints_locallyCompactSpace p l hp hl` and
  `leviPoints_nonarchimedeanGroup p l hp hl`, as in the target statement.
- **Conclusion.** Write `J` for `(leviJacquetFunctor p l r hp hr hl hmul).obj π`. Let
  `P', M', U', p', l', r', hp', hl', hr', hmul'` be an actual parabolic datum of `M`, with
  `p' : P' ⟶ M`, and assume `¬ IsIso p'`. Then
  `(jacquetFunctor p' l' r' hp' hr' hl' hmul').obj J` is a subsingleton.

This conclusion is the written-out supercuspidality of `J` used in the target statement
and in the hypothesis of `cuspidalEmbedding_of_finite_supercuspidal`.

## Proof

The proof is by contradiction. Assume that the Jacquet module of `J` at `P'` is
nontrivial.

1. **Extension.** Apply `hExt` to `G`, the datum `(P, M, U)` and the datum
   `(P', M', U')` of `M`. It gives a parabolic `pR : R ⟶ G` with Levi `nR : M' ⟶ R`,
   radical `rR : W ⟶ R` and multiplication isomorphism. It also gives three facts:
   - `nR ≫ pR = l' ≫ p' ≫ l ≫ p`;
   - `range pR ≤ range p`;
   - `range (p' ≫ l ≫ p) = range (l ≫ p) ⊓ range pR`.
2. **Transitivity conditions.** `hTrans` needs three conditions. It is applied with its
   parabolic `P := R` (Levi `nR`, radical `rR`), its `Q := P` (Levi `l`, radical `r`) and
   its `PL := P'` (Levi `l'`, radical `r'`).
   - `pointImage pR ≤ pointImage p` and the intersection condition on point images
     follow from the corresponding all-test range facts, evaluated at the identity test
     object `Over.mk (𝟙 _)`. The rewriting uses
     `pointImage_eq_range_carrier : pointImage j = (range j).carrier (Over.mk (𝟙 _))`
     and the pointwise infimum of subgroup functors.
   - The composite condition `l' ≫ p' ≫ l ≫ p = nR ≫ pR` is the extension's equation,
     reversed.

   The Jacquet half of the conclusion is a natural isomorphism
   `e : leviJacquetFunctor pR nR rR ≅ leviJacquetFunctor p l r ⋙ leviJacquetFunctor p' l' r'`.
3. **Nontriviality at `R`.** `leviJacquetFunctor` is `jacquetFunctor` followed by a
   pullback, which keeps the carrier. So `SmoothRep.equivOfIso (e.app π)` gives a
   linear equivalence between the Jacquet module of `π` at `R` and the Jacquet module of
   `J` at `P'`. The latter is nontrivial, so the former is nontrivial.
4. **Equal ranges.** By the minimality hypothesis, `range pR < range p` is impossible.
   Together with `range pR ≤ range p`, this gives `range pR = range p`.
5. **`P'` is not proper.** `range (l ≫ p) ≤ range p`, because `l ≫ p` factors through
   `p` (`SubgroupFunctor.range_le_of_factor`). With step 4, the extension's
   intersection formula becomes
   `range (p' ≫ l ≫ p) = range (l ≫ p) ⊓ range p ≥ range (l ≫ p)`.
   `p'` and `l ≫ p` are closed subgroups: parabolics are closed, and so is a Levi
   followed by a parabolic. The published
   `IsClosedSubgroup.isIso_of_range_le_range_comp` (from `LeviCuspidalEmbeddingSteps`),
   with `q := p'` and `j := l ≫ p`, gives `IsIso p'`. This contradicts `¬ IsIso p'`.

## Provenance

The argument is the second step of the proof of the Corollary in Renard VI.2.1 (printed
p. 139 / PDF p. 145): minimality of `P` plus transitivity of Jacquet functors makes
`r_P^G(π)` supercuspidal. The Lean route differs from the source in the following ways,
all internal derivations.

- **Minimality.** The source works with standard parabolics, minimal for inclusion. Here
  the parabolics are arbitrary actual parabolics, and minimality is stated with the
  all-test range `SubgroupFunctor.range`. The theorem takes minimality as a hypothesis.
  `exists_minimal_nontrivial_leviJacquet` in `LeviCuspidalEmbeddingSteps` produces a
  datum satisfying it.
- **The smaller parabolic.** The source recalls (V.3.11) that the standard parabolics of
  `M` are the traces `M ∩ P'` of the standard parabolics `P' ⊂ P` of `G`. For actual
  parabolics, the parabolic `R` of `G` with `R ⊆ P` and trace `P'` on `M` is supplied
  by the hypothesis `LeviParabolicExtensionStatement`.
- **Transitivity.** The source cites Lemma VI.1.4,
  `r_{M∩P'}^M ∘ r_P^G = r_{P'}^G`. Here it is the Jacquet half of the hypothesis
  `LeviParabolicTransitivityStatement`.
- **Properness.** The source's "strictly smaller" becomes the statement that equal ranges
  force `p'` to be an isomorphism. That uses the closed-subgroup lemma above.
