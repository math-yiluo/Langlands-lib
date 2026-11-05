# Irreducible tempered representations as subrepresentations of induced discrete series

Author: Worker 6. Module `Langlands.Representation.Exponents.TemperedIrreducibleDiscreteSeriesStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `TemperedIrreducibleDiscreteSeriesStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.6, Theorem, printed p.231 / PDF p.237, with its proof on printed pp.231–232 / PDF pp.237–238. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The first assertion of the theorem says: let `(π, V)` be an irreducible smooth representation of `G`. Then `π` is tempered if and only if there are a standard parabolic subgroup `P = MN` of `G` and an irreducible representation `(σ, E)` of `M` that is square-integrable modulo the center such that `π` is a subrepresentation of `i_P^G(σ, E)`. The second assertion, uniqueness of `(M, σ)` up to conjugation, is the companion statement unit `TemperedIrreducibleDiscreteSeriesUniquenessStatement`.

This is a **derived** formulation. Temperedness is the published derived predicate `IsNormalizedExponentTempered`, and the parabolic ranges over all actual rational parabolics instead of standard ones. See "Faithfulness notes".

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`, as in the published temperedness predicate.

A *Levi datum* below consists of group schemes `P M U` over `Spec k`, an actual rational parabolic `p : P ⟶ G` (`hp : IsParabolicSubgroup p`), a rational Levi `l : M ⟶ P` (`hl : IsRationalLeviSubgroup l`), and a matching geometric unipotent radical `r : U ⟶ P` (`hr`) with `hmul : IsIso (subgroupMultiplication l r)`. For a Levi datum, `rationalPoints M` carries the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl` from the published `ArbitraryParabolicLeviPoints`.

A smooth representation `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` is called *discrete* below when `σ.IsIrreducible` holds and, for every measurable structure on `rationalPoints M ⧸ Subgroup.center (rationalPoints M)` with `[BorelSpace _]` and every Haar measure `haar` on that quotient, `IsSquareIntegrableModCenter σ.representation haar` holds. An *embedding* of `π` into the induction of `σ` is an `f : π.representation.IntertwiningMap ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation` with `Function.Injective f`.

The statement asserts: for every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with `π.IsIrreducible`, `IsNormalizedExponentTempered hG π` holds if and only if there are a Levi datum, a discrete `σ` on its Levi points and an embedding of `π` into the induction of `σ`.

## The objects

- `leviInductionFunctor p l r hp hr hl hmul` is Renard's normalized parabolic induction `i_P^G` on representations of `M(F)` (published, `ArbitraryParabolicLeviPoints`). The induced representation has carrier universe `max u v`. `Representation.IntertwiningMap` allows different carrier universes, so `π` and `σ` both have carrier universe `v`.
- `IsSquareIntegrableModCenter` is the published IV.3.2 predicate: admissibility, a unitary central character, and square-integrable absolute matrix coefficients on the quotient by the abstract center. Square-integrability does not depend on the Haar measure, since Haar measures differ by a positive scalar. The quotient `M(F) ⧸ Z(M(F))` is a locally compact group, so Haar measures exist and the quantification is not vacuous.
- `SmoothRep.IsIrreducible` is simplicity of the lattice of invariant subspaces, including nonzeroness, with no finite-dimensionality.

## Faithfulness notes

- **All parabolics.** The source uses a standard parabolic. The statement allows any actual rational parabolic. The two forms are equivalent: a standard parabolic is a particular actual one, and conversely every parabolic `P` is `G(F)`-conjugate to a standard `P'`, with `i_P^G σ ≃ i_{P'}^G σ^g`.
- **No extra hypotheses.** The only hypothesis on `π` is irreducibility, as in the source. Admissibility of `π` is not assumed. In the forward direction it is part of temperedness. In the converse direction it follows because `π` embeds in `i_P^G σ`, which is admissible when `σ` is.
- **Universes.** The representations `π` and `σ` share the carrier universe `v`. In the source proof `σ` is a quotient of `(r_P^G π)_0`, whose carrier lies in the universe of `π`.

## Remaining obligations

The proof is a separate obligation. The source route uses:

- for sufficiency: Remark 2 of VII.2.1 for `M` (published statement `SquareIntegrableNormalizedTemperedStatement`), the Lemma of VII.2.2 (a separate statement unit, `LeviInductionNormalizedTemperedStatement`), and that subrepresentations of tempered representations are tempered (exactness of the Jacquet functors);
- for necessity: a standard parabolic `P` minimal with `(r_P^G π)_0 ≠ 0`, finite generation of `r_P^G π` for irreducible `π` (VI.1.3), an irreducible quotient of a finitely generated module (A.VI.3), the Lemmas of VII.2.3 and VII.2.4 and minimality to get square-integrability, and Frobenius reciprocity VI.1.1;
- the structural inputs these use for actual reductive groups (presentation existence, standard reduction, Jacquet admissibility, Cartan and Iwahori decompositions, compactness of `G/P`).

## Provenance

This is a derived statement of the first assertion of the Theorem of VII.2.6 for the represented-parabolic interface. Temperedness is the published normalized-exponent predicate, and square-integrability is the published IV.3.2 predicate applied to `M(F)`. Induction is the published `leviInductionFunctor`. Allowing arbitrary instead of standard parabolics is a formalization choice explained above.
