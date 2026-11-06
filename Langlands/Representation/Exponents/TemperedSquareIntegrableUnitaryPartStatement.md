# Square-integrability of tempered representations through unitary Jacquet parts

Author: Worker 6. Module `Langlands.Representation.Exponents.TemperedSquareIntegrableUnitaryPartStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `TemperedSquareIntegrableUnitaryPartStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.4, Lemma, printed p.230 / PDF p.236. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The lemma says: let `(π, V)` be an admissible tempered representation of `G` with a central character. Then `π` is square-integrable modulo the center if and only if `(r_P^G π)_0 = {0}` for every proper standard parabolic subgroup `P = MN`. The proof: "this follows from the definitions, from the fact that the central character is unitary (Remark 1, VII.2.1) and from Casselman's criterion."

This is a **derived** formulation: temperedness is the published derived predicate `IsNormalizedExponentTempered`, and the condition on `(r_P^G π)_0` is imposed for every proper actual parabolic instead of every proper standard one. These choices are explained below.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`. It assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`, a measurable structure `[MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]` with `[BorelSpace …]`, and an arbitrary Haar measure `haar` on that quotient, with `[haar.IsHaarMeasure]`. These are the hypotheses of the published Casselman statement `ArbitraryParabolicCasselmanCriterionStatement`.

For every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` and every `ω : Subgroup.center (rationalPoints G) →* ℂˣ`, it assumes `IsNormalizedExponentTempered hG π` and `π.HasCentralCharacter ω`. It then asserts that `IsSquareIntegrableModCenter π.representation haar` holds if and only if, for every actual rational parabolic `p : P ⟶ G` with `hp`, rational Levi `l : M ⟶ P` with `hl`, matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul`, and split component `a : A.toGrp ⟶ M` with `ha`, if `¬ IsIso p` then `unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥`.

## The objects

- `IsSquareIntegrableModCenter π.representation haar` is the published IV.3.2 predicate. It requires admissibility and a unitary central character, and that every absolute matrix coefficient lies in `L^2` of `haar`.
- `π.HasCentralCharacter ω` is the published predicate that every element `z` of the center of `G(F)` acts by the scalar `ω z`. It is Renard's "admettant un caractère central" (III.1.10, printed p.63 / PDF p.69). No unitarity or open-kernel condition is assumed. For tempered `π ≠ 0`, unitarity of `ω` is Remark 1 of VII.2.1, published in corrected form, with a nonzero hypothesis, as `NormalizedTemperedCentralCharacterStatement`. The open kernel then follows from smoothness. For `π = 0` every `ω` is a central character.
- `unitaryJacquetPart p l r hp hl hr hmul ha π` is Renard's `(r_P^G π)_0` from `ArbitraryParabolicUnitaryJacquetPart`: the supremum of the characteristic spaces of the split component over the exponents with zero real part. `= ⊥` is Renard's `(r_P^G π)_0 = {0}`.
- `¬ IsIso p` says that the closed subgroup `P` is not all of `G`. This is Renard's "propre".

## Faithfulness notes

- **Every proper parabolic.** The source quantifies over proper standard parabolics with respect to a fixed minimal parabolic. The statement quantifies over every actual proper rational parabolic with any rational Levi, matching radical and split component. The two conditions are equivalent because every parabolic is `G(F)`-conjugate to a standard one, and conjugation transports the Jacquet module, its exponents and its unitary part. This equivalence is part of the proof obligation.
- **Why the parabolic must be proper.** For `P = G` the normalized Jacquet module is `π` itself, and under a unitary central character every exponent has zero real part. Then `(r_G^G π)_0 = π`, so the condition would fail for `π ≠ 0`.
- **Central character.** The source's hypothesis is a central character, without unitarity. The statement takes an arbitrary `ω` with `π.HasCentralCharacter ω`. The source's "admissible" is part of the published temperedness predicate.
- **Haar measure.** Square-integrability is tested for an arbitrary Haar measure on `G(F) ⧸ Z(G(F))`. It does not depend on that choice, since Haar measures differ by a positive scalar. The quotient is by the abstract center of `G(F)`, as in the published square-integrability predicate.
- **Degenerate cases.** If `G` has no proper rational parabolic, the right-hand side is vacuous. The statement then says that every tempered `π` with a central character is square-integrable modulo the center. This is correct: `G(F) ⧸ Z(G(F))` is then compact, and matrix coefficients are bounded. For `π = 0` both sides hold.

## Remaining obligations

The proof is a separate obligation. A proof along the source route needs:

- Remark 1 of VII.2.1: the central character of a nonzero tempered representation is unitary (published statement `NormalizedTemperedCentralCharacterStatement`, proof open), so the published Casselman statement applies. The zero representation is treated separately;
- the published Casselman statement `ArbitraryParabolicCasselmanCriterionStatement` and its proof (separate proof task);
- for the forward direction, that `0` is not in `pres.positiveCone` for a proper parabolic. This holds because `Δ(P)` is nonempty and linearly independent. It also needs existence of a compatible presentation for every actual proper parabolic triple;
- for the reverse direction, the following argument. Let `χ` be an exponent for a standard `P` with `ℜ(χ) = Σ_{α ∈ Δ(P)} c_α α`, all `c_α ≥ 0` by temperedness. Suppose some `c_β = 0`. Let `Q = LU ⊇ P` be the standard parabolic whose Levi `L` has simple roots `Δ_0^M ∪ {α : c_α > 0}`. Then `Q` is proper. By transitivity of Jacquet functors (VI.1.4) and Lemma VII.1.1(ii) applied in `L`, the restriction of `χ` to `A_L` is an exponent of `r_Q^G π`. Its real part is the restriction of `ℜ(χ)` to `𝔞_L`, which is `0`. This contradicts `(r_Q^G π)_0 = {0}`. Hence every exponent lies in the strictly positive cone, and Casselman's criterion applies. A Lean proof also needs presentation existence for the standard parabolics and compatibility of presentations under `Q ⊇ P`;
- the reduction from arbitrary to standard parabolics described above.

## Provenance

This is a derived statement of the Lemma of VII.2.4 for the represented-parabolic interface. Temperedness is the published normalized-exponent predicate, square-integrability the published IV.3.2 predicate, and `(r_P^G π)_0` the unitary Jacquet part. The quantification over all proper actual parabolics instead of proper standard ones is a formalization choice, equivalent to the source by conjugation.
