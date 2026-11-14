# KP Corollary 11.7.6 from its three inputs

This module reduces Corollary 11.7.6 of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), printed p. 434 (PDF p. 465), to three other published targets. It does not prove Corollary 11.7.6 unconditionally. The source prints the corollary without a proof; it follows at once from Lemma 11.5.2 (printed pp. 430–431), Proposition 11.5.4 (printed p. 431) and the surjectivity in Corollary 11.7.5 (printed p. 434). This module formalizes that deduction. The November 2024 corrections do not change these items.

## The reduction statement

`QuotientReductionStatement` is the proposition

`ZeroKernelStatement → CharacterKernelStatement → (rational surjectivity) → QuotientStatement`,

all at the same universe `u`. Its three premises are:

- `ZeroKernelStatement` (Proposition 11.5.4): for every datum `d : ZeroSubgroupDatum i j`, `d.zeroSubgroup` is the kernel of `reductiveKottwitzRational F G hG`;
- `CharacterKernelStatement` (Lemma 11.5.2): `characterValuationKernel (ValuativeRel.valuation F) G` is the inverse image of `fundamentalInvariantTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG` under that map;
- surjectivity of `reductiveKottwitzRational F G hG` for every nonarchimedean local field `F` and connected reductive `G`. This is written out in the statement. It is exactly the first conjunct of `ChamberStatement` (Corollary 11.7.5), and the statement does not need the chamber clause.

The conclusion is the existing `QuotientStatement`, unchanged. None of the premises is proved here; their proof tasks are Task 6367 (`ZeroKernelStatement`), Task 6366 (`CharacterKernelStatement`) and Task 6368 (`ChamberStatement`).

Provenance: this is derived. It is the obvious implication behind the source's unproved Corollary 11.7.6, written with the Library's existing statements of its three inputs. It makes no new claim from the literature.

## Proof

`quotients_of_surjective_of_ker_of_comap` is the group-theoretic core. Let `κ : Γ →* A` be a surjective homomorphism to a commutative group, `T` a subgroup of `A`, `N = ker κ` and `H = κ⁻¹(T)` (with `H` given any normality instance). The lemma proves:

- `N` is normal, since it is a kernel;
- `N ≤ H`, since `κ(g) = 1` lies in `T`;
- `Γ/N ≃ A`, the first isomorphism theorem for `κ`, sending `[g]` to `κ(g)`;
- `H/(N ∩ H) ≃ T`, the first isomorphism theorem for the restriction `H → T` of `κ`. This restriction is surjective because every `t ∈ T` is `κ(g)` for some `g`, and such a `g` lies in `H`. Its kernel is `N.subgroupOf H`. The class of `x` goes to `κ(x)`;
- `Γ/H ≃ A/T`, the first isomorphism theorem for the composite `Γ → A → A/T`. The composite is surjective, and its kernel is `κ⁻¹(T) = H`. The class of `g` goes to the class of `κ(g)`.

The lemma takes `N` and `H` as variables together with the equations `N = ker κ` and `H = κ⁻¹(T)`, and substitutes them. Each isomorphism is `QuotientGroup.quotientMulEquivOfEq` (changing the denominator along the kernel equation) followed by `QuotientGroup.quotientKerEquivOfSurjective`. So every representative formula holds by `rfl`.

`quotientReduction` proves `QuotientReductionStatement`. For given `F`, `G`, `hG` and datum `d`, it applies the core lemma with `κ = reductiveKottwitzRational F G hG`, `N = d.zeroSubgroup`, `H = characterValuationKernel (ValuativeRel.valuation F) G` (with the Library instance `characterValuationKernel_normal`) and `T = fundamentalInvariantTorsion …`. The three premises supply the surjectivity and the two equations. The lemma's conclusion is then exactly the body of `QuotientStatement`.

`quotientStatement_of_chamberStatement` gives the same conclusion from `ZeroKernelStatement`, `CharacterKernelStatement` and `ChamberStatement`, using only the surjectivity conjunct of the last. Once the three proof tasks are done, it proves the exact target.

All three declarations depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
