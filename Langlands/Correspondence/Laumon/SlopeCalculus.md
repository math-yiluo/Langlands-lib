# Slope calculus: irreducible modules, twists, transport and Swan-one lines

Laumon (1987), (2.1.2.4)–(2.1.2.7), pp. 152–154; Katz 1983, pp. 211–215; Serre, *Local Fields*,
IV §3 and VI §2. Notation is that of `Langlands.Correspondence.Laumon.Slopes`: a representation
is `A : FiniteRepresentation E H` with `f : H →* (Ω ≃ₐ[K] Ω)`, `E = PadicAlgCl ℓ`, `G^u` are the
Library's absolute upper ramification groups, `V_μ = slopeSummand f A μ` and
`s(V) = ladicSwan f A`.

This module carries out the row `SlopeCalculus` of §4.1 of the [design note for Laumon's local Fourier bijection](../../../notes/henniart/laumon-local-fourier-weil-conjectures-design.md), with its three
statements under the names of the row; `ladicCharacterLine` is added to express rank-one modules.

## `ladicCharacterLine`

`ladicCharacterLine χ`, for a character `χ : H →* Eˣ`, is the rank-one representation on `E`
on which `h` acts by `χ h`: the Library's `FiniteRepresentation.twist χ` of the trivial
representation on `E`. For a representation `V`, the tensor product `V ⊗ L` with this line is
represented by the twist `FiniteRepresentation.twist χ A`, which has the same carrier as `A`, so
the slope summands of `V` and of `V ⊗ L` are subspaces of the same space.

## `IrreducibleSingleSlopeStatement`

For `ℓ ≠ p`, `f` a topological embedding whose image contains wild inertia, and `A` continuous,
with a finite model and irreducible: the set of slopes is `{s(V)/r}` with `r = A.rank`, and
`V_{s(V)/r} = V`. Since the slope decomposition is `H`-stable (`SlopesExactStatement`), an
irreducible module is purely of one slope `λ`, and then `s(V) = λ r` (Laumon (2.1.2.4)–(2.1.2.5);
compare Henniart 1988, §4.1, p. 510: `s(σ) = n(σ) λ(σ)` for `σ` irreducible on inertia).

## `UnramifiedTwistSwanStatement`

Two invariance properties of the slope decomposition.

1. **Twists.** For every `f`, every representation `A` and every character `χ : H →* Eˣ` with
   `χ h = 1` whenever `f h` lies in wild inertia, `V_μ` is the same subspace for `A` and for its
   twist by `χ`, for every `μ`; hence the slopes and `s(V)` agree. No continuity is needed: the
   groups `P`, `G^(μ+)` (`μ ≥ 0`) and `G^μ` (`μ > 0`) defining the summands lie in wild
   inertia, where the twist does not change the action. A line trivial on inertia, in particular
   one of `Langlands.Henniart.LocalNumerical.ladicUnramifiedCharacters`, is trivial on wild
   inertia, so this covers Laumon's unramified twists, and also every tame twist.
2. **Transport of structure.** Let `τ₀ : K ≃+* K'` be an isomorphism of nonarchimedean local
   fields preserving the valuation (`τ₀ a ≤ᵥ τ₀ b ↔ a ≤ᵥ b`), `τ : Ω ≃+* Ω'` an isomorphism of
   separable closures extending it, and `c : (Ω ≃ₐ[K] Ω) ≃* (Ω' ≃ₐ[K'] Ω')` the conjugation by
   `τ`, characterized by `c σ (τ x) = τ (σ x)`. For a representation `A` of `H` with
   `f' : H →* (Ω' ≃ₐ[K'] Ω')`, the slope summands over `K'` through `f'` equal those over `K`
   through `c⁻¹ ∘ f'`. The upper ramification groups are defined from the valuations alone, so
   `c` carries them to each other (Serre IV §3). The coordinate negation `a(x) = −x` of the
   Fourier transform (Laumon, Corollaire (1.2.2.3), p. 143, and (2.5.6), p. 169) acts on the end traits of
   `Langlands.Correspondence.Laumon.Traits`, completed to `k((t))`, by the `k`-automorphism
   `t ↦ −t`; this is the case `K = K' = LaurentSeries k`, `τ₀` this automorphism and `τ` any
   extension of it to `Ω`. So the pullback by the negation preserves all slopes and `s(V)`.

## `SwanOneTensorStatement`

Laumon, Proposition (2.1.2.7): let `L` be an `I`-module of rank one and Swan conductor one; then
for every `I`-module `V`, (i) `s(V ⊗ L) = r(V_{[0,1[}) + s(V_1 ⊗ L) + s(V_{]1,∞[})`, and
(ii) `s(V_1 ⊗ L) ≤ s(V_1)`, with equality if and only if `(V_1 ⊗ L)^(I^(1−ε)) = 0` for at least
one `ε ∈ [0, 1/r(V_1)[`. The proof rests on the fact that for a simple `P`-module `W` of slope
`λ`, `W ⊗ L` is simple of slope `max(1, λ)` if `λ ≠ 1` and of slope `≤ 1` if `λ = 1`; Katz's
second lemma, pp. 214–215, is the case of a line of Swan conductor larger than all slopes.

Lean form. For `ℓ ≠ p`, `f` a topological embedding whose image contains inertia, a character
`χ : H →* Eˣ` whose line is continuous, has a finite model and has `s = 1`, and `A` continuous
with a finite model, put `B = V ⊗ L` (the twist of `A` by `χ`), `B_μ` its slope summands,
`r₁ = dim V_1` and `s₁ = Σ_μ μ · dim (B_μ ∩ V_1)`. Then:

1. `V_μ ⊆ B_1` for `μ < 1`; `B_μ = V_μ` for `μ > 1`; `B_μ ⊆ V_1` for `μ < 1`; and
   `V_1 ⊆ Σ_{μ ≤ 1} B_μ`;
2. `s(B) = Σ_{μ < 1} dim V_μ + s₁ + Σ_{μ > 1} μ · dim V_μ`, Laumon's (i);
3. `s₁ ≤ r₁`; and if `V_1 ≠ 0`, `s₁ = r₁` if and only if `V_1 ∩ B^(G^(1−ε)) = 0` for some
   `ε` with `0 ≤ ε < 1/r₁`, Laumon's (ii).

Here `V_1 ⊗ L` is the subspace `V_1` of `B`. It is a sub-`H`-module, so its slope-`μ` part is
`B_μ ∩ V_1` (by the exactness clauses of `SlopesExactStatement`), and `s₁` is its Swan conductor
`s(V_1 ⊗ L)`; its vectors fixed by `G^(1−ε)` are `V_1 ∩ B^(G^(1−ε))`. Since `V_1` is purely of
slope one, `s(V_1) = r(V_1)`, which is the right side of Laumon's inequality. The condition
`V_1 ≠ 0` makes the interval `[0, 1/r(V_1)[` meaningful; for `V_1 = 0` both sides of the
inequality vanish.

The equality criterion is proved through the inertia-stable blocks of `V_1 ⊗ L`. Each `B_μ ∩ V_1`
is stable under `H`, so by `SlopeIntegralityStatement` (in
`Langlands.Correspondence.Laumon.SlopeIntegrality`) `μ · m` is an integer for its dimension
`m ≤ r₁`. If `μ < 1` this gives `μ ≤ 1 − 1/m ≤ 1 − 1/r₁`. If `V_1 ∩ B^(G^(1−ε)) = 0` with
`ε < 1/r₁`, every slope of `V_1 ⊗ L` is at least `1 − ε > 1 − 1/r₁`, so all of them equal one and
`s₁ = r₁`; conversely, if `s₁ = r₁` all slopes of `V_1 ⊗ L` are one and `ε = 0` works. Laumon's
proof applies integrality to simple `P`-submodules `W` of `V_1`, where `μ · r(W)` need not be an
integer (Katz 1983, p. 213); the blocks above are inertia-stable, which is what the integrality
statement covers.

## Generality

The statements are for all nonarchimedean local fields, of either characteristic, and `ℓ ≠ p`
(the twist and transport clauses need no condition on `ℓ`). Laumon works with henselian traits of
equal characteristic.

## Declarations used

The module imports `Langlands.Correspondence.Laumon.SlopeIntegrality` and
`Langlands.Weil.Representation.Twist`. It uses `slopeSummand`, `slopeSupport` and `ladicSwan` of
`Langlands.Correspondence.Laumon.Slopes`, and the Library's `FiniteRepresentation.twist`,
`FiniteRepresentation.of`, `localAbsoluteUpperRamificationGroup`, `localWildInertia`,
`absoluteInertia`, `Langlands.fixedVectors`, `IsLadicContinuous` and
`IsLadicDefinedOverFiniteExtension`. It uses no declaration of weil-conjectures. Every
declaration of this module depends at most on `propext`, `Classical.choice` and `Quot.sound`.
