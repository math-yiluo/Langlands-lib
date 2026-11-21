# The twisted endoscopic condition for the cyclic block embedding

Derived from Clozel–Rajan, *Solvable base change*, arXiv:1806.02513v1, §6: the Shapiro cocycle (6.5) (PDF p. 16), the condition (E5) in the form (6.7)–(6.10) (PDF p. 17), the sections (6.13)–(6.14) (PDF p. 18), and the character recurrence (6.15) with the verification at the lift of `σ`, (6.16)–(6.17) (PDF p. 19). The condition itself is (2.1.4a) of Kottwitz–Shelstad, *Foundations of twisted endoscopy*, §2.1 (printed p. 17, PDF p. 22): `Int(s) ∘ Lθ ∘ ξ = a′ · ξ` for a 1-cocycle `a′` of the Weil group in the centre of the dual group.

This file proves that condition for the published block homomorphism `shiftedBlockEmbedding` (`ξ₀`) of `CyclicRelativeWeilBlockSum`. The proof works whenever the character family satisfies the recurrence. It uses an explicit twisting element that includes a block permutation. The Weil group is the actual relative Weil group `RelativeWeilGroup c F E`, and the characters are actual Hecke characters of `E`.

## Setting

The setting is the one of `CyclicRelativeWeilBlockSum`. `E/F` is a Galois extension of number fields and `κ : (E ≃ₐ[F] E) ≃* Multiplicative I` labels the Galois group by a finite additive group `I`. The map `r : I → RelativeWeilGroup c F E` is a transversal with `degree (r i) = ofAdd i` (hypothesis `hr`). `δ_i(w) = ideleDefect … i w` is the idele class with `r_i w = δ_i(w) r_(i+k(w))`, where `k` is the degree. The dual group of `Res_{E/F} GL_n`, for `n = b · |I|`, has one factor of `GL_n(ℂ)` for each outer label `i`. Here `n × n` matrices are indexed by `Fin b × I`, so each outer factor is a matrix of `|I|` blocks of size `b`. The Weil group permutes the outer factors through `shiftAction`. `ξ₀` sends `(h, w)` to the element whose outer factor `i` is the block diagonal matrix with block `α` equal to `η_α(δ_i(w)) · h_(i−α)`.

Fix `σ : E ≃ₐ[F] E` and write `ι = (κ σ).toAdd` for its label. Nothing here assumes that `σ` generates the Galois group, that `I` is cyclic of prime order, or that the characters have finite order.

## Definitions

- `blockShift b ι` is the permutation matrix of the relabelling `(j, α) ↦ (j, α + ι)` of `Fin b × I`, as an invertible matrix. Its inverse is the permutation matrix of the inverse relabelling. `blockShift_conj_blockDiag` shows that conjugating a block diagonal matrix by it moves the block at `α + ι` to position `α`. `blockDiag_scalar` identifies the block diagonal matrix with all blocks equal to one scalar with the scalar matrix.
- `shapiroCocycle ω w i = ω(δ_i(w))` is the cocycle of Clozel–Rajan (6.5), `a_i(w) = ω(δ_i(w))`, for any Hecke character `ω` of `E`. `shapiroCocycle_mul` proves the cocycle law `a(ww′)_i = a(w)_i · a(w′)_(i+k(w))` for the shifted action, using `ideleDefect_mul`. `shapiroCocycle_inclusion` gives its value on the idele classes of `E`: `ω` applied after the arithmetic transport by the Galois image of `r_i`. `shapiroCentral ω w` is the corresponding central element of the dual group, the scalar matrix `a(w)_i` in each outer factor. This file does not prove the Shapiro-lemma identification of this cocycle class with `ω`.
- `IsBlockRecurrence F E κ σ η ω` is the recurrence (6.15), `η_(α+1) ∘ σ = ω η_α`, with `+1` replaced by the label `ι` of `σ`: for every `α`, `HeckeCharacter.comap σ.toRingEquiv (η (α + ι)) = ω * η α`. In terms of values, `η_(α+ι)(σ y) = ω(y) η_α(y)` for every idele class `y` of `E`.
- `dualShift F E κ σ b f` is the dual automorphism `θ̂` of `θ` (the automorphism of `Res_{E/F} GL_n` defined by `σ`). On a function of the outer labels it is the translation `f ↦ (i ↦ f (i + ι))`. This sign is the convention for which `ξ₀` and the twisting element below satisfy (E5).
- `twistingElement` is the element `s` of the dual group whose outer factor `i` is

  `s_i = diag_α(η_(α+ι)(ε_i)) · P_ι`,  with  `ε_i = δ_ι(r_i)`,

  where `P_ι = blockShift b ι`. By definition of the defects, `ε_i` is the idele class of `r_ι r_i r_(ι+i)⁻¹`.

## Results

`projection_transversal` shows that `r_ι` projects to `σ`. `ideleDefect_transversal` is the comparison of defects under conjugation by `r_ι`:

`ε_i · δ_(i+ι)(w) = σ(δ_i(w)) · ε_(i+k(w))`.

Both sides map to `r_ι r_i w r_(ι+i+k(w))⁻¹` under the injective inclusion of idele classes. The proof uses `RelativeWeilGroup.conjugation`, according to which conjugation by `r_ι` acts on the idele classes by the arithmetic transport of `σ`.

`twistingElement_conj` is the coordinate form of (E5). Assume `IsBlockRecurrence F E κ σ η ω`. Then for every `x = (h, w)` and every outer label `i`,

`s_i · ξ₀(x)_(i+ι) · s_(i+k(w))⁻¹ = a(w)_i · ξ₀(x)_i`.

The proof conjugates by `P_ι`, which turns block `α + ι` of `ξ₀(x)_(i+ι)` into a block with the same factor `h_(i−α)` as block `α` of `ξ₀(x)_i`. It then moves all scalars past `h_(i−α)`. What remains is the scalar identity

`η_(α+ι)(ε_i) · η_(α+ι)(δ_(i+ι)(w)) · η_(α+ι)(ε_(i+k(w)))⁻¹ = ω(δ_i(w)) · η_α(δ_i(w))`.

The left side is `η_(α+ι)(σ(δ_i(w)))` by `ideleDefect_transversal`. The right side equals the same value by the recurrence.

`twistedEndoscopicCondition` is the same identity in the semidirect product. With `U` the dual group of `Res_{E/F} GL_n` extended by the relative Weil group, and for every `x` in the extended dual group of the endoscopic group, it proves

`(s, 1) · (θ̂(ξ₀(x)_left), w) · (s, 1)⁻¹ = (a(w) · ξ₀(x)_left, w)`,

where `w` is the Weil component of `x`. This is `Int(s) ∘ Lθ ∘ ξ₀ = a · ξ₀`, the form of (2.1.4a) with the cocycle `a′` equal to the Shapiro cocycle of `ω`. It is also Clozel–Rajan (6.7), `s θ̂(g) w(s)⁻¹ = a(w) g`.

`twistingElement_conj_dual` is the case `w = 1`. There the cocycle is trivial, so `ξ₀` maps the dual group `(GL_b)^I` of the endoscopic group into the fixed points of `Int(s) ∘ θ̂`.

## Relation to the source

Clozel–Rajan work with the section `z_(i,α)(w) = η_(i+α)(δ_i(w))` of (6.14) and a diagonal twisting element. With that section and that twisting element, the equations (6.17) at the lift of `σ` need not hold. (For degree two they can hold, depending on the choice of characters.) Clozel–Rajan therefore introduce a coboundary correction of the section after (6.17) (PDF pp. 19–21), and they prove in Lemma 3 (PDF p. 21) that the corrected section is conjugate to the original one. This file does not use the corrected section. Its twisting element contains the block permutation `P_ι`, and the recurrence gives (E5) for every element of the relative Weil group at once, the lift of `σ` included, for every finite label group `I` (in particular `|I| = 2`). This file does not prove that its datum is equivalent to the one Clozel–Rajan construct.

Informal remark, not formalized here: suppose `I = ℤ/p`, `ι = 1` and `r_i = t^i` for `0 ≤ i < p`. Then `ε_i = 1` except `ε_(p−1)`, the idele class of `t^p`. An element `g` is fixed by `Int(s) ∘ θ̂` exactly when `g_i = s_i g_(i+1) s_i⁻¹` for all `i`. So its factor `g_0` commutes with the product `s_0 s_1 ⋯ s_(p−1)`, which is block scalar with block `α` equal to `η_α(t^p)`. The recurrence at the `σ`-fixed class `t^p` gives `η_α(t^p) = η_0(t^p) ω(t^p)^α`. If `ω(t^p)` is a primitive `p`-th root of unity `ζ`, these scalars are distinct, as in Clozel–Rajan's choice `s_0 = (1, ζ, …, ζ^(d−1))`.

## Scope

This file proves only (2.1.4a) and the inclusion of `ξ₀((GL_b)^I)` in the fixed points of `Int(s) ∘ θ̂`. It does not prove or assume any of the following:

- (2.1.3), that `s` is `θ`-semisimple;
- (2.1.4b), that `ξ₀` maps onto the identity component of the twisted centralizer;
- that the Shapiro cocycle of `ω` represents the class attached to the twisting character of the trace formula, or which of a character and its inverse that is for the operator conventions of `AdelicGLCharacterTwistOperator`;
- existence of families `η` satisfying the recurrence (which needs `ω` to be trivial on the norm-type products `∏_τ τ(y)`);
- ellipticity, uniqueness of the endoscopic datum (Clozel–Rajan Proposition 5), or its absence when the rank is not divisible by the degree (Proposition 4(1));
- any transfer of functions or trace identity.
