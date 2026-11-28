# The chambers of `𝔞_P` and the Weyl sets `Ω(P, S)`

Module `Langlands.Global.LocalWavePacketMainTermChamberStatement` defines four auxiliary
predicates and states `Langlands.Global.StandardChamberParametrizationStatement`. The file
states the proposition and does not prove it.

## Sources

- J. Arthur, *On a family of distributions obtained from Eisenstein series II: Explicit
  formulas*, Amer. J. Math. 104 (1982), registered as `arthur-1982-eisenstein-distributions-II`
  (PDF page = printed page − 1288). §1, p.1292: `W(𝔞_M, 𝔞_{M₁})` is the set of isomorphisms
  `𝔞_M → 𝔞_{M₁}` obtained by restricting elements of the Weyl group `W_0` of `(G, A_0)`. p.1295:
  the sum over standard `P₁ ⊇ P_0` and `t ∈ W(𝔞_P, 𝔞_{P₁})` is rewritten as a sum over
  `Q = t⁻¹P₁ ∈ 𝓟(M)`, with `θ_{P₁}(tΛ) = θ_Q(Λ)` and `Y_Q(T)` the projection of
  `t⁻¹(T − T_0) + T_0` to `𝔞_M`. p.1293: `W^L(𝔞_M, 𝔞_{M₁})` is the subset of elements of
  `W(𝔞_M, 𝔞_{M₁})` that fix `𝔞_L` pointwise. §2, p.1298: `{e^{Λ(Y_Q(T))}}` is a
  `(G, M)`-family, and for adjacent `Q`, `Q' ∈ 𝓟(M)` the common wall of their chambers spans
  `i𝔞_L^*` for a Levi subgroup `L ⊇ M` with `dim 𝔞_M^L = 1`.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page = printed page + 9), §7,
  p.326, (15): `⟨α, Y_Q(T)⟩ ≥ c‖T‖` for `α ∈ Δ_Q` and `T` in a cone in the positive chamber;
  §8, p.328, the use of these facts in the proof of Proposition 2.

Clause 5 uses `Y_Q(T)` given by the projection of `t⁻¹T`, as required by the unshifted
exponential in `WavePacketMainTermLimitStatement`. Arthur's Iwasawa height comparison on
p.1294 gives the affine expression `t⁻¹(T − T_0) + T_0` used on p.1295.

## The Euclidean model

The statement works in the setting of `Langlands/LinearAlgebra/GMFamilies.lean`. Given a
linear isomorphism `eV : V T ≃ E` from `𝔞_0 = V T` onto a finite-dimensional real inner product
space in which the relative Weyl group acts by isometries (`relativeWeylRealAction`), and the
finite set `R ⊆ E` of Riesz vectors `rootVectorIn eV α` of the relative roots `α`:

- `standardChamberSpace eV S` is `𝔞_S = {H ∈ 𝔞_0 : α(H) = 0 for α ∈ S}` (`rootAnnihilator`)
  inside `E`;
- `IsParameterTranspose i ν eV J S σ h hS` says that `h ∈ 𝔞_J` corresponds to `hS ∈ 𝔞_S` under
  the transpose of `σ : 𝔞_J^* → 𝔞_S^*`: `⟨σy, hS⟩ = ⟨y, h⟩` for all `y`, the pairing being
  `pair T` after restricting characters to `T` (`restrictToTorus`);
- `IsStandardChamberPoint i ν eV Δ J S σ h` says that `h ∈ 𝔞_J` is the transpose image of a
  point `hS ∈ 𝔞_S` at which every `α ∈ Δ ∖ S` is positive: `h` lies in the chamber
  `σ⁻¹(𝔞_S^+)`;
- `IsSimpleRootTranspose i ν eV J S σ α v` says that `v ∈ 𝔞_J` is the transpose image of the
  orthogonal projection `α_S` of the Riesz vector of `α` to `𝔞_S` (`restrictedRoot`): `v` is
  `σ⁻¹(α_S)`.

`Ωr J S` (a `let` in the statement) is the set of real parameter maps
`realWeylParameter (Standard.leviToParabolic i ν J.roots) c (π S)` of the Weyl conjugations
`(w, c)` from `P_J` to `P_S` (`IsWeylConjugation`): the real form of the Library's
`weylParameterSet`, Lapid's and Arthur's `Ω(P_J, P_S) = W(𝔞_{P_J}, 𝔞_{P_S})`.

## The statement

For a number field `F`, a connected reductive `G`, a maximal split torus `i : T → G`, a generic
cocharacter `ν` with simple roots `Δ_0 = simpleRelativeRoots i ν`, reflection data `D`, Levi
projections `π S`, Euclidean coordinates `eV` as above and `R`:

0. `R` is a root set (`IsRootSet`); the coroot of a relative root is
   `eV(α^∨) = (2/‖α‖²) α` (Riesz vectors); and for every standard `J`, `𝔞_J` is a Levi space
   (`IsLeviSpace`).

For every standard `J`:

1. **Weyl realization.** Every `σ ∈ Ωr J S` is the restriction of the action of an element `w`
   of the relative Weyl group on `𝔞_0^*` (`relativeWeylRealCharacterAction`):
   `σy = wy` after restriction to `T` (Arthur 1982, p.1292).
2. **Chambers.** Every point of the chamber `σ⁻¹(𝔞_S^+)` is regular in `𝔞_J` (`IsRegular`); all
   of its points have the same positive roots (`posSet`); it is not empty; every regular point of
   `𝔞_J` lies in the chamber of some pair `(S, σ)`; and two pairs whose chambers have points with
   the same positive roots are equal (first `S = S'`, then `σ = σ'`). This is the bijection
   between `𝓟(M_J)` (the Library's `parabolics R 𝔞_J`) and `⊔_S Ω(P_J, P_S)`,
   `Q = σ⁻¹(P_S)` (Arthur 1982, p.1295).
3. **Simple roots.** The simple roots `simpleRoots 𝔞_J Q` of the chamber `Q` of `(S, σ)` are the
   vectors `σ⁻¹(α_S)`, `α ∈ Δ_0 ∖ S`, and distinct `α` give distinct vectors. These are positive
   multiples of the coroots `σ⁻¹(α^∨)` of Arthur's `Δ_Q^∨`, so `θ_Q(Λ) = θ_{P_S}(σΛ)`.
4. **Walls.** If the chambers of `(S, σ)` and `(S₂, σ₂)` are adjacent along the simple root
   `σ⁻¹(α_S)` of the first (`IsAdjacentAlong`), then `σ₂ σ⁻¹` fixes the wall `⟨·, α^∨⟩ = 0` of
   `𝔞_S^*` pointwise: `σ₂ y = σ y` in `𝔞_0^*` whenever `⟨σ y, α^∨⟩ = 0`. Thus `σ₂σ⁻¹` lies in
   `W^L(𝔞_{P_S}, 𝔞_{P_{S₂}})` for the Levi subgroup `L` with simple roots `S ∪ {α}`, whose
   space `𝔞_L` is that wall: it is the elementary symmetry of `L`.
5. **The orthogonal set of `T`.** For `T ∈ 𝔞_0` with `α(T) ≥ 0` for every `α ∈ Δ_0` there are
   points `Y_Q ∈ 𝔞_J` that form a positive `(G, M_J)`-orthogonal set
   (`Langlands.GMFamily.IsPositiveOrthogonalSet`), with `‖Y_Q‖ ≤ ‖T‖`, such that for the chamber
   `Q` of `(S, σ)`: `Y_Q` is the transpose image of `T` (`⟨y, Y_Q⟩ = ⟨σy, T⟩` for every
   `y ∈ 𝔞_J^*`, that is, `Y_Q = σ⁻¹(T_S)` with `T_S` the projection of `T` to `𝔞_S`), and
   `α(T) ≤ ⟪σ⁻¹(α_S), Y_Q⟫` for `α ∈ Δ_0 ∖ S`, the bound behind Lapid's (15).

## Use

`Langlands.Global.WavePacketMainTermLimitReductionStatement` (module
`Langlands.Global.LocalWavePacketMainTermLimitReduction`) takes this proposition, with
`WavePacketMainTermFamilyStatement`, as a premise of Lapid's §8 limit: clauses 0–3 write the
main term of formula (2) as `∑_{Q ∈ 𝓟(M)} c_Q d_Q / θ_Q`, clause 4 gives the `(G, M)`-family
property of `d_Q` from the wall relation of `WavePacketMainTermFamilyStatement`, and clause 5
gives the hypotheses of Lemma 8 (`Langlands.GMFamily.OrthogonalSetLimitStatement`) for
`c_Q(T; Λ) = e^{Λ(Y_Q(T))}`.
