# Maximal-parabolic decay on Levi Siegel regions

Module `Langlands.Global.AdelicShiftedMaximalDecay`, namespace
`Langlands.Global.StandardParabolicFamily`. It states and proves
`RelativeCuspidalRegionDecayStatement` (theorem `relativeCuspidalRegionDecay`): rapid decay of
cuspidal functions along a standard parabolic `P_J` on Siegel regions of the Levi `M_J`. On these
regions only the simple roots of `J` are bounded below. The main step is
`shiftedMaximalDecay`, the decay of Mœglin–Waldspurger I.2.10 along a maximal parabolic
`J \ {β}` of `M_J` on the same kind of region.

## Setting

`𝓕` is a compatible standard parabolic family of a connected reductive group `G` over a number
field `F`, with maximal split torus `T` (`𝓕.T`), simple roots `Δ` and standard indices `J ⊆ Δ`.
Points of the positive torus are the intrinsic positive points `a` of `T`, mapped to `G(𝔸)` by
`aG = positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T)`. `hG` is a smooth relative dimension of `G`, `rho` a
matrix representation of `G` of size `N > 0` and `height` its adelic height
(`RepresentationGrowth.adelicHeight`). Derivatives are the right-orbit derivative words
`adelicIteratedDirectionalValue` of the module `Langlands.Global.AdelicMaximalUnipotentDecay`,
along the basis `Module.finBasis ℝ (smoothModel F d)`.

## Declarations

### `exists_splitComponent_shift`

Let `J` be a standard index and `a` a positive torus point whose roots in `J` are at least `b`.
Then there are a point `s` of the positive split component `𝔄_J` of `P_J`
(`positiveSplitComponent J`) and a positive torus point `sT` with: the image of `s` in `G(𝔸)` is
`aG sT`; every root of `J` is `1` at `sT`; and `sT a` lies in the weak simple-root chamber of `G`
with threshold `b` (`weakSimpleRootChamber`).

*Proof.* The compatibility of `𝓕` gives a cocharacter `ζ` of `T` pairing to `0` with the roots
of `J` and to at least `1` with the other simple roots. Let
`t = ∑_{α ∈ Δ} max(0, log b − log |α(a)|)` and choose a positive torus point `x` with logarithm
`t ζ` (`exists_characterLog_eq`). Its roots in `J` are `1`, so the published
`positiveTorusSplitComponent` makes `x` the image of a point `s ∈ 𝔄_J`. For `α ∈ J` the value at
`sT a` is the value at `a`. For `α ∉ J` its logarithm is
`t ⟨α, ζ⟩ + log |α(a)| ≥ t + log |α(a)| ≥ log b`.

### `range_map_le_of_le` and `IsRadicalInvariant.splitComponent_mul_comm`

For `Q ≤ P` the adelic image of `P_Q` lies in that of `P_P` (`le_iff_range_le`). If `f` is left
invariant under `U_J(𝔸)` (`IsRadicalInvariant J f`), `s ∈ 𝔄_J` and `x ∈ P_J(𝔸)`, then
`f(s x g) = f(x s g)`. The reason is that `s x = u x s` with `u = s x s⁻¹ x⁻¹ ∈ U_J(𝔸)`, by the
published `commutator_mem_radical_of_splitComponent`.

### `adelicIteratedDirectionalValue_leftTranslate`

Derivative words, being right-orbit derivatives, commute with left translation:
`D(f(c ·))(x) = (D f)(c x)`. The proof is by induction on the word.

### `exists_compact_factors_height_bound`

For compact sets `Ω` and `K` there is `C ≥ 1` with `ht(p a k) ≤ C ht(a)` for `p ∈ Ω` and `k ∈ K`.
This follows from submultiplicativity and continuity of the height.

### `shiftedMaximalDecay`

Fix a standard index `J`, `β ∈ J`, a threshold `b`, an order `n`, an exponent `R ≥ 0`, compact sets
`Ω ⊆ P_0(𝔸)` and `K ⊆ G(𝔸)`, a compact set `Y_f` of finite adelic points and an open finite level
`L`. There is a constant `C ≥ 0` with the following property. Let `f` be continuous on `G(𝔸)`,
smooth on the archimedean slices, left invariant under `P_0(F)` and under `U_J(𝔸)`, and right
invariant under `L`. Assume its constant term along `J \ {β}` (`removeSimpleRoot J β`) vanishes,
and that every derivative word of length `n` is bounded by `M_w ht(x)^R` on all of `G(𝔸)`.
Take `p ∈ Ω`, a positive torus point `a` whose roots in `J` are at least `b`, and `k ∈ K` with
the finite part of `p a k` in `Y_f`. Then

`|f(p a k)| ≤ C |β(a)|^{-n/[F:ℚ]} M_w ht(a)^R`

(the factor `|β(a)|^{-1/[F:ℚ]}` is `relativeCharacterDecay (𝟙 𝓕.T) β a`). The constant does not
depend on `f` or `M_w`.

*Proof.* The published `adelicMaximalUnipotentDecay` (the iterated form of MW I.2.10 on the weak
simple-root chamber of `G`) is applied along the maximal parabolic `Δ \ {β}` of `G`. It yields
an enlarged compact set `K'` and a constant `C_d`. Given `a`, take `s` and `sT` from
`exists_splitComponent_shift`, write `S` for the image of `s`, and set
`f_s = f(S⁻¹ ·) = unnormalizedAction J s⁻¹ f`. The point `sT a` lies in the chamber, and
`f_s(p aG(sT a) k') = f(p aG(a) k')` because `S = aG sT` and `S⁻¹` passes `p ∈ P_J(𝔸)`
(`splitComponent_mul_comm`). The function `f_s` satisfies the hypotheses of the published
decay theorem:
- `f_s` is left invariant under `P_0(F)` and `U_J(𝔸)`, again by `splitComponent_mul_comm` and by
  `IsRadicalInvariant.unnormalizedAction`;
- its constant term along `Δ \ {β}` equals that along `J \ {β}` (the published
  `adelicRelativeCuspidalConstantTerm`), and this is the shift of the constant term of `f`
  (`constantTerm_unnormalizedAction_of_radicalInvariant`), hence zero;
- it is smooth on the archimedean slices, as a left translate in the archimedean Lie group;
- its finite part at the shifted point is unchanged (`finite_positiveMap`).
The derivative words of `f_s` at `p aG(sT a) k'` are those of `f` at `p aG(a) k'`
(`adelicIteratedDirectionalValue_leftTranslate`; the words of `f` are again `U_J(𝔸)`-invariant).
They are therefore bounded by `M_w (E ht(a))^R`, with `E` from
`exists_compact_factors_height_bound` for `Ω` and `K'`. Finally
`β(sT a) = β(a)`, as `β ∈ J`. The constant is `C = C_d E^R`.

### `ratSpan_eq_top_of_span_eq_top` and `exists_abs_le_of_mem_span`

A set generating an abelian group `M` over `ℤ` spans `ℚ ⊗ M` over `ℚ` (`ratSpan`). If `v` lies in
the real span of a set `X`, there is `K ≥ 0` with `|ℓ(v)| ≤ K B` for every linear form `ℓ` with
`|ℓ| ≤ B` on `X` (write `v` as a finite combination and take `K` the sum of the absolute values of
the coefficients).

### `exists_regionHeight_bound`

Let `J` be a set of characters of `T` and `Φ` a set of real linear forms on `𝔞_0 = V T`
(elements of `Vstar T`) such that the vectors `1 ⊗ γ` (`γ ∈ J`) and `Φ` span `𝔞_0^*` over `ℝ`. For
a threshold `b` there are `C₀ ≥ 1` and `r ≥ 0` with the following property. Let `a` be a positive
torus point with logarithm `H ∈ 𝔞_0` (`cocharacterFunctional H = characterLog a`). If the
characters of `J` are at least `b` at `a` and have logarithms at most `t ≥ 0`, and
`|φ(H)| ≤ B` for `φ ∈ Φ`, then `ht(aG a) ≤ C₀ exp(r (max(B, −log b) + t))`.

*Proof.* The character lattice of the split torus `T` is finitely generated; a finite generating
set `S` has `ratSpan S = ⊤`, so the published `adelicPositiveTorusLogHeightBound` applies to `S`.
Each `1 ⊗ χ`, `χ ∈ S`, is a real combination of the spanning vectors, on which the logarithm is
bounded by `max(B, −log b) + t`; hence `|log |χ(a)|| ≤ K (max(B, −log b) + t)` with a constant
`K` for all `χ ∈ S`.

### `RelativeCuspidalRegionDecayStatement` and `relativeCuspidalRegionDecay`

Assume `N > 0`. Let `J` be a standard index and `Φ` a set of real linear forms on `𝔞_0` such that
`Φ` and the simple roots of `J` span `𝔞_0^*` over `ℝ`. Fix `b`, `B ≥ 0`, compact `Ω ⊆ P_0(𝔸)` and `K`, a compact `Y_f` and an open
finite level `L`. Let `f` be continuous, smooth on the archimedean slices, left invariant under
`P_0(F)` and `U_J(𝔸)`, right invariant under `L`, with vanishing constant terms along
`J \ {β}` for every `β ∈ J`. Assume that for every derivative word `D` there is `C_D ≥ 0` with
`|D f(x)| ≤ C_D ht(x)^R` on `G(𝔸)`, for one exponent `R ≥ 0`. Then for every `m ∈ ℕ` there is
`C ≥ 0` with

`|f(p a k)| ht(p a k)^m ≤ C`

for `p ∈ Ω`, `a` with roots in `J` at least `b` and logarithm `H` with `|φ(H)| ≤ B` for
`φ ∈ Φ`, `k ∈ K`, and the finite part of `p a k` in `Y_f`. Real forms are allowed in `Φ` (not only
characters) so that weights of the root system, which are real combinations of roots, can be
used as complementary coordinates.

*Proof.* The argument is that of the published `adelicRelativeCuspidalRapidDecay`, with
`shiftedMaximalDecay` in place of `adelicMaximalUnipotentDecay`; this is what removes the
chamber condition on the roots outside `J`. Let `t` be the largest of `0` and the logarithms of
the roots of `J` at `a`. By `exists_regionHeight_bound`, `ht(aG a) ≤ A₀ e^{r t}`. If `t = 0`, the
height of `p a k` is bounded and the order-zero growth bound gives the estimate. Otherwise `t`
is the logarithm of a root `β ∈ J`. The order `n` is chosen with `n/[F:ℚ] ≥ r (R + m)`, and
the derivative words of length `n` are bounded by `W_n ht(x)^R`, with `W_n` the sum of the
finitely many constants. Then `shiftedMaximalDecay` for `β` gives
`|f(p a k)| ht(p a k)^m ≤ C_β W_n E₀^m e^{-n t/[F:ℚ]} ht(aG a)^{R+m} ≤ C_β W_n E₀^m A₀^{R+m}`.
The constant is the sum of the bounds over the finitely many `β ∈ J` and the bounded case.

## Sources and provenance

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.2.10 (pp. 30–33), the
  decay of a function with vanishing constant term along a maximal parabolic, and I.2.12
  (Corollary, p. 35), rapid decrease of cuspidal functions on Siegel domains.

The statement is derived. It is the relative form, for the Levi `M_J` inside `G`, of the rapid
decrease of cusp forms on Siegel domains (MW I.2.12, I.2.18). The proof reduces it to the
Library's decay theorem on the chamber of `G` (`adelicMaximalUnipotentDecay`, MW I.2.10) by
translating with positive points of the split component of `P_J`. These points are central in
`M_J` and trivial on the roots of `J`, and they move a point of a Levi Siegel region into the
chamber of `G`.
