# A uniform Weyl displacement bound for the minimal Iwasawa height

Module `Langlands.Global.ArthurWeylHeightStatement`, namespace
`Langlands.Global.ArthurTruncation`. The module states one proposition,
`WeylHeightLowerBoundStatement`, and does not prove it. The objects are those of
`Langlands.Global.ArthurTruncation` and of the statements of
`Langlands.Global.ArthurSiegelSetsIwasawaStatement` (see their Markdown, in particular "Common
hypotheses").

## Statement

`WeylHeightLowerBoundStatement` quantifies over the data of
`IwasawaTruncationIdempotentStatement`, in the same order and with the same types: a number field
`F`; a group scheme `G` over `F`, affine and locally of finite type; a commutative group scheme
`T` with `i : T → G` whose underlying morphism is a monomorphism; a cocharacter `ν`; `hG`
(`IsConnectedReductive G`, written `_hG` in the Lean binder since the conclusion does not refer
to it); `hi` (`IsMaximalSplitTorus i`); the genericity `IsGenericCocharacter i ν` (fixing the
minimal parabolic subgroup `P_0 = Standard.parabolicHom i ν ∅` with unipotent radical
`N_0 = Standard.unipotentHom i ν ∅`); reflection data `D : RelativeRootReflectionData i`; a
subgroup `K` of `G(𝔸) = AdelicGroupPoints F G` with `hK : IsIwasawaCompact (Standard.parabolicHom
i ν ∅) K` (`K` compact and `P_0(𝔸)K = G(𝔸)`, with no maximality or admissibility condition); and
the bijectivity `hρ : Function.Bijective (restrictToTorus F i ν ∅)`. Write
`H_0 = height hi hK hρ : G(𝔸) → 𝔞_0 = V T` for the Iwasawa height of `K` read in `V T`.

The proposition asserts: for every simple relative root `β : simpleRelativeRoots i ν`, every
`ϖ : Vstar T` with `D.IsRealFundamentalWeight ν β ϖ` (the fundamental weight `ϖ_β ∈ Δ̂_0`: in the
real span of the relative roots, `⟨ϖ, β̌⟩ = 1` and `⟨ϖ, α̌⟩ = 0` for the other simple roots `α`,
with the real coroots of `D`) and every rational normalizing point `n : normalizerPoints i`, with
Weyl class `s = QuotientGroup.mk n : relativeWeylGroup i` and adelic image
`w = innerAdelicPoint F G n.val ∈ G(𝔸)`, there is a real `B ≥ 0` such that for every
`v ∈ N_0(𝔸)` (an element of `AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range
(Standard.unipotentHom i ν ∅))`) and every `x ∈ G(𝔸)`:

`pair T ϖ (H_0 x) ≤ pair T (relativeWeylFullRealAction i s ϖ) (H_0 (w * v * x)) + B`,

that is, `ϖ(H_0(x)) ≤ (sϖ)(H_0(w v x)) + B`. The constant `B` is chosen after `β`, `ϖ`, the lift
`n` and all the data above (in particular `K`), and is uniform in `v` and `x`. The proposition
contains no representation, height comparison, truncation parameter `T` or regularity condition.

**The Weyl action.** `n` normalizes `i` through the automorphism `σ` of `T` with
`σ(t) = n t n⁻¹` (`IsNormalizingPoint`). The action `relativeWeylFullRealAction i s` on
`Vstar T` is the real extension of `χ ↦ χ ∘ σ⁻¹` on characters, and the action
`relativeWeylRealAction i s` on `V T` is the real extension of `μ ↦ σ ∘ μ` on cocharacters; the
pairing is invariant under the two together (`pair_relativeWeyl`). With these conventions
`H_0(w m w⁻¹) = s·H_0(m)` for `m` in the Levi component `M_0(𝔸)` (the centralizer of the split
torus), which is the direction used below.

## Source

J. Arthur, *A trace formula for reductive groups II: applications of a truncation operator*
(1980), registered as `arthur-1980-trace-formula-reductive-groups-II` (PDF page = printed page −
85), §1, proof of Lemma 1.1, printed p.91 (PDF p.6). After writing
`s⁻¹(H_0(w_s n^* x) − T)` as a sum, Arthur states for `v ∈ N_0(𝔸)`: "If `ϖ ∈ Δ̂_0`, it is well known
that `ϖ(s⁻¹H_0(w_s v w_s⁻¹))` is nonnegative and `ϖ(T − s⁻¹T)` is strictly positive." The
representatives `w_s` are fixed in Arthur 1978, §1, printed p.917 (PDF p.7; registered as
`arthur-1978-trace-formula-reductive-groups-I`), in the intersection of `G(ℚ)` with the normalizer
of `A_0`, and `K` is the maximal compact subgroup fixed there with properties (i)–(iii).

**Scope of the derived formulation.** The source works over `ℚ`, with its fixed `K`, and uses the
exact nonnegativity of `ϖ(s⁻¹H_0(w_s v w_s⁻¹)) = (sϖ)(H_0(w_s v w_s⁻¹))`. The proposition is
stated over every number field, for every compact `K` with `P_0(𝔸)K = G(𝔸)` and every rational
normalizing point `n` (not only one fixed representative per Weyl element), with one additive
error `B` depending on `K`, `n` and `ϖ`. It is the form in which the inequality enters the argument
of Lemma 1.1 for a general `K` (see "Why every compact Iwasawa subgroup" in the Markdown of
`ArthurSiegelSetsIwasawaStatement`): there the additive error is absorbed by the regularity of
`T`, because `ϖ(T − s⁻¹T) = (ϖ − sϖ)(T)` is a nonzero nonnegative combination of the values
`α(T)`, `α ∈ Δ_0`, when `sϖ ≠ ϖ`. The cutoff, the Bruhat unfolding and the cancellation of
Lemma 1.1 are not part of this statement.

## Derivation

The following explains why the proposition holds; this file does not contain a proof.

**Reduction to `N_0(𝔸)`.** Write `x = u m k` with `u ∈ N_0(𝔸)`, `m ∈ M_0(𝔸)`, `k ∈ K`. Then
`w v x = (w m w⁻¹)(w u') k` with `u' = m⁻¹ v u m ∈ N_0(𝔸)` and `w m w⁻¹ ∈ M_0(𝔸)`. As `H_0` is
right `K`-invariant, additive under left translation by `P_0(𝔸)` and trivial on `N_0(𝔸)`,
`H_0(w v x) = s·H_0(x) + H_0(w u')`, so by `pair_relativeWeyl`

`(sϖ)(H_0(w v x)) = ϖ(H_0(x)) + (sϖ)(H_0(w u'))`.

The proposition is therefore equivalent to a lower bound of `(sϖ)(H_0(w u))` over
`u ∈ N_0(𝔸)`, uniform in `u`. Given a compact subgroup `K_0` of the class and a rational
representative `w_s` of `s` for which Arthur's nonnegativity holds, this lower bound follows from
the bounded differences of heights (Markdown of `ArthurTruncationStatement`, "Bounded
difference"): `H^K − H^{K_0}` is bounded on `G(𝔸)`, and `H^{K_0}(g c) − H^{K_0}(g)` is bounded
for `c` in a compact set. Indeed `w = w_s z` with `z ∈ M_0(F)` (both represent `s`), so
`w u = (w_s (z u z⁻¹) w_s⁻¹) w_s z` with `z u z⁻¹ ∈ N_0(𝔸)`, and right translation by the fixed
point `w_s z` changes the height by a bounded amount.

**A direct derivation for the given `K`.** Let `P_β ⊇ P_0` be the standard maximal parabolic
subgroup with `Δ_0^{P_β} = Δ_0 ∖ {β}`. Take a rational representation `ρ` of `G` on `V` and a
nonzero `e ∈ V(F)` whose line is stable under `P_β`, with `P_β` acting by a character `χ` (a
Chevalley line). Its restriction to the split torus is `dϖ + μ` with `d > 0` and `μ` the
restriction of a real combination of rational characters of `G`. Put `y = w v x`. Since `v` is
unipotent, `ρ(y)⁻¹ρ(w)e = ρ(x)⁻¹ρ(v)⁻¹e = ρ(x)⁻¹e`.

- With `x = p k`, `p ∈ P_0(𝔸)`, `k ∈ K`, the vector `ρ(x)⁻¹e = χ(p)⁻¹ρ(k)⁻¹e` has adelic height
  comparable, with constants from the compact set `K`, to `e^{−χ(H_0(x))}`.
- With `y = q k'`, `q ∈ P_0(𝔸)`, `k' ∈ K`, the vector `ρ(w)e` is a weight vector whose line is
  stable under `M_0 ⊆ w P_β w⁻¹`, with character `sχ`. Projecting `ρ(q)⁻¹ρ(w)e` to the degree of
  `ρ(w)e` for the generic cocharacter `ν` removes the `N_0`-part of `q`, and the coordinate equal
  to `1` on `ρ(w)e` is `(sχ)(q)⁻¹`. The adelic norm of this coordinate is at most the height of the
  vector, so `e^{−(sχ)(H_0(y))}` is bounded by a constant times the height of `ρ(y)⁻¹ρ(w)e`.

Comparing the two bounds gives `χ(H_0(x)) ≤ (sχ)(H_0(y)) + C`. The `μ`-terms agree: the Weyl group
fixes `μ`, and `μ(H_0(y)) = μ(H_0(x))` by the product formula for the rational point `w` and
because `v` is unipotent. Dividing by `d` gives the proposition with `B = max(C/d, 0)`.

## Related declarations

- `height` (`Langlands.Global.ArthurTruncation`): `H_0`, built from `IsIwasawaCompact.height`
  (`Langlands.Global.AdelicIwasawaHeight`).
- `RelativeRootReflectionData.IsRealFundamentalWeight`
  (`Langlands.GroupScheme.Rational.RelativeRealCorootStatements`).
- `relativeWeylFullRealAction`, `pair_relativeWeyl`
  (`Langlands.GroupScheme.Rational.RelativeCentralDirections`).
- `innerAdelicPoint` (`Langlands.Automorphic.GroupSchemeConstantTermConjugation`): the adelic
  point of a rational point, by which `innerIso` conjugates adelic points.
- `IwasawaTruncationIdempotentStatement` (`Langlands.Global.ArthurSiegelSetsIwasawaStatement`):
  Arthur 1980, Lemma 1.1, for every compact Iwasawa subgroup, whose proof uses this inequality.

## Provenance

Derived from Arthur 1980, proof of Lemma 1.1, printed p.91 (the nonnegativity of
`ϖ(s⁻¹H_0(w_s v w_s⁻¹))` for `v ∈ N_0(𝔸)` and `ϖ ∈ Δ̂_0`), with the conventions of Arthur 1978,
§1, p.917. The derived formulation (every number field, every compact `K` with
`P_0(𝔸)K = G(𝔸)`, every rational normalizing point, one additive error `B`) is explained in
"Scope of the derived formulation" and "Derivation".
