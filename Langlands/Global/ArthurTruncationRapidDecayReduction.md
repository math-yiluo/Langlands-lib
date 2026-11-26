# Reduction of Arthur's Proposition 13.2 on `G(F) \ G(𝔸_F)¹`

**Sources.**

- J. Arthur, *An introduction to the trace formula* (2005), in `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §4, printed p. 24 (PDF p. 36), the choice of the maximal compact subgroup `K`; §13, Proposition 13.2(a),(b) and (13.5)–(13.6), printed pp. 70–72 (PDF pp. 82–84).
- J. Arthur, *A trace formula for reductive groups II* (1980), `arthur-1980-trace-formula-reductive-groups-II`: §1, printed p. 89 (PDF p. 4), and Lemma 1.4 with its proof, printed pp. 95–97 (PDF pp. 10–12).
- J. Arthur, *The trace formula in invariant form* (1981), `arthur-1981-trace-formula-invariant-form`: §1, printed p. 9, maximal compact subgroups admissible relative to `M₀`.

The module `Langlands.Global.ArthurTruncationRapidDecayReduction` proves the target `Langlands.Global.ArthurTruncation.TruncationRapidDecayStatement` ([statement](ArthurTruncationRapidDecayStatement.md)) from one proposition stated here, `NormOneTruncationFamilyEstimateStatement`: part (b) of Proposition 13.2 for a suitable maximal compact subgroup. The theorem is `truncationRapidDecayStatement_of_familyEstimate`. The module does not prove `NormOneTruncationFamilyEstimateStatement`. The embedded Lie atlas on `G(F∞)¹` required by the target is `exists_normOneLieAtlas` ([GroupSchemeNormOneAtlas](../Automorphic/GroupSchemeNormOneAtlas.md)). All declarations below are in `Langlands.Global.ArthurTruncation`.

## The family estimate

`IsNormOneFamilyEstimate A hG hi D hK hρ rho Tp` is, word for word, the second conjunct of `IsNormOneTruncationEstimate`. It is part (b), the estimate (13.5)–(13.6), for a given atlas `A`, compact `K`, height `rho` and truncation parameter `Tp`. `isNormOneTruncationEstimate_iff` records, by `Iff.rfl`, that `IsNormOneTruncationEstimate` is part (a) together with this predicate.

## The premise

`NormOneTruncationFamilyEstimateStatement` takes a number field `F`, a connected reductive `G`, a maximal split torus `i`, a generic cocharacter `ν` and an embedded Lie atlas `A : NormOneLieAtlas F G hG.smoothDimension_spec e`. It asserts that there is a subgroup `K` of `G(𝔸_F)` such that

- `P₀(𝔸_F) K = G(𝔸_F)` for the standard minimal parabolic `P₀` (`IsIwasawaCompact`);
- `K` is a maximal compact subgroup (`IsMaximalCompactSubgroup`);
- the parabolic part `P₀(𝔸_F) ∩ K` commutes with the positive torus of every actual algebraic Siegel setup (`IsPositiveTorusCompatible`);
- for reflection data `D`, the comparison `hρ` and every closed matrix realization `rho` in `GL_N` with `N > 0`, there is a threshold `c` such that `IsNormOneFamilyEstimate` holds for every `T` with `β(T) > c` for each simple relative root `β`.

The first three conditions are the conditions on `K` in `TruncationRapidDecayStatement`. As in the target, the finite set of operators, the order `r` and the constant `B` in the estimate are chosen after the Siegel set, the exponents `n, n₀` and the level `K₀`, and before the measure space and the family.

**Relation to the sources.** Arthur 2005, p. 24, chooses a suitable maximal compact subgroup `K = ∏_v K_v` of `G(𝔸)` with `G(𝔸) = P₀(𝔸) K`, citing Arthur 1981, p. 9, and fixes it. Proposition 13.2(b), (13.5)–(13.6), is the estimate for this fixed `K`, and its proof on p. 71 rests on Arthur 1980, Lemma 1.4, which is stated for the maximal compact subgroup `K` of `G(𝔸)` fixed in §1 of that paper (p. 89). The premise asserts that some `K` with the three listed properties satisfies the estimate. Arthur's `K` is such a subgroup. Arthur 1981, p. 9, takes `K_v` maximal compact and admissible relative to the minimal Levi subgroup `M₀`, and lists the following properties of such `K_v`: `G(F_v) = P(F_v) K_v` for the parabolic subgroups `P` containing `M₀`, and `P(F_v) ∩ K_v = (N_P(F_v) ∩ K_v)(M_P(F_v) ∩ K_v)`. A compact subgroup of `G(𝔸)` containing `K` has compact projections containing the maximal compact `K_v`, so it equals `K`. At an archimedean place `N_P(F_v)` has no nontrivial compact subgroup, so `P₀(F_v) ∩ K_v` lies in `M₀(F_v)`, which centralizes the maximal split torus and so commutes with the positive torus. The positive torus has trivial finite components. The premise does not assert the estimate for any other compact subgroup with the three properties.

The premise is asserted for every embedded atlas, and Arthur works with the Lie structure of `G(F∞)¹`. The topology of an embedded atlas is the subspace topology, and the inclusion into `G(F∞)` is an immersion. So the smooth structure is that of the embedded submanifold `G(F∞)¹ ⊂ G(F∞)`. The class `C^r` and the left-invariant operators of order at most `r` therefore do not depend on the atlas. Only the presentation of the operators by words in a tangent basis does.

## Part (a) from part (b)

Arthur 2005, p. 71: "It is enough to prove (ii), since it is a refined version of (i)." `isRapidlyDecreasing_of_isNormOneFamilyEstimate` proves this implication for a fixed atlas, compact, height and `Tp`.

Let `f` be uniformly tempered (`IsNormOneUniformlyTempered`): it satisfies `IsNormOneCr A ∞ K₀` for an open compact `K₀`, and `|X f(y)| ≤ B_X H(y)^p` for all operators `X`, with one exponent `p ≥ 0`. Here `H` is `RepresentationGrowth.adelicSourceNorm F G rho`. Fix compact factors `C` with `C.compactSubgroup = K`, `T₁` and `n`. Apply the family estimate with exponents `n + 1` and `n₀ = ⌈p⌉₊ + 1`. Take the one-point measure space `PUnit` with its Dirac measure and the constant family `f`. The fixed-level hypothesis of order `r` follows from order `∞`. Joint measurability follows from continuity of `f` (`continuous_of_isNormOneCr`).

- `exists_pos_le_adelicSourceNorm`: there is `c₀ > 0` with `c₀ ≤ H` on `G(𝔸_F)`. The scaled height `adelicHeight = N^(∑ mult) · H` is at least `1` (`one_le_adelicHeight`).
- Since `p − n₀ ≤ 0`, each term of the supremum is at most `∑_X B_X H(y)^(p−n₀) ≤ ∑_X B_X c₀^(p−n₀) = M`.
- So `H(x)^(n+1) |Λ^T f(x)| ≤ B M` on `S ∩ G(𝔸_F)¹`. With `H(x)^(-1) ≤ c₀^(-1)` this gives `|Λ^T f(x)| ≤ B M c₀^(-1) H(x)^(-n)`. That is the `IsRapidlyDecreasing` bound for the zero extension (`normOneExtend_coe`).

## The reduction

`truncationRapidDecayStatement_of_familyEstimate` takes `e` and an atlas `A` from `exists_normOneLieAtlas`, and then `K` with its three properties from the premise for `A`. For `D`, `hρ` and a closed `rho` it takes the threshold `c` of the premise. For `T` beyond `c`, part (b) is the premise, and part (a) follows from part (b) as above.
