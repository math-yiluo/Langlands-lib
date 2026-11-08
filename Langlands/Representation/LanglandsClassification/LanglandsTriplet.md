# Coroot chambers and Langlands triplets

Author: Worker 6. Module `Langlands.Representation.LanglandsClassification.LanglandsTriplet`. The chambers are in namespace `Langlands.GroupScheme`; the unramified characters, their real parts and the triplet predicate are in `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The module uses:

- V.3.14–V.3.15, printed p.113 / PDF p.119: the sets `Δ(P)`, the projected coroots `β̌`, and the open and closed chambers `^G_P[𝔞*]^+` and its closure;
- V.3.20, printed pp.115–116 / PDF pp.121–122: the unramified characters `X(M)` and the real part `ℜ(ψ) ∈ 𝔞*_M`;
- VII.4.1, Definition, printed p.241 / PDF p.247: Langlands triplets.

This is a definition unit. Its only theorem is that the open chamber is contained in the closed one. It asserts nothing from the VII.4.1 Lemma (`PP̄`-regularity of `σ ⊗ ψ`) or from the VII.4.2 classification theorem.

## Coroot chambers (`Langlands.GroupScheme`)

The data are a field `k`, a group scheme `G` over `Spec k` with `[IsAffineHom G.X.hom]`, commutative group schemes `A` and `T`, a map `i : T.toGrp ⟶ G` with `[Mono i.hom.hom.left]`, a cocharacter `ν : cocharacterLattice T`, a set `J : Set (characterLattice T)`, a map `f : A ⟶ T`, and integral reflection data `D : RelativeRootReflectionData i`. In the intended use `i` is a maximal split torus `A_∅ ⊂ G`, `ν` is a generic cocharacter defining the minimal parabolic `P_∅`, `J ⊆ Δ_∅` is the set `Δ^M_∅` of simple roots of a standard Levi `M`, and `f` is the inclusion `A_M ⊂ A_∅`. None of this is assumed by the chamber definitions; `IsLanglandsTriplet` below imposes it.

The published `RelativeRootReflectionData i` supplies, for every relative root `α` (an element of `relativeRoots i`), a cocharacter `D.coroot α` with `⟨α, D.coroot α⟩ = 2`, together with a normalizer point acting on characters by `χ ↦ χ - ⟨χ, D.coroot α⟩ α`. These are the coroots `α̌` of the source. The pairing of the real spaces is `RealTorusSpace.pair`, and `simpleRelativeRoots i ν` is the published set of simple roots for the positive system defined by `ν`.

- `restrictedCorootChamber i ν J f D : Set (Vstar A)` is the set of `x` in the real character space `Vstar A = ℝ ⊗ X^*(A)` for which there is `y : Vstar T` with
  1. `rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y = x` (`y` restricts to `x` along `f`),
  2. `⟨y, α̌⟩ = 0` for every relative root `α ∈ J`, and
  3. `⟨y, α̌⟩ > 0` for every simple root `α ∉ J`.
- `restrictedClosedCorootChamber i ν J f D` is the same set with `⟨y, α̌⟩ ≥ 0` in condition 3.
- `restrictedCorootChamber_subset_closed` proves the inclusion: the same witness `y` works, with strict inequalities weakened.

### Comparison with the source

Renard defines `^G_P[𝔞*_M]^+ = {χ ∈ 𝔞*_M | ⟨χ, β̌⟩ > 0, β ∈ Δ(P)}`, where `Δ(P)` consists of the restrictions to `𝔞_M` of the simple roots `α ∈ Δ_∅ \ Δ^M_∅`, and `β̌` is the projection to `𝔞_M` of the coroot `α̌`. The closed chamber uses `≥ 0`.

The Lean definition avoids the projection by lifting to `𝔞*_∅`. The reason it describes the same set is the following, which is not formalized. Renard V.3.13 (printed p.112 / PDF p.118) embeds `𝔞*_M` in `𝔞*_∅` as the subspace orthogonal to the coroots `α̌`, `α ∈ Δ^M_∅`, and gives `𝔞_∅ = 𝔞_M ⊕ 𝔞^M_∅`, where `𝔞^M_∅` is spanned by these coroots (V.3.13 applied to `M`). Restriction `𝔞*_∅ → 𝔞*_M` along `𝔞_M ⊂ 𝔞_∅` therefore maps this orthogonal subspace isomorphically onto `𝔞*_M`. For `x ∈ 𝔞*_M`, condition 1 together with condition 2 singles out the unique such lift `y`, and for that `y`, `⟨y, α̌⟩ = ⟨x, β̌⟩` since `y` vanishes on the `𝔞^M_∅`-component of `α̌`. Conditions 1–3 thus say `⟨x, β̌⟩ > 0` for every `β ∈ Δ(P)`.

The coroots come from the supplied data `D`. When the Weyl group is finite, the coroot of a root is determined by the reflection condition. That uniqueness is not formalized here, so the chambers are defined relative to `D`.

## Unramified characters and real parts (`Langlands.Aubert.General.RepresentedParabolic`)

Here `k` is a nonarchimedean local field (`[ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`), `l : M ⟶ P` has `hl : IsRationalLeviSubgroup l`, and `rationalPoints M` carries the published Levi topology `leviPointTopology l hl`.

- `leviUnramifiedCharacters l hl` is the published `Plancherel.unramifiedCharacters` for the family of norms `|χ|_F` of all rational characters `χ` of `M` (`Plancherel.rationalNormCharacters M`). Its elements are the continuous characters `M(F) → ℂˣ` that are trivial on the common kernel `^0M` of these norms. This is Renard's `X(M) = Hom(M/^0M, ℂˣ)`.
- `leviUnramifiedRealPart l hl a ha ψ`, for `a : A.toGrp ⟶ M` with `ha : IsSplitComponent a`, is `Plancherel.SplitTorus.normalizedRealPart` of the restriction `ψ ∘ a` of `ψ` to `A(F)`. It is an element of `Vstar A`.

Renard defines `ℜ(ψ) ∈ 𝔞*_M = X^*(M) ⊗ ℝ` by lifting `ψ` through the surjection `X^*(M) ⊗ ℂ → X(M)`, `χ ⊗ s ↦ |χ|_F^s`, and taking the real part. The Lean definition instead records the real part of the restriction of `ψ` to the split component `A_M`, in `X^*(A_M) ⊗ ℝ`. These agree through the restriction isomorphism `X^*(M) ⊗ ℝ ≅ X^*(A_M) ⊗ ℝ` of V.3.19 (equal-rank lattices), since `|χ|_F^s` restricts to `|χ|_{A_M}|_F^s`. That identification is not formalized.

The parameter is the published normalized one, in which `|χ|_F^s` has real part `Re(s) χ` (the `q^(-s)` lift of V.3.20). V.3.20 also writes `ℜ(χ) = ln |χ|`, which under the fixed valuation differs by the negative factor `-ln q`. The published `ArbitraryParabolicTempered` Markdown records this discrepancy. The module uses only the normalized parameter, the same one as the published temperedness predicate. With it, for `GL_2` and the upper triangular Borel subgroup `B`, `δ_B^{1/2}` has real part half the positive root, which lies in the open chamber; the trivial representation is the unique irreducible quotient of `i_B^G(δ_B^{1/2})`, as the classification requires.

The twist `σ ⊗ ψ` of the source is the published `SmoothRep.twist` with the open-kernel lemma `Plancherel.unramifiedCharacter_isOpen_ker`, as in the published `RenardGenericIrreducibilityStatements`. This module does not define a separate twist.

## Langlands triplets (VII.4.1, Definition)

The ambient rational points carry the canonical topology `RationalPointFamily.pointTopology` (local instance `tripletAmbientPointTopology`), with `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`. `IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ` takes

- `i : T.toGrp ⟶ G`, `ν`, and reflection data `D`, fixing the minimal parabolic;
- `p : P ⟶ G`, `l : M ⟶ P`, `a : A.toGrp ⟶ M` with `hp : IsParabolicSubgroup p`, `hl : IsRationalLeviSubgroup l`, `ha : IsSplitComponent a`;
- the simple-root index `J` and the factor `f : A ⟶ T`;
- `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` and `ψ : leviUnramifiedCharacters l hl`.

It is the conjunction of:

1. `(⟨T, i, ν, J, f⟩ : ParabolicRootPresentationData A G).IsCompatible p l a`. This published predicate says that `i` is a maximal split torus, `ν` is generic with minimal parabolic `P_∅` contained in `P`, `J` is a set of simple roots, `P` is the standard parabolic and `M` the standard Levi of `J`, and `f` is the factor of the split component through `T`. This is Renard's "`P = MN` is a standard parabolic subgroup".
2. `σ.IsIrreducible`.
3. `IsNormalizedExponentTempered hl.isConnectedReductive σ`, the published temperedness predicate (VII.2.1, normalized-exponent formulation) for `M`. It uses the Levi topology together with the published instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`.
4. `leviUnramifiedRealPart l hl a ha ψ ∈ restrictedCorootChamber i ν J f D`: Renard's `ℜ(ψ) ∈ ^G_P[𝔞*_M]^+`.

Renard's triplet carries the representation `(σ, E)` itself. In Lean the carrier is part of `σ`, in an independent universe `v`; there is no finite-dimensionality or other carrier restriction. The temperedness predicate includes admissibility, as in the published definition.

## Scope

The VII.4.1 Lemma (`σ ⊗ ψ` is `PP̄`-regular, giving an intertwining operator `J_{P̄|P}` unique up to scalar) and Theorem VII.4.2 (existence and uniqueness of the Langlands quotient) are later statement units. Independence of the chamber from the reflection data, the identification of the Lean real part with `ℜ` on `𝔞*_M`, and the decomposition `𝔞*_∅ = 𝔞*_M ⊕ (𝔞^M_∅)*` are not formalized.
