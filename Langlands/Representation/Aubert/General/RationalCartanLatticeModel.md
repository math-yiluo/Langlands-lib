# The lattice model of the Cartan elements of `G(F)`

Module `Langlands.Representation.Aubert.General.RationalCartanLatticeModel`.

This module checks the eight fields of the abstract
`Langlands.Aubert.General.IsCartanLatticeModel` (module
`Langlands.Representation.Aubert.General.CartanLatticeContraction`) for the
rational points `G(F)` of an affine group scheme over a nonarchimedean local
field `F`. Combined with `IsCartanLatticeModel.hasWallContraction`, this gives
the wall contraction field of a standard parabolic system for `G(F)`.

The Cartan sets are the dominant representatives `C̃⁺ = C₀ F₀ ∩ Z_dom` of
D. Renard, *Représentations des groupes réductifs p-adiques* (French version
dated 9 July 2026, source id
`renard-2026-representations-groupes-reductifs-padiques`), V.5.1, with the
notation of V.3.23. The `contracts` field is derived from Renard V.5.2 (iii)
(printed p. 123), in the form packaged by the Library predicate
`Langlands.BruhatTits.SpecialCompact.SimultaneousStandardBasisAt`. The
derivation is internal to this module and is not taken from the literature.

## Setting

`F` is a nonarchimedean local field with residue cardinality `q`. `G` and `Z`
are group schemes over `F` with `G` affine over the base. `i : S → G` is a
morphism from a split torus `S` and `ν` is a cocharacter of `S`. `j : Z → G`
and `s : S → Z` are morphisms, and `h` is the bijectivity of the
restriction-evaluation map of `s`; `h` defines the centralizer valuation
`centralizerValuation s h : Z(F) → V(S)` used for dominance. `ϖ` is the
order-one uniformizer fixed in the Library, and `⟨β, x⟩` is the integer pairing
of a character `β` with a cocharacter `x`. `SimpleRoot i ν` is the type of
simple relative roots, `rootSet i ν I` is the set of characters in
`I : Finset (SimpleRoot i ν)`, and `levi i ν I` and `unipotent i ν I` are the
standard Levi `M_I` and unipotent radical `N_I` of
`Langlands.Representation.Aubert.General.RationalPointFamily`.

## Definitions

- `uniformizerPowers i : Multiplicative X_*(S) →* G(F)` is `x ↦ ϖ^x = i(x(ϖ))`,
  the uniformizer section `Plancherel.RenardCartan.uniformizerSection S`
  followed by `rationalPoints.map i`.
- `simpleRootPairing i ν β : X_*(S) →+ ℤ` is `x ↦ ⟨β, x⟩` for a simple root `β`.
- `rationalCartanSet i ν j s h F₀ I` is the image under `j` of
  `Plancherel.RenardCartan.tildeC0Plus s F₀ (dominantCentralizer ...)`. Here
  `tildeC0Plus s F₀ D = (C₀ · F₀) ∩ D`, where `C₀ ⊆ Z(F)` is the image of `S`'s
  uniformizer section under `s`, and the dominance set is the
  `dominantCentralizer` of the torus factor `Standard.leviTorusHom i ν (rootSet i ν I)`
  of the standard Levi scheme for `rootSet i ν I`. A point `z` is dominant when
  `α(centralizerValuation s h z) ≥ 0` for every positive relative root `α` of
  that Levi for `ν`. These are Renard's representatives `C̃⁺` for `M_I`.

## Theorems

- `characterNorm_latticeSection A α c`: for a split torus `A` over `F`, a
  character `α` and a cocharacter `c`, the normalized norm of `α` at `c(ϖ)` is
  `q^{-⟨α, c⟩}`.
- `exists_residueCardinality_zpow_lt`: for `ε > 0` there is an integer `L` with
  `q^{-p} < ε` for every integer `p ≥ L`.
- `latticePairing_componentCharacterRestriction q β c`: for `q : A → S`, the
  restriction of `β` along `q` pairs with `c` as `β` pairs with `q ∘ c`.
- `simpleRootPairing_apply` (simp): the unfolding of `simpleRootPairing`.
- `uniformizerPowers_mem_levi I x`: `ϖ^x ∈ M_I`.
- `commute_uniformizerPowers hfinite I hexists x hx m hm`: if the simple roots
  are finite, `rootSet i ν I` has a standard cocharacter, `⟨β, x⟩ = 0` for
  `β ∈ I`, and `m ∈ M_I`, then `m ϖ^x = ϖ^x m`.
- `mem_positiveRelativeRoots_leviTorusHom hJ hβ` (for `G` locally of finite
  type over the base): if `J` is a set of simple roots and `β ∈ J`, then `β`
  is a positive relative root of the torus factor of the standard Levi scheme
  for `J`.
- `map_mem_levi_of_isRepresentedBy hrep I f`: if `j` represents the torus
  centralizer of `i`, then `j(f) ∈ M_I` for every `f ∈ Z(F)`.
- `exists_rep_rationalCartanSet hsj hval hF0 I` (for `G` locally of finite type
  over the base): assume `s ≫ j = i`, the valuation formula
  `hval : centralizerValuation s h (s(c(ϖ))) = 1 ⊗ c` for every cocharacter `c`,
  and `F₀` finite. Then there is an integer `B` such that every
  `t ∈ rationalCartanSet i ν j s h F₀ I` equals `ϖ^x · j(f)` with `f ∈ F₀` and
  `⟨β, x⟩ ≥ -B` for all `β ∈ I`.
- `uniformizerPowers_conj_mem hi hfinite hexists hbasis J u hu`: assume `i` is a
  maximal split torus, the simple roots are finite, every `rootSet i ν I` has a
  standard cocharacter, and `SimultaneousStandardBasisAt i ν K₀` holds for a
  subgroup `K₀ ⊆ G(F)`. Let `u ∈ N_J`. Then for every neighbourhood `O` of `1`
  in `G(F)` (rational-point topology) there is an integer `L` such that
  `ϖ^y u ϖ^{-y} ∈ O` for every `y` with `⟨β, y⟩ = 0` for `β ∈ J` and
  `⟨β, y⟩ ≥ L` for all simple `β ∉ J`.
- `isCartanLatticeModel_rational` (for `G` locally of finite type over the
  base): under the hypotheses `hi`, `hfinite`, `hexists`, `hrep`, `hsj`, `hval`,
  `hbasis` above and `F₀` finite,
  `IsCartanLatticeModel (levi i ν) (unipotent i ν) (rationalCartanSet i ν j s h F₀)
  (uniformizerPowers i) (simpleRootPairing i ν) (j '' F₀)` holds in the
  rational-point topology of `G(F)`.

## Proofs

`characterNorm_latticeSection`: unfold the norm character to the normalized
absolute value of `α(c(ϖ)) ∈ Fˣ`. The composite `c ≫ α` is the
`⟨α, c⟩`-th power endomorphism of `𝔾_m` (`eq_gmEndEquiv_zsmul`), so the value is
`ϖ^{⟨α, c⟩}`, whose normalized absolute value is `q^{-⟨α, c⟩}`.

`exists_residueCardinality_zpow_lt`: since `q > 1`, some power `(q⁻¹)^n` is
below `ε`; take `L = n` and use monotonicity of `p ↦ q^{-p}`.

`latticePairing_componentCharacterRestriction` and `simpleRootPairing_apply`
hold by definition.

`uniformizerPowers_mem_levi`: `ϖ^x` is a point of the torus `i(S)`, and the
torus points lie in every standard Levi (`torusPoints_le_levi`).

`commute_uniformizerPowers`: under the finiteness and standard-cocharacter
hypotheses the standard Levi for `rootSet i ν I` equals the common centralizer
of the cocharacters annihilating `rootSet i ν I`
(`standardLevi_eq_cocharacterAnnihilatorCentralizer`). Since `x` annihilates
it, `m` lies in the dynamic centralizer of `i ∘ x`, which is the torus
centralizer of `i ∘ x` (`torusCentralizer_gm_eq_dynamicCentralizer`).
Evaluating that centralizer condition at the point `ϖ ∈ 𝔾_m(F)` gives
`m ϖ^x = ϖ^x m`.

`mem_positiveRelativeRoots_leviTorusHom`: a selected simple root is a relative
root of the Levi torus factor (`selectedRoots_subset_relativeRoots_standardLeviTorusFactor`,
using the proved `dynamicLie`), and it is positive for `ν` because simple roots
are positive (`simpleRelativeRoots_subset_positive`).

`map_mem_levi_of_isRepresentedBy`: `j(f)` is in the range of `j`, which is the
torus centralizer by `hrep`, and the centralizer points lie in every standard
Levi (`centralizerPoints_le_levi`).

`exists_rep_rationalCartanSet`: let `b` be an upper bound of the finite set of
values `β(centralizerValuation s h f)` with `β ∈ I` and `f ∈ F₀`, and take
`B = ⌈b⌉`. An element of the Cartan set is `j(z)` with `z = s(x(ϖ)) · f`,
`f ∈ F₀` (`mem_tildeC0`, `mem_C0`), and `z` dominant. Then
`j(z) = ϖ^x · j(f)` by `s ≫ j = i`. For `β ∈ I`, `β` is a positive root of the
Levi (`mem_positiveRelativeRoots_leviTorusHom`), so dominance and `hval` give
`0 ≤ ⟨β, x⟩ + β(centralizerValuation s h f) ≤ ⟨β, x⟩ + b`, hence
`⟨β, x⟩ ≥ -⌈b⌉`.

`uniformizerPowers_conj_mem`: unpack `hbasis` into a basis `𝓑` of
compact open normal subgroups at `1` and, for `rootSet i ν J`, a compatible
standard split component `q : A → S` with Levi representative `jM : M → G`,
split component `a : A → M` and basis-member clauses for every `K ∈ 𝓑`.
Choose `K ∈ 𝓑` with `K ⊆ O`. The uniform compact containment clause of
`K`'s basis-member property, applied to the compact set `{u} ⊆ N_J`, gives
`ε > 0` such that `u ∈ m⁻¹ (K ∩ N_J) m` for every `m` in the epsilon chamber
`standardComponentCAepsilon i ν (rootSet i ν J) q ε`. Choose `L` with
`q^{-p} < ε` for `p ≥ L`. Let `y` be as in the statement.

1. `y` comes from `A`: `y` annihilates `rootSet i ν J`, so `i ∘ y` is central
   in the Levi torus factor `t` (`isCentral_standardLeviTorusFactor_of_annihilates`).
   The torus factor composed with `q` is `a` (checked after the monomorphism
   `jM`), `t` is a monomorphism because it is a maximal split torus of `M`
   (`isMaximalSplitTorus_standardLeviTorusFactor`), and so the central
   cocharacters of `t` are the images of the cocharacters of `A`
   (`IsSplitComponent.range_cocharacterMapInt_eq_centralCocharacters`). Write
   `y = q ∘ c`.
2. `ϖ^y` lies in the epsilon chamber: it is the image of `c(ϖ) ∈ C_A` under
   `q ≫ i` (`uniformizerSection_naturality`), and for a simple `β ∉ J` the
   restriction of `β` to `A` has norm
   `q^{-⟨β|_A, c⟩} = q^{-⟨β, y⟩} < ε` at `c(ϖ)`, by
   `characterNorm_latticeSection` and `⟨β, y⟩ ≥ L`.
3. Hence `u = ϖ^{-y} k ϖ^y` for some `k ∈ K ∩ N_J`, so
   `ϖ^y u ϖ^{-y} = k ∈ K ⊆ O`.

`isCartanLatticeModel_rational`: the fields are, in order: `F₀` finite gives
`j '' F₀` finite; `exists_rep` is `exists_rep_rationalCartanSet`; `e_mem_levi`
is `uniformizerPowers_mem_levi`; `F₀_subset_levi` is
`map_mem_levi_of_isRepresentedBy`; `levi_le_normalizer` is
`RationalPointFamily.levi_le_normalizer`; `commute_of_pair_eq_zero` is
`commute_uniformizerPowers`; `exists_standard` is a standard cocharacter of
`rootSet i ν I` from `hexists`, rewritten for the finite index set `I`; and
`contracts` is `uniformizerPowers_conj_mem`.
