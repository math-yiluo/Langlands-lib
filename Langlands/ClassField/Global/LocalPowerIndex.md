# Upper bounds for the indices of local `d`-th powers

This module, in namespace `Langlands.ClassField.Global`, bounds the index of the
`d`-th powers in the multiplicative group of every completion of a number field
`K`:

- for `d ≠ 0` and a finite place `v`, `(K_vˣ : K_vˣ^d) ≤ d^2 · |O_v / d O_v|`;
- for `d ≠ 0`, the index is at most `2` at a real place and `1` at a complex
  place;
- for a finite set `S` of finite places and `2 ≤ d`, the product of these indices
  over `S` and all infinite places is at most `d^(2 (|S| + |S_∞|))`, where
  `S_∞` is the set of infinite places.

These are upper bounds. The single-place bounds assume `d ≠ 0`, and the product
bound assumes `2 ≤ d`. The case `d = 0` is excluded: every unit has zeroth
power `1`, so the subgroup of `0`-th powers is trivial and has infinite index;
for example, at a complex place its index is not `1`. None of the bounds needs
roots of unity in `K`.

It imports [LocalUnitPowers](LocalUnitPowers.md), which supplies Hensel's lemma
without monicity (`exists_isRoot_of_isAdicComplete`), the binomial identity
`one_add_mul_pow_eq`, the adic completeness of `O_v`
(`isAdicComplete_adicCompletionIntegers`), the identification
`localUnitsToIntegerUnits` of valuation units with `O_vˣ`, the subgroups
`localUnitPowers v d` and `infiniteUnitPowers w d` of `d`-th powers, and the
qualitative finiteness `localUnitPowers_finiteIndex`. Through it the module
also uses `unitsExponent` and `localUnits` from
[LocalUnitCohomology](LocalUnitCohomology.md). This module proves the
quantitative bounds. Throughout, `O_v = v.adicCompletionIntegers K`, `K_v =
v.adicCompletion K`, `U_v = localUnits v` (the units of valuation one), and
`𝔪` is the maximal ideal of `O_v`.

## An index estimate (section `GroupIndex`)

- `index_range_le_relIndex_mul_card_ker f A B hAB hBA`: let `G` be a commutative
  group and `f : G →* G` an endomorphism with finite kernel. Suppose `f` maps
  the subgroup `A` onto a subgroup `B ≤ A` of finite index. Then
  `(G : f G) ≤ (A : B) · |ker f|`. The proof combines four index identities:
  `(G : f A) = (G : A ⊔ ker f) · (G : f G)` (Mathlib's `Subgroup.index_map`);
  the tower laws for `B ≤ A` and for `A ≤ A ⊔ ker f`; and
  `(A ⊔ ker f : A) = (ker f : A ∩ ker f)`, which divides `|ker f|`. The factor
  `(G : A ⊔ ker f)` is nonzero, so it cancels.

## Hensel's lemma for congruence units (section `Hensel`)

- `one_add_mul_mul_pow_eq e c w`: in any commutative ring, with `d = e + 1`,
  `(1 + d c w)^d = 1 + d^2 c (w + c (w^2 Σ_{k<e} C(d, k+2) d^k c^k w^k))`. This is
  `one_add_mul_pow_eq` applied to `z = c w`.
- `exists_one_add_mul_mul_pow_eq I d hd c hc t`: let `R` be an `I`-adically
  complete commutative ring, and let `d ≠ 0` and `c ∈ I`. Then every element
  `1 + d^2 c t` is `(1 + d c z)^d` for some `z ∈ R`. Write `d = e + 1` and
  `Q = X^2 Σ_{k<e} C(d, k+2) d^k c^k X^k`. Apply Hensel's lemma to
  `f = X + c Q - t` at `a₀ = t`. Here `f(t) = c Q(t) ∈ I`, and
  `f'(t) = 1 + c Q'(t)` is a unit modulo `I`. The root `z` satisfies
  `z + c Q(z) = t`, and `one_add_mul_mul_pow_eq` gives the claim.

## Congruence units of `O_v` (section `IntegerUnits`)

- `integerCongruenceUnits v I : Subgroup (O_v)ˣ` is the kernel of
  `(O_v)ˣ → (O_v ⧸ I)ˣ`. `mem_integerCongruenceUnits_iff` says that `x` lies in
  it if and only if `x - 1 ∈ I`.
- `finite_quotient_of_ne_bot v I hI`: if `I ≠ ⊥`, then `O_v ⧸ I` is finite.
  Indeed `I` is a power of `𝔪`, and the residue field is finite.
- `integerCongruenceUnits_finiteIndex v I hI`: hence, for `I ≠ ⊥`, the
  congruence units have finite index.
- `natCast_ne_zero_adicCompletionIntegers v d hd`: `(d : O_v) ≠ 0` for `d ≠ 0`,
  since `K` has characteristic zero.

## The filtration argument (section `CongruenceFiltration`)

Fix `d ≠ 0` and a nonzero `c ∈ 𝔪`.

- `map_pow_integerCongruenceUnits v d hd c hc`: the `d`-th power map sends
  `1 + d c O_v` onto `1 + d^2 c O_v`. The image lies in `1 + d^2 c O_v` by
  `one_add_mul_mul_pow_eq`. Conversely, `exists_one_add_mul_mul_pow_eq` with
  `I = 𝔪` writes each `y ∈ 1 + d^2 c O_v` as `(1 + d c z)^d`. Since `y` is a
  unit, so is `1 + d c z`.
- `congruenceCoeff v d c x` chooses `z` with `x = 1 + d c z`, and
  `congruenceCoeff_spec` records this equation. If `d c ≠ 0`, the map
  `congruenceCoeffHom v d c hdc : (1 + d c O_v) →* Multiplicative (O_v ⧸ d O_v)`
  sends `x` to `z mod d`. It is a homomorphism because
  `(1 + d c z)(1 + d c z') = 1 + d c (z + z' + d c z z')`.
- `finite_quotient_natCast v d hd`: `O_v ⧸ d O_v` is finite.
- `relIndex_integerCongruenceUnits_le v d hd c hc0`: the index of
  `1 + d^2 c O_v` in `1 + d c O_v` is at most `|O_v / d O_v|`. If
  `z ∈ d O_v`, then `d c z ∈ d^2 c O_v`, so the kernel of `congruenceCoeffHom`
  lies in `1 + d^2 c O_v`. The relative index is therefore at most the index of
  this kernel, which is the order of the image, at most `|O_v / d O_v|`.
- `ker_powMonoidHom_integerUnits v d`: the kernel of `x ↦ x^d` on `(O_v)ˣ` is
  `rootsOfUnity d O_v`.
- `index_integerUnitPowers_le v d hd`:
  `((O_v)ˣ : ((O_v)ˣ)^d) ≤ d · |O_v / d O_v|`.
  Let `c` be an irreducible element of the discrete valuation ring `O_v`. Apply
  `index_range_le_relIndex_mul_card_ker` with `A = 1 + d c O_v` and
  `B = 1 + d^2 c O_v`. Then use `relIndex_integerCongruenceUnits_le` and the
  bound `|μ_d(O_v)| ≤ d` (Mathlib's `card_rootsOfUnity`).

## Valuation units (section `Transfer`)

- `localUnitsToIntegerUnits_injective v` and
  `localUnitsToIntegerUnits_surjective v`: the Library's
  `localUnitsToIntegerUnits v : U_v →* (O_v)ˣ` is bijective. Units of `O_v` have
  valuation one by `adicCompletionIntegers.isUnit_iff_valued_eq_one`.
- `localUnitPowers_eq_comap v d`: `localUnitPowers v d` is the preimage of
  `((O_v)ˣ)^d` under this map.
- `index_localUnitPowers_le v d hd`: for `d ≠ 0`,
  `(U_v : U_v^d) ≤ d · |O_v / d O_v|`. This
  makes the Library's `localUnitPowers_finiteIndex` quantitative.

## Powers in the completion (section `LocalPowers`)

- `localPowers v d : Subgroup (K_v)ˣ` is the range of `x ↦ x^d` on `(K_v)ˣ`.
  `mem_localPowers_iff` unfolds membership as `∃ y, y ^ d = x`. This is the
  definition named in the submission.
- `exponentMod v d : (K_v)ˣ →* Multiplicative (ZMod d)` reduces the valuation
  exponent `unitsExponent v` modulo `d`.
- `ker_exponentMod_le v d`: its kernel lies in `K_vˣ^d ⊔ U_v`. If the exponent
  of `x` is `d k`, choose `π` of exponent `-1`
  (`exists_unitsExponent_eq_neg_one`). Then `x = (π^(-k))^d · (x π^(d k))`, and
  the second factor has exponent `0`.
- `index_sup_localUnits_le v d hd`: for `d ≠ 0`,
  `(K_vˣ : K_vˣ^d ⊔ U_v) ≤ d`, and this index
  is nonzero, because the kernel of `exponentMod` has index at most
  `|ZMod d| = d`.
- `localUnitPowers_le_subgroupOf v d`: `U_v^d ≤ K_vˣ^d ∩ U_v`.
- `index_localPowers_le_mul v d hd`: for `d ≠ 0`,
  `(K_vˣ : K_vˣ^d) ≤ d · (U_v : U_v^d)`, and
  this index is nonzero. By the tower law,
  `(K_vˣ : K_vˣ^d) = (K_vˣ^d ⊔ U_v : K_vˣ^d) · (K_vˣ : K_vˣ^d ⊔ U_v)`. The first
  factor equals `(U_v : K_vˣ^d ∩ U_v)`, which divides `(U_v : U_v^d)`.
- `localPowers_finiteIndex v d hd`: for `d ≠ 0`, `localPowers v d` has finite
  index.
- `index_localPowers_le v d hd`: for `d ≠ 0`,
  `(K_vˣ : K_vˣ^d) ≤ d^2 · |O_v / d O_v|`.

## Residue norms (section `ResidueNorm`)

- `valued_algebraMap_adicCompletion v r`, `algebraMap_integers_apply' v r` and
  `valued_algebraMap_integers v r`: the valuation on `K_v` of the image of
  `r ∈ 𝓞 K`, mapped directly or through `O_v`, is `v.intValuation r`. The
  second lemma holds by `rfl` and is used for rewriting.
- `residueIdeal v b : Ideal (𝓞 K)` is the preimage of `b O_v`. By
  `mem_residueIdeal_iff`, `r` lies in it if and only if
  `v.intValuation r ≤ v.intValuation b`. By `residueIdeal_eq_pow`, for `b ≠ 0`
  it equals `v ^ m`, where `m` is the multiplicity of `v` in `(b)`.
- `exists_valued_sub_lt v x b hb`: for `b ≠ 0`, every `x ∈ O_v` is congruent
  modulo `b` to an algebraic integer. First approximate `x` by `y ∈ K`, using
  the density of `K` in `K_v`; the ultrametric inequality gives `v(y) ≤ 1`.
  Then approximate `y` by an element of `𝓞 K`, using Mathlib's
  `exists_valuation_sub_lt_of_integer`.
- `algebraMap_quotient_surjective v b hb`: for `b ≠ 0`, the map
  `𝓞 K → O_v ⧸ b O_v` is surjective. Its kernel is `residueIdeal v b`.
- `card_quotient_eq_absNorm v b hb`: for `b ≠ 0`,
  `|O_v / b O_v| = N(residueIdeal v b)`, the absolute norm.
- `prod_card_quotient_le S b hb`: for `b ≠ 0`,
  `∏_{v ∈ S} |O_v / b O_v| ≤ |N_{K/ℚ}(b)|`. The ideals `v ^ m_v` are pairwise
  coprime (Mathlib's `isCoprime_pow_of_ne`), so their product is their
  intersection. This intersection contains `(b)`, and
  the absolute norm of `(b)` is `|N_{K/ℚ}(b)|`.
- `prod_card_quotient_natCast_le S d hd`: for `d ≠ 0`,
  `∏_{v ∈ S} |O_v / d O_v| ≤ d^[K : ℚ]`, since `N_{K/ℚ}(d) = d^[K : ℚ]`.

## Infinite places (section `Infinite`)

For an infinite place `w`, `infiniteUnitPowers w d` is the Library's subgroup of
`d`-th powers of units of `w.Completion`.

- `infiniteUnitPowers_eq_top_of_isComplex w hw d hd`: for `d ≠ 0`, at a complex
  place every unit is a `d`-th power. The proof transfers along Mathlib's
  `ringEquivComplexOfIsComplex` and uses that `ℂ` is algebraically closed.
- `index_infiniteUnitPowers_le_two w hw d hd`: for `d ≠ 0`, at a real place the
  index is at most `2`. Along `ringEquivRealOfIsReal`, every positive real
  number `t` is the `d`-th power of `t^(1/d)`. For every unit `x`, one of `x`
  and `-x` is positive. So the quotient is the image of `{1, -1}`.
- `index_infiniteUnitPowers_le_ite w d hd`: for `2 ≤ d`, the index is at most
  `d` at a real place and `1` at a complex place.
- `prod_index_infiniteUnitPowers_le d hd`: for `2 ≤ d`, the product over all
  infinite places is at most `d^r₁`, where `r₁` is the number of real places.

## The product bound (section `Product`)

- `prod_index_localPowers_le S d hd`: for a finite set `S` of finite places and
  `2 ≤ d`,
  `(∏_{v ∈ S} (K_vˣ : K_vˣ^d)) · ∏_w (K_wˣ : K_wˣ^d) ≤ d^(2 (|S| + |S_∞|))`.
  The finite places contribute at most `d^(2|S|) · d^[K : ℚ]`, and the infinite
  places at most `d^r₁`. Since `[K : ℚ] = r₁ + 2 r₂` and `|S_∞| = r₁ + r₂`, the
  exponent is `2|S| + 2 r₁ + 2 r₂`.

## Provenance

Artin–Tate, *Class Field Theory*, Preliminaries §3, printed p. 7, compute
`(k* : k*^n) = n / |n|_k · (k*_n : 1)` for a local field `k`, using the
Herbrand quotient and the isomorphism `U_i ≅ U_{i+m}` given by `x ↦ x^n` for
large `i`. If `k` contains the `n`-th roots of unity, this gives `n^2 / |n|_k`,
and archimedean fields satisfy the same formulas. Chapter VI §3, printed p. 26,
uses the product formula to obtain `∏_{p ∈ S} (k_p : k_p^n) = n^(2s)` when `S`
contains the places above `n` and `∞`.

The Lean proof differs from Artin–Tate. It proves only upper bounds, which hold
without roots of unity. It does not use the Herbrand quotient: it uses the
explicit pair of congruence subgroups `1 + d c O_v ⊇ 1 + d^2 c O_v` and the
index estimate of section `GroupIndex`. Instead of the product formula, it
bounds `∏ |O_v / d O_v|` by the absolute norm `d^[K : ℚ]`. The Hensel step
reuses the non-monic Hensel lemma of [LocalUnitPowers](LocalUnitPowers.md).
