# Finite Haar measure of Siegel sets and reductive finite volume

Author: Worker 1179. The good-position hypothesis below was agreed with Worker 235.

This module does five things:

1. It proves a general covolume criterion for a discrete subgroup of a locally compact
   group.
2. It defines the predicate `IsPositiveTorusCompatible`: every element of the compact
   subgroup `K` that lies in the canonical standard parabolic `P(𝔸_F)` commutes with the
   positive torus `A_{T₀}`.
3. It states, without proving it, that the actual adelic Siegel sets of the Library have
   finite Haar measure in the norm-one group when `K` is compatible in this sense
   (`SiegelProductFiniteMeasureStatement`).
4. It states, without proving it, the good-position form of Siegel reduction
   (`AdelicGoodSiegelReductionStatement`), and proves that it implies the Library target
   `AdelicSiegelReductionStatement`.
5. It proves that the two new statements together give finite volume of the actual
   norm-one rational quotient of every connected reductive group over a number field,
   both for one group at a time and as the Library target
   `ConnectedReductiveFiniteVolumeStatement`.

The module does not prove finite volume outright. Its two inputs,
`AdelicGoodSiegelReductionStatement` and `SiegelProductFiniteMeasureStatement`, are both
unproved.

## Covolume criterion

`LeftCosetSpace.isFiniteMeasure_haarQuotientMeasure_of_measure_lt_top` works in a
second-countable, locally compact topological group `H` with its Borel structure. Let `Λ`
be a discrete subgroup and let `S ⊆ H` be any set, not necessarily measurable, with
`Measure.haar S < ∞`. Suppose every `g : H` has some `γ ∈ Λ` with `γ * g ∈ S`. Then the
Library's quotient measure `haarQuotientMeasure Λ hΛ` on the left coset space `Λ \ H` is
a finite measure.

## Common data

All three new definitions use the following data, all in universe `u`:

- a number field `F`;
- an affine group scheme `G` over `Spec F` that is locally of finite type and connected
  reductive (`IsConnectedReductive G`);
- the data `T, i, ν, T₀, j` of an actual algebraic Siegel setup, so that
  `IsSiegelAlgebraicSetup F G T i ν T₀ j` holds. This is the Library predicate of
  `AdelicSiegelReductionStatement.md`: `i : T → G` is a maximal split torus, `ν` is a
  generic cocharacter, the canonical standard parabolic `P = Standard.parabolicScheme i ν ∅`
  is a minimal parabolic with Levi `M = Standard.leviScheme i ν ∅`, which is the
  centralizer of `T`, and unipotent radical `N = Standard.unipotentScheme i ν ∅`, and
  `j ≫ i` maps `T₀` onto a maximal split torus of the derived group;
- compact factor data `C : CompactFactors F G N M`. This is a compact set
  `Ω_N ⊆ N(𝔸_F)`, a compact set `Ω_M ⊆ M(𝔸_F)¹` and a compact subgroup `K` of `G(𝔸_F)`;
- a threshold `t : ℝ≥0ˣ`.

`A_{T₀}` denotes the Library's intrinsic positive subgroup
`PositiveRealTorus.intrinsicSubgroup F T₀` of `T₀(𝔸_F)`, and
`positiveMap F G T i T₀ j : A_{T₀} → G(𝔸_F)` is the continuous homomorphism induced by
`j ≫ i`. The weak Siegel product

  `weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t`

is the ordered set `Ω_N Ω_M A_{T₀}(t) K` of `AdelicSiegelReductionStatement`. Here
`A_{T₀}(t)` is the image under `positiveMap` of the points `a ∈ A_{T₀}` with
`t ≤ |α(a)|` for every simple relative root `α`, where `|·|` is the normalized idelic norm.

## The compatibility predicate

`AdelicSiegelFactors.IsPositiveTorusCompatible F G T i ν T₀ j K` is a definition returning
`Prop`, for a subgroup `K` of `G(𝔸_F)`. It says: for every `k ∈ K` that lies in the range of
the map `P(𝔸_F) → G(𝔸_F)` induced by `Standard.parabolicHom i ν ∅`, and for every
`a ∈ A_{T₀}`, the elements `k` and `positiveMap F G T i T₀ j a` commute. In words, the
parabolic part `P(𝔸_F) ∩ K` of `K` commutes with the actual positive torus.

## The Siegel-set statement

`AdelicSiegelFactors.SiegelProductFiniteMeasureStatement` is a definition returning
`Prop`. It quantifies over the common data above. It assumes

- `IsParabolicIwasawaCompact F G P (Standard.parabolicHom i ν ∅) K`, that is, `K` is a
  maximal compact subgroup of `G(𝔸_F)` and `P(𝔸_F) K = G(𝔸_F)`, with `P(𝔸_F)` on the left;
- `IsPositiveTorusCompatible F G T i ν T₀ j K`.

The conclusion is that the left Haar measure `Measure.haar` of the norm-one subgroup
`normOneSubgroup F G = G(𝔸_F)¹` gives finite outer measure to the preimage under the
inclusion `G(𝔸_F)¹ → G(𝔸_F)` of the weak Siegel product above. This is the same set that
`AdelicSiegelReductionStatement` uses, and the same `Measure.haar` from which
`normOneRationalQuotientHaarMeasure` is built. The statement does not change the measure
or the set.

## The good-position reduction statement

`AdelicSiegelFactors.AdelicGoodSiegelReductionStatement` is a definition returning `Prop`.
It has the same shape as the Library target `AdelicSiegelReductionStatement`. For every
number field `F` and every affine, locally finite type, connected reductive group scheme
`G` over `Spec F`, it asserts that there exist `T, i, ν, T₀, j` with
`IsSiegelAlgebraicSetup F G T i ν T₀ j`, compact factor data `C` and a threshold `t` such
that

- `IsSiegelCover F G T i ν T₀ j C t` holds. This is the Library predicate: `K` satisfies
  `IsParabolicIwasawaCompact` for `P`, and `G(F) · weakSiegelProduct = G(𝔸_F)¹` as subsets
  of `G(𝔸_F)`;
- and `IsPositiveTorusCompatible F G T i ν T₀ j K` holds for `K = C.compactSubgroup`.

The only difference from `AdelicSiegelReductionStatement` is the second item.

## The reduction theorems

`AdelicSiegelFactors.adelicSiegelReductionStatement_of_good` proves
`AdelicGoodSiegelReductionStatement → AdelicSiegelReductionStatement` (same universe `u`).

`AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_siegel` takes
proofs of `AdelicGoodSiegelReductionStatement` and `SiegelProductFiniteMeasureStatement`
(same universe `u`), a number field `F` and a group scheme `G` over `Spec F` with
`IsAffine G.X.left`, locally of finite type and connected reductive. It concludes
`IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G)`.

`AdelicSiegelFactors.connectedReductiveFiniteVolumeStatement_of_siegel` takes the same two
proofs and concludes the Library target
`AdelicGroupPoints.ConnectedReductiveFiniteVolumeStatement` (module
`Langlands.Global.AdelicReductiveFiniteVolumeStatement`) in the same universe.

## Sources and provenance

The compatibility predicate, the Siegel-set statement and the good-position reduction
statement are derived. No single cited passage states them in this form. The covolume
criterion and the three reduction theorems are internal to this module.

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §2.7, printed
  pp. 71–72 (PDF pp. 88–89 counting from 1), registered source
  `getz-hahn-2024-automorphic-representations`, SHA256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. Theorem 2.7.1 is the
  Iwasawa decomposition `G(𝔸_F) = P(𝔸_F) K` with `K` maximal compact. Definitions (2.25)
  and (2.26) define the Siegel set `S(t) = Ω_N Ω_M A_{T₀}(t) K`. Theorem 2.7.2 is the
  reduction statement `G(F) S(t) = G(𝔸_F)¹`. Getz–Hahn do not state that Siegel sets have
  finite measure.
- Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), registered
  source `moeglin-waldspurger-1995-spectral-decomposition` (folder SHA256
  `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
  - I.1.4, printed p. 4 (chapter file `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`,
    PDF page 4). The maximal compact subgroup `K = ∏_v K_v` of I.1.1 can be chosen with
    (i) `G(𝔸) = P₀(𝔸) K`, and (ii) `P(𝔸) ∩ K = (M(𝔸) ∩ K)(U(𝔸) ∩ K)` for every standard
    parabolic `P = MU`.
  - I.1.13, printed p. 18 (chapter file
    `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, PDF page 1). For this `K`,
    `f ↦ ∫_{U₀(𝔸) × M₀ × K} f(umk) m^{-2ρ₀} dk dm du` is a Haar measure on `G(𝔸)`, where
    `ρ₀` is the half-sum of the positive roots of the minimal parabolic `P₀ = M₀U₀`.
  - I.2.1, printed pp. 18–20 (same chapter file, PDF pages 1–3). Siegel domains
    `S = ω A_{M₀}(t₀) K` for that `K`, the reduction `G(k) S = G`, and, for number fields,
    the decompositions `M = A_M M¹` and `A_M = A_G ⊕ A_M^G` (printed p. 19).

**Compatibility.** Mœglin–Waldspurger's condition (ii) for `P₀` implies
`IsPositiveTorusCompatible`. Let `k ∈ P(𝔸_F) ∩ K` and write `k = m u` with
`m ∈ M(𝔸_F) ∩ K` and `u ∈ N(𝔸_F) ∩ K`. The image of `positiveMap` lies in `T(𝔸_F)`, and `T`
is central in its centralizer `M`, so `m` commutes with it. The group `N(𝔸_F) ∩ K` is a
compact subgroup of `N(𝔸_F)`. Its projection to the archimedean factor `N(F ⊗ ℝ)` is a
compact subgroup of a real unipotent group, hence trivial. The image of `positiveMap` is
trivial at the finite places, because every character of a point of `A_{T₀}` is a positive
real number placed at the archimedean places and `1` at the finite places, and `T₀` is
split. So `u` and `positiveMap a` live in complementary factors of
`G(𝔸_F) = G(F ⊗ ℝ) × G(𝔸_{F,f})` and commute.

**Good-position reduction.** Choose `K` as in Mœglin–Waldspurger I.1.4 for the minimal
parabolic `P` of the setup. It is maximal compact, satisfies `P(𝔸_F) K = G(𝔸_F)`, and is
compatible by the previous paragraph. Getz–Hahn Theorem 2.7.2 applies to any such `K` and
gives the covering `G(F) S(t) = G(𝔸_F)¹` for suitable `Ω_N`, `Ω_M` and `t`. This is the
same reduction as in `AdelicSiegelReductionStatement.md`, with this particular `K`.
Mœglin–Waldspurger I.2.1 states the analogous reduction for this `K` in `G(𝔸)`.

**Finite measure.** The derivation below is the standard one. It is not formalized here.
Write `P = P(𝔸_F)`, `N = N(𝔸_F)`, `M = M(𝔸_F)`, `L = P ∩ K`, and let `A(t)` be the image
of the chamber `A_{T₀}(t)` in `G(𝔸_F)`. Let `S = Ω_N Ω_M A(t) K`.

1. *Haar measure.* `G` is reductive, hence `G(𝔸_F)` is unimodular, and `K` is compact
   with `P K = G(𝔸_F)`. Then the push-forward of `δ(m)⁻¹ dn dm dk` under
   `Φ(n, m, k) = n m k` is a Haar measure of `G(𝔸_F)`. Mœglin–Waldspurger I.1.13 state
   this for their `K`. The standard proof, by uniqueness of a measure on `G(𝔸_F)` that is
   left `P`-invariant and right `K`-invariant, uses only these two properties of `K`. Here
   `δ(m) = |χ_N(m)|` is the modulus of conjugation by `m` on `N`, and
   `χ_N = det Ad|_{Lie N}` is a rational character of `M`.
2. *Borel superset.* Since `P → G` is a closed immersion, `P` is closed in `G(𝔸_F)` and
   `L` is compact. Let `B` be a compact neighbourhood of `1` in the positive split centre
   `A_G` of `G(𝔸_F)`, which lies in `T(𝔸_F) ⊆ M`. Let `W = Ω_N Ω_M B L`, a compact subset
   of `P` with `W L = W`. Since `P = N ⋊ M` homeomorphically, `W ⊆ C_N C_M` for compact
   `C_N ⊆ N` and `C_M ⊆ M`. Put `E = W A(t) K`. It is σ-compact, hence Borel, because
   `A(t)` is the image of a closed subset of the σ-compact group `A_{T₀}`. Since `B` is
   central, `S B ⊆ E`.
3. *Iwasawa coordinates of `E`.* If `n m k = w a k'` with `w ∈ W`, `a ∈ A(t)` and
   `k' ∈ K`, then `ℓ = (w a)⁻¹ n m = k' k⁻¹ ∈ L`. By compatibility `ℓ` commutes with `a`,
   so `n m = (w ℓ) a` with `w ℓ ∈ W ⊆ C_N C_M`. Uniqueness of the decomposition in
   `P = N ⋊ M` gives `n ∈ C_N` and `m ∈ C_M A(t)`. Hence
   `Φ⁻¹(E) ⊆ C_N × C_M A(t) × K` and
   `Haar(E) ≤ vol(C_N) vol(K) ∫_{C_M A(t)} δ(m)⁻¹ dm`.
4. *The Levi integral.* For a number field, `M = M(𝔸_F)¹ × A_T` as topological groups,
   where `A_T` is the positive part of `T` (Mœglin–Waldspurger I.2.1, p. 19). The
   character `δ` is trivial on `M(𝔸_F)¹`, because `χ_N` is a rational character of `M`.
   The setup makes `T` the product of the split central component `Z₀` and the image of
   `T₀`, with finite intersection, so `A_T = A_G × A₀`, where `A₀` is the image of
   `A_{T₀}`. The character `δ` is trivial on `A_G`, because `A_G` is central. Projecting
   `C_M` gives compact sets `C¹ ⊆ M(𝔸_F)¹`, `C_G ⊆ A_G` and `C₀ ⊆ A₀` with
   `C_M ⊆ C¹ C_G C₀`. Since `|α|` is bounded below on `C₀`, we get `C₀ A(t) ⊆ A₀(t')` for
   some `t' > 0`. So the Levi integral is at most
   `vol(C¹) vol(C_G) ∫_{A₀(t')} δ(a)⁻¹ da`.
5. *The chamber integral.* The simple roots `α ∈ Δ` restricted to the split torus `T₀`
   form a basis of its rational character group, because they restrict to a basis for the
   maximal split torus of the semisimple derived group. So `λ_α(a) = |α(a)|` is a system of
   coordinates identifying `A₀` with `(ℝ_{>0})^Δ`. In these coordinates the Haar measure
   `da` is a constant multiple of `∏_α dλ_α / λ_α`, and `A₀(t')` is `λ_α ≥ t'` for every
   `α`. Write `χ_N = Σ_β (dim 𝔤_β) β` over the positive relative roots `β`, and expand each
   `β` in simple roots with non-negative integer coefficients. Then
   `χ_N = Σ_α c_α α` with every `c_α ≥ dim 𝔤_α ≥ 1`, and
   `δ(a) = |χ_N(a)| = ∏_α λ_α^{c_α}`. Therefore
   `∫_{A₀(t')} δ(a)⁻¹ da` is a constant times `∏_α ∫_{t'}^∞ x^{-c_α} dx / x < ∞`.
   Both the chamber and `δ` are expressed through the same normalized idelic norm
   `λ_α = |α(a)|`. For `a ∈ A₀`, the value `α(a)` is a positive real `x` placed at every
   archimedean place, and `λ_α = x^{[F:ℚ]}` (Library `normCharacter_fullIntrinsic`). The
   argument does not need this relation.
6. *Norm-one group.* For a number field, `G(𝔸_F) = G(𝔸_F)¹ × A_G` as topological groups
   (I.2.1, p. 19 with `M = G`), and Haar measure on `G(𝔸_F)` is the product of Haar
   measures on the factors. Let `S¹` be the part of `S` in `G(𝔸_F)¹`. Then `S¹ B ⊆ E`, and
   Fubini's theorem shows that `S¹` lies in a Borel subset of `G(𝔸_F)¹` whose Haar measure
   is at most `Haar(E) / vol(B) < ∞`. Any left Haar measure of `G(𝔸_F)¹`, in particular
   `Measure.haar`, is a constant multiple of this one.

Step 3 is the only place where compatibility is used. Without it, `n m` can differ from
`w a` by an element `ℓ ∈ L` that does not commute with `a`, and moving `ℓ` past `a` can
enlarge the `N`-coordinate without bound. For example, for `SL₂` over `ℚ(i)` with
`K_∞ = n(1) SU(2) n(1)⁻¹`, where `n(z)` is the upper unipotent matrix, and with `Ω_N` the
unit disc and `Ω_M` the diagonal unit circle at the complex place, the `N`-coordinates
over `a_r = diag(r, r⁻¹)` fill an annulus of area proportional to `r²`. Then step 3 gives
no bound, so the statement only concerns compatible `K`. This module makes no claim about
incompatible `K`.

## Proofs

**Covolume criterion.** `Λ` is countable because it is discrete in a second-countable
space. Replace `S` by its measurable hull `toMeasurable Measure.haar S`, which has the same
Haar measure. The covering hypothesis makes the image of the hull under the quotient map
`LeftCosetSpace.mk Λ` everything: for a coset of `g`, the element `γ * g ∈ S` lies in the
hull and has the same coset (`mk_subgroup_mul`). The Library inequality
`LeftCosetSpace.quotientMeasure_image_le` bounds the quotient measure of the image of a
measurable set by its ambient measure. It applies to the measurable fundamental domain
`isFundamentalDomain Λ hΛ Measure.haar` that defines `haarQuotientMeasure`. So the measure
of the whole quotient is at most `Measure.haar S < ∞`.

**`adelicSiegelReductionStatement_of_good`.** Take the witnesses of the good statement
and drop the compatibility component.

**`isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_siegel`.** From
`AdelicGoodSiegelReductionStatement` take an algebraic setup, compact factor data `C`, a
threshold `t`, a proof of `IsSiegelCover` and a proof of compatibility. The first
component of `IsSiegelCover` and the compatibility proof are the two hypotheses of
`SiegelProductFiniteMeasureStatement`, which then gives finite Haar measure of
`S = val⁻¹' weakSiegelProduct ...` in `G(𝔸_F)¹`. Apply the covolume criterion with
`H = G(𝔸_F)¹`, `Λ = rationalNormOneSubgroup F G` (discrete by
`isDiscrete_rationalNormOneSubgroup`) and this `S`. This yields finiteness of
`normOneRationalQuotientHaarMeasure F G`, which is the Library's `haarQuotientMeasure` for
this subgroup.

For the covering hypothesis let `x ∈ G(𝔸_F)¹`. The second component of `IsSiegelCover`
says `G(F) · weakSiegelProduct = G(𝔸_F)¹` as subsets of `G(𝔸_F)`. So `x = q s` with
`q` a principal rational point and `s` in the Siegel product. The element
`rationalNormOne F G q⁻¹` of `rationalNormOneSubgroup F G` then satisfies
`q⁻¹ x = s`, which lies in the Siegel product.

**`connectedReductiveFiniteVolumeStatement_of_siegel`.** Introduce the bound variables of
`ConnectedReductiveFiniteVolumeStatement` and apply the previous theorem.
