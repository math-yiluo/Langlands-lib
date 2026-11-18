# The classes `unipotentIntegralClasses` as a quotient of a semilocal group

This module is the second piece of the proof of premise B
(`UnipotentClassProductStatement`) of the published reduction
`ArchimedeanFactorizationReduction` (Task 7397). Premise B integrates over the
set `unipotentIntegralClasses F m S` of classes `N_m(𝔸) g` in
`N_m(𝔸) \ GL_m(𝔸)` whose representative has `g_v ∈ N_m(F_v) GL_m(𝒪_v)` at
every finite place `v ∉ S`. Here that set is identified with the quotient
`𝒩 \ 𝒢` of a product of local groups, compatibly with right translations and
with the local projections used in premise B. The measure-theoretic
comparison is a separate piece.

Provenance: internal. These are the standard facts behind the decomposition of
the domain of a partial Whittaker integral into local factors (Cogdell 2004,
proof of Theorem 4.1, pp.219-220, uses them without comment), written here for
the Library's adelic groups. All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.UnipotentClass`. Throughout, `F` is a
number field, `m : ℕ` and `S` is a finite set of finite places.

## General linear groups over products of rings

- `glProdEquiv A B n : GL_n(A × B) ≃ₜ* GL_n(A) × GL_n(B)` for topological
  commutative rings `A`, `B`. The forward map applies `GL.map` of the two
  projections. The inverse pairs the entries of two matrices (`prodMatrix`)
  and pairs their inverse matrices for the inverse. It is continuous by
  `Units.continuous_iff`, entry by entry. The construction copies the pattern
  of the Library's `AdelicGL.split`.
- `glPiEquiv n R : GL_n(∀ i, R i) ≃ₜ* ∀ i, GL_n(R i)` for any family of
  topological commutative rings, in the same way (`piMatrix`).
- `prodCongr`: the product of two isomorphisms of topological groups. Mathlib
  has no such construction for `ContinuousMulEquiv`.

## The decomposition of `GL_m(𝔸)`

- `RealGL F m = ∏_v GL_m(ℝ)` over the real places, `ComplexGL F m = ∏_w GL_m(ℂ)`
  over the complex places, `LocalGL F m S = ∏_(v ∈ S) GL_m(F_v)`, and
  `AwayGL F m S` is the restricted product of the `GL_m(F_v)`, `v ∉ S`, with
  respect to the `GL_m(𝒪_v)` (the Library's `AwayRestrictedProduct`).
- `archSplit F m : GL_m(F_∞) ≃ₜ* RealGL F m × ComplexGL F m` composes the
  Library's mixed coordinates `archimedeanGLCoordinates` with `glProdEquiv` and
  `glPiEquiv`.
- `adelicSplit F m S : (RealGL × ComplexGL) × (LocalGL × AwayGL) ≃ₜ* Points F m`
  composes `archSplit`, the Library's `FiniteAdelicGL.splitAtPlaces` (for the
  predicate `· ∈ S`), `AdelicGL.split` and the comparison
  `GeneralLinearGroupPoints.adelicHomeomorph` between group-scheme points and
  adelic matrices.
- Components: `realComponent_adelicSplit`, `complexComponent_adelicSplit`,
  `finiteComponent_adelicSplit_of_mem` and `finiteComponent_adelicSplit_of_not_mem`
  show that the Library's component maps `realComponent`, `complexComponent`
  and `finiteComponent`, applied to `adelicSplit w`, return the corresponding
  coordinate of `w`. The component maps are multiplicative
  (`realComponent_mul`, `realComponent_inv`, and similarly for the others).
  They send `N_m(𝔸)` into the local upper unitriangular groups
  (`realComponent_mem`, `complexComponent_mem`, `finiteComponent_mem`), because
  the entries of a component are images of the adelic entries under ring
  homomorphisms.
- `adelicSplit_mem_iff`: `adelicSplit w ∈ N_m(𝔸)` iff every coordinate of `w`
  is upper unitriangular. Membership in `N_m(𝔸)` means that the adelic matrix is
  upper unitriangular (Library `Unfolding.mem_unipotentAdelic_iff`). The
  forward direction follows from the component lemmas. For the converse, an
  adelic entry is `0` (or `1`) as soon as its archimedean part, computed by
  `archSplit_symm_apply`, and its value at every finite place, given by the
  Library's `localProjection_splitAtPlaces_symm_of_pos/_of_neg`, are.

## The semilocal group and the unipotent subgroup

- `awayIntegralSubgroup F m S = K^S`: the families integral at every place
  outside `S` (the Library's open subgroup `awayIntegral`). It is compact
  (`isCompact_awayIntegral`): by the Library's `map_standardIntegral_splitAtPlaces`
  it is the second projection of the image of the compact standard integral
  subgroup `∏_v GL_m(𝒪_v)` under `splitAtPlaces`.
- `SemilocalGL F m S = 𝒢 = (RealGL × ComplexGL) × (LocalGL × K^S)`, and
  `semilocalEmbedding F m S = Ψ : 𝒢 →* Points F m` is `adelicSplit` after the
  inclusion of `K^S`. It is an open embedding (`isOpenEmbedding_semilocalEmbedding`),
  since `K^S` is open and `adelicSplit` is a homeomorphism.
- `awayUnipotent F m S`: the elements of `K^S` that are upper unitriangular at
  every place. `semilocalUnipotent F m S = 𝒩` is the product subgroup
  `(∏_v N_m(ℝ) × ∏_w N_m(ℂ)) × (∏_(v ∈ S) N_m(F_v) × awayUnipotent)`, written
  with `Subgroup.prod` and `Subgroup.pi`.
- `semilocalEmbedding_mem_iff`: `Ψ x ∈ N_m(𝔸) ↔ x ∈ 𝒩`, from
  `adelicSplit_mem_iff`. Consequently `𝒩` is closed
  (`isClosed_semilocalUnipotent`): it is the preimage of the closed subgroup
  `N_m(𝔸)` (Library `isClosed_upperUnipotent_adelicPoints`) under `Ψ`.

## The class map

- `SemilocalQuotient F m S = 𝒩 \ 𝒢` (the Library's `LeftCosetSpace`), and
  `classMap F m S : 𝒩 \ 𝒢 → N_m(𝔸) \ GL_m(𝔸)` sends `𝒩 x` to `N_m(𝔸) Ψ(x)`
  (`classMap_mk`). It is well defined and injective because
  `Ψ(y) Ψ(x)⁻¹ = Ψ(y x⁻¹) ∈ N_m(𝔸) ↔ y x⁻¹ ∈ 𝒩`.
- `isOpenEmbedding_classMap`: it is continuous (a lift of a continuous map)
  and open: the image of an open set `U` is the image under the open quotient
  map of `GL_m(𝔸)` of the image under the open map `Ψ` of the preimage of `U`.
- `isUnipotentIntegral_iff`: the Library's condition `IsUnipotentIntegral`
  says exactly that `x k` is upper unitriangular for some `k ∈ GL_m(𝒪_v)`.
- `mul_mem_unipotentIntegralOutside_iff`: left multiplication by `N_m(𝔸)` does
  not change whether a point lies in `unipotentIntegralOutside`, because the
  finite components of `n ∈ N_m(𝔸)` are unitriangular. Hence
  `mk_mem_unipotentIntegralClasses_iff`: the class of `g` lies in
  `unipotentIntegralClasses F m S` iff `g` lies in `unipotentIntegralOutside`.
  The representative `out` used in the definition of
  `unipotentIntegralClasses` differs from `g` by an element of `N_m(𝔸)`.
- `exists_semilocal_of_mem_unipotentIntegralOutside`: if `g` lies in
  `unipotentIntegralOutside`, there is `y ∈ 𝒢` with the archimedean and `S`
  coordinates of `g` such that `g Ψ(y)⁻¹ ∈ N_m(𝔸)`. Proof: write
  `g = adelicSplit w` and choose `k_v ∈ GL_m(𝒪_v)` with `g_v k_v` upper
  unitriangular for each `v ∉ S`. The family `(k_v)` defines an element
  `k ∈ K^S` (every component is integral). Put `y = (w_∞, (w_S, k⁻¹))`. Then
  `g Ψ(y)⁻¹ = adelicSplit (w y'⁻¹)` has trivial archimedean and `S` coordinates
  and the unitriangular coordinates `g_v k_v` outside `S`, so it lies in
  `N_m(𝔸)` by `adelicSplit_mem_iff`.
- `exists_unipotent_mul_mul_of_mem_unipotentIntegralOutside`: the same
  statement in explicit form, `g = n · g' · k` with `n ∈ N_m(𝔸)`, `g'` the
  point with the archimedean and `S` components of `g` and identity components
  outside `S`, and `k = adelicSplit (1, (1, k₀))` for some `k₀ ∈ K^S`. It
  follows from the previous lemma because `Ψ(y) = g' · k`.
- `range_classMap`: the image of `classMap` is `unipotentIntegralClasses F m S`.
  If `x ∈ 𝒢`, the component of `Ψ x` at `v ∉ S` lies in `GL_m(𝒪_v)`, and
  `k = (Ψ x)_v⁻¹` shows that it lies in `N_m(F_v) GL_m(𝒪_v)`. Conversely, if the
  class of `g` lies in `unipotentIntegralClasses`, the reduction lemma gives `y`
  with `g Ψ(y)⁻¹ ∈ N_m(𝔸)`, that is, the class of `g` is `classMap (𝒩 y)`.

## Local projections

For `m = t + 1`, the Library's projections `realQuotientProjection`,
`complexQuotientProjection` and `finiteQuotientProjection` take the class of
the component of the chosen representative `q.out`. The lemmas
`realQuotientProjection_mk`, `complexQuotientProjection_mk` and
`finiteQuotientProjection_mk` show that any representative `g` gives the same
local class. `g` and `q.out` differ by an element of `N_m(𝔸)`, whose
components are unitriangular. Consequently
`realQuotientProjection_classMap`, `complexQuotientProjection_classMap` and
`finiteQuotientProjection_classMap` (for `v ∈ S`) state that the local
projections of `classMap (𝒩 x)` are the classes of the coordinates
`x_v` of `x`.
