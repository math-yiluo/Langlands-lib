# Adelic identity neighborhoods from archimedean triple cells

Module `Langlands.Global.AdelicArchimedeanTripleCell`, namespace `Langlands.Global`.

## Declarations

### Naturality

For affine group schemes `H`, `G` over a number field `F` and a homomorphism `f : H → G`:

- `atPlace_affinePointsTarget`: the projection `InfiniteAdelicGroupPoints.atPlace` from
  `G(F_∞)` to the completion `G(F_v)` at an archimedean place `v` commutes with `f`. Proof:
  injectivity of regular-function evaluation (`affinePointEvaluation_injective`) with
  `atPlace_evaluation` and `affinePointEvaluation_postcomp`.
- `inAdelicGroupPoints.finite_map` and `AdelicGroupPoints.finite_map`: the infinite and finite parts of `G(𝔸)` commute with the
  adelic map `map F H G f` (naturality of `affinePointsTarget` for the projections of
  `𝔸 = F_∞ × 𝔸_f`).
- `AdelicGroupPoints.map_ofInfinite`: `map F H G f (ofInfinite F H y) = ofInfinite F G (f(y))` for `y ∈ H(F_∞)`,
  checked on both components of `AdelicGroupPoints.split`.

### The assembly

`exists_nhds_eq_ofFinite_mul_triple`. Let `G` be affine and locally of finite type over `F` and
`iₖ : Nₖ → G` (`k = 1, 2, 3`) homomorphisms from affine group schemes whose underlying morphisms
are closed immersions. Suppose that at every archimedean place `v` and for every identity
neighborhood `A` of `G(F_v)`, the set of products `a b c` with `a`, `b`, `c` in `A` and in the
images of `N₁(F_v)`, `N₂(F_v)`, `N₃(F_v)` respectively is an identity neighborhood of `G(F_v)`.
Then there are an identity neighborhood `W` of `G(𝔸)`, compact sets `Kₖ ⊆ Nₖ(𝔸)` and a compact
`L ⊆ G(𝔸_f)` such that every `g ∈ W` is

`g = ofFinite(l) · i₁(x₁) · i₂(x₂) · i₃(x₃)` with `l ∈ L` and `xₖ ∈ Kₖ`

(`ofFinite` includes a finite adelic point with archimedean part `1`).

*Proof.* At each place choose a compact identity neighborhood `A_v` of `G(F_v)` (local
compactness, `affinePointsLocallyCompactSpace`); by hypothesis the corresponding cell `C_v` is an
identity neighborhood. As there are finitely many archimedean places, the points of `G(F_∞)` all
of whose components lie in the cells form an identity neighborhood `W_∞`; with a compact identity
neighborhood `L` of `G(𝔸_f)`, `W` is the set of `g` with infinite part in `W_∞` and finite part
in `L`. The set `Kₖ` consists of the points `ofInfinite(assemble(y))` with `y_v` in the preimage
of `A_v` under `iₖ` at every place; these preimages are compact because `iₖ` is a closed
embedding on `F_v`-points (`isClosedEmbedding_affinePointsTarget`), so `Kₖ` is compact. For
`g ∈ W`, decompose each component of the infinite part, choose preimages of the three factors,
assemble them over the places (`InfiniteAdelicGroupPoints.assemble`) and compare components
(`InfiniteAdelicGroupPoints.completions` is injective). Finally `g = ofFinite(g_f) · ofInfinite(g_∞)`
and `AdelicGroupPoints.map_ofInfinite` gives the factorization.

## Provenance

Internal and derived: the assembly over places of local factorizations, using the published
product structures `AdelicGroupPoints.split` and `InfiniteAdelicGroupPoints.completions`. Its use
is the archimedean open cell of `Langlands.Global.AdelicSiegelArchimedeanCell`.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
