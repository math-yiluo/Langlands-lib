# Lattice coordinates on `G(F)` and the restriction kernel in torus coordinates

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.TorusLatticeDuality` (submitted with this module):
  `latticeAnnihilator`, `mem_latticeAnnihilator`, and through `TorusFourierInversion` and
  `TorusFourierDecay` the characters `torusCharacter`;
- the published `Representation.Plancherel.RationalUnramifiedCharacterCoordinates` (Worker 200):
  `rationalReductiveValuationBasis G hG`, a `ℤ`-basis indexed by `Fin (rationalImageRank G)` of
  `Additive (rationalDiscreteValuationImage G)`, the image lattice of the integer valuation map
  (written `Λ(G)`), and the circle coordinates
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG : Im X(G) ≃ₜ* (Fin r → Circle)`
  with their value formula `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_symm_apply`;
- the published `Representation.Plancherel.RationalNormKernelTopology` (Worker 200):
  `continuous_rationalValuationImageProjection`;
- the published `Representation.Plancherel.RationalRestrictionKernel` (Worker 200):
  `mem_rationalUnitaryUnramifiedCharacterRestrict_ker`, and through its imports
  `rationalUnitaryUnramifiedCharacterRestrict` and `RenardCartan.splitValuationImage`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- I.1, printed pp. 239–240 (PDF pp. 5–6): `G¹`, `X(G) = Hom(G/G¹, ℂ^×)`, its unitary subgroup
  `Im X(G)` and `H_G`; "L'application de restriction `Im X(G) → Im X(A_G)` est surjective de
  noyau fini" (p. 239). In the Library, `Im X(G)` is `unitaryUnramifiedCharacters` for the
  rational norm characters, and the integer valuation map `rationalValuationImageProjection G`
  (kernel `G¹`, `rationalValuationImageProjection_ker`) is used in place of `H_G`.
- Proof of Proposition VII.2.1, case `M = G`, printed pp. 317–318 (PDF pp. 83–84): the Fourier
  inversion over `A_G` (quoted in `TorusFourierInversion.md`).

Waldspurger works with `Im X(G)` and `H_G` directly and has no coordinates. This module puts
the Library's coordinates in the form needed by the torus results: the characters become
`z ↦ ∏ᵢ zᵢ^{n(g)ᵢ}` and the restriction kernel to a central `T` becomes the annihilator of the
lattice `n(s(T(F)))`. The statements are derived for this purpose.

## Scope and hypotheses

`F` is a nonarchimedean local field, `G` an affine group scheme over `F` locally of finite type,
and `G(F) = GroupScheme.rationalPoints G` has the canonical `rationalPointTopology F G.X`.
`hG : GroupScheme.IsConnectedReductive G` is an explicit argument of every declaration. In the
last section `T` is a commutative group scheme over `F` and `s : T → G` an arbitrary morphism of
group schemes; centrality is not needed for these statements.

Hypotheses of the results:

- `rationalValuationCoordinates_apply`, `rationalValuationCoordinates_mul`,
  `rationalValuationCoordinates_one`, `rationalUnitaryUnramifiedCharacter_apply`: `hG`.
- `continuous_rationalValuationCoordinates`: `hG`, `IsAffine G.X.left` and
  `LocallyOfFiniteType G.X.hom` (for the topology).
- `measurable_rationalValuationCoordinates`: in addition a measurable space on `G(F)` with
  `OpensMeasurableSpace`.
- `mem_rationalSplitLattice`: `hG`.
- `finiteIndex_rationalSplitLattice`: `hG` and
  `hindex : (RenardCartan.splitValuationImage s).FiniteIndex`, the finite index of the image of
  `T(F)` in the valuation image lattice of `G`.
- `coordinates_symm_mem_restrict_ker_iff`: `hG`, `IsAffine G.X.left`, `IsAffine T.X.left`.

## Definitions

- `rationalValuationLatticeEquiv G hG : Additive Λ(G) ≃+ (Fin r → ℤ)`, the coordinate isomorphism
  of the basis `rationalReductiveValuationBasis G hG`.
- `rationalValuationCoordinates G hG g`, the coordinates `n(g) ∈ ℤ^r` of the valuation image of
  `g ∈ G(F)`.
- `rationalSplitLattice hG s : AddSubgroup (Fin r → ℤ)`, the split valuation image
  `RenardCartan.splitValuationImage s` (the image of `T(F)` in `Λ(G)`) in coordinates, written
  `Λ_s`.

## Results

- `rationalValuationCoordinates_apply`: `n(g)ᵢ` is the `i`-th basis coordinate of the valuation
  image of `g`.
- `rationalValuationCoordinates_mul`, `rationalValuationCoordinates_one`: `n` is a homomorphism.
- `continuous_rationalValuationCoordinates`: `n` is continuous, hence locally constant.
- `measurable_rationalValuationCoordinates`: `n` is measurable.
- `rationalUnitaryUnramifiedCharacter_apply`: the unitary unramified character with circle
  coordinates `z` takes the value `torusCharacter (n g) z = ∏ᵢ zᵢ^{n(g)ᵢ}` at `g`.
- `mem_rationalSplitLattice`: `m ∈ Λ_s` if and only if `m = n(s(t))` for some `t ∈ T(F)`.
- `finiteIndex_rationalSplitLattice`: `Λ_s` has finite index in `ℤ^r` if the split valuation
  image has finite index in `Λ(G)`.
- `coordinates_symm_mem_restrict_ker_iff` (**restriction kernel in coordinates**): the character
  with circle coordinates `z` lies in the kernel of the restriction
  `rationalUnitaryUnramifiedCharacterRestrict s` (it is trivial on `s(T(F))`) if and only if
  `z ∈ latticeAnnihilator Λ_s`.

With `TorusLatticeDuality` (`finite_latticeAnnihilator`, `isTrivialOn_latticeAnnihilator_iff`),
the last two results say that for a split component `s` with `hindex`, the restriction kernel
`K = ker(Im X(G) → Im X(A_G))` is, in coordinates, the finite annihilator of the finite-index
lattice `Λ_s`, and the characters `χ_m` of the torus trivial on `K` are exactly the `m ∈ Λ_s`.

## Proof notes

1. `n` is the valuation-image projection followed by the additive coordinate isomorphism, so it
   is additive. Continuity: the projection is continuous into the discrete image, and every map
   out of a discrete space is continuous. Measurability follows.
2. Character formula: the published value formula gives `((∏ᵢ zᵢ^{n(g)ᵢ} : Circle) : ℂ)`, and the
   inclusion `Circle → ℂ` is multiplicative (`map_prod Circle.coeHom`).
3. `Λ_s` is the preimage of the split valuation image under the inverse coordinate isomorphism.
   Membership unwinds to `n(s(t)) = m`. Its index equals the index of the split valuation image
   (`AddSubgroup.index_comap_of_surjective`, `Subgroup.index_toAddSubgroup`).
4. Restriction kernel: by `mem_rationalUnitaryUnramifiedCharacterRestrict_ker` the character is
   in the kernel if and only if its value at every `s(t)` is `1`; by step 2 that value is
   `χ_{n(s(t))}(z)`, and by step 3 the `n(s(t))` are exactly the elements of `Λ_s`.

## Relation to the Library

`RationalUnramifiedCharacterCoordinates` constructs the coordinates and the Laurent-monomial
value formula used here; this module records `n` as a function on `G(F)` with its continuity and
the torus-character form of the values. `RationalRestrictionKernel` proves that the restriction
kernel is finite under `hindex`; this module identifies it with a lattice annihilator, so that
`TorusLatticeDuality` and `TorusFourierInversion` apply to it. `SplitComponentLatticeBridge`
proves `hindex` for a split component whose restriction of rational characters is injective
(`finiteIndex_splitValuationImage_of_injective`).

## Open obligations

For Proposition VII.2.1: the sum over `A_G / (A_G ∩ G¹)` in place of the integral over `A_G`,
the passage from `Im X(G)` to the orbit `Im X(G)/S` with its factor `|S|` (III.7; the orbit
measure of `RationalNormalizedOrbitMeasure`), and the remaining steps of the proof.
