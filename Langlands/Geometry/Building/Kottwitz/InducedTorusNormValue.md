# The norm law on rational points built from a permuted cocharacter basis

This internal helper module, used by the proof of KP Corollary 11.1.9
(`inducedTorusKottwitzRationalSurjectivity`), computes the constructed Kottwitz
map `torusKottwitz F F T hT` on a rational point whose extension to a splitting
field `E` is an explicit cocharacter expansion. It then proves that this value is
a prescribed class. The only input from the source is the norm law of KP
Proposition 11.1.1, through the Library's proved `torusKottwitzExistence`.
Everything else is derived from existing Library APIs.

All declarations are in `Langlands.Geometry.Building.Kottwitz.InducedCocharacterBasis`.

## Setting

As in `InducedCocharacterBasis`, `F` is a nonarchimedean local field and `E` is a
finite Galois intermediate field of `F^sep/F` over which the affine torus `T`
splits. `b` is a character basis of `T_E` indexed by a finite `J`. In addition,
`L : IntermediateField K F^sep` with `K = UnramifiedClosure F` satisfies
`hL` (`T_L` is split) and `hEL : ∀ x ∈ E, x ∈ L`. The inclusion `E → L` is never
made an algebra instance; that instance search times out. Points are compared
through `F^sep` instead.

## Declarations

* `relativeExtend_coefficientEvaluation_sum` (generic fields `k → L → M`):
  extending coefficients of `∑ xᵢ ⊗ νᵢ` gives `∑ xᵢ ⊗ ext(νᵢ)`. Proof: additivity
  and the Library's `relativeExtend_coefficientEvaluation_tmul`.
* `inclusionHom F E L hEL : E →* L`, the inclusion inside `F^sep`.
* `splitBasis j`: the cocharacter of `T_L` whose extension to `F^sep` is
  `geometricBasis j`. It exists because `extendGeometricCocharacters F L F^sep T`
  is bijective (`extendGeometricCocharacters_bijective`).
  `extendGeometricCocharacters_splitBasis` records this.
* `extend_eq_of_extend_eq`: if `extend_E x0 = ∑ⱼ x j ⊗ dualBasis j`, then
  `extend_L x0 = ∑ⱼ (x j) ⊗ splitBasis j`, with units mapped by `inclusionHom`.
  Proof: extension to `F^sep` is injective (`GaloisPoint.relativeExtend_injective`).
  Both sides extend, through `relativeExtend_extend` and the generic sum lemma, to
  `∑ⱼ x j ⊗ geometricBasis j`.
* `normLawValue_sum`: the norm-square value `normLawValue F F T L hL` of
  `∑ⱼ wⱼ ⊗ νⱼ` is `proj (∑ⱼ ord_L(wⱼ) • ext(νⱼ))`. Here `proj` is the inertia
  projection and `ord_L` is the integer order for `normalizedIntermediateValuation F L`.
  Proof: additivity and `normLawValue_tmul`.
* `card_smul_torusKottwitz`: for `L` finite Galois over `K` and `x0` as above,
  `|Gal(L/K)| • κ(extend_K x0) = proj (∑ⱼ ord_L(x j) • geometricBasis j)`.
  Proof: apply the norm law of `torusKottwitzExistence`, in the form
  `torusNormLawAt_iff`, to `relativeExtend_{K→L}(extend_K x0)`. Its relative
  norm is the `|Gal(L/K)|`-th power (`relativeNorm_relativeExtend`). It equals
  `extend_L x0` (`relativeExtend_extend`), which `extend_eq_of_extend_eq`
  expands; then apply `normLawValue_sum`.
* `orderUnits_inclusionHom_zpow`: `ord_L(w^m) = m · ord_L(w)` for `w ∈ Eˣ`.
* `galoisRepresentation_geometricBasis_smul`: suppose `Gal(F^sep/F)` acts on `J`
  through `σ • j = indexHom (σ.restrictNormal E) j` (hypothesis `hact`). Then it
  permutes the geometric basis.
* `mk_sum_eq_card_smul`: let `u : J → Eˣ` have inertia-orbit sums of
  `ord_L(u i)` equal to `[L : K]` (hypothesis `hsum`). Let the orbit sums
  `n j = orbitSum ν j` of `ν` be `Gal(F^sep/F)`-invariant (hypothesis `hn`).
  Then `proj (∑ⱼ ord_L(u j ^ n j) • geometricBasis j) = proj (|Gal(L/K)| • ν)`.
  Proof: by `PermutationCoinvariants.mk_eq_mk_iff` it suffices to compare orbit
  sums. The coordinates of the left vector are `n j · ord_L(u j)`
  (`Basis.repr_sum_self`, `orderUnits_inclusionHom_zpow`). `n` is constant on
  inertia orbits, so its orbit sum is `n j · [L : K]` (`orbitFunSum_mul_const`,
  `hsum`). The right side gives `|Gal(L/K)| · n j`, and
  `|Gal(L/K)| = [L : K]` (`IsGalois.card_aut_eq_finrank`).
* `torusKottwitz_eq_of_family`: under the hypotheses of the previous lemma, if
  `extend_E x0 = ∑ⱼ (u j ^ n j) ⊗ dualBasis j`, then `κ(extend_K x0) = proj ν`.
  Proof: `card_smul_torusKottwitz` and `mk_sum_eq_card_smul` give
  `|Gal(L/K)| • κ = |Gal(L/K)| • proj ν`. Then cancel with
  `PermutationCoinvariants.zsmul_cancel`, using `|Gal(L/K)| ≠ 0`. This step has
  to sit in this module: the `ℤ`-actions on the coinvariants that it compares are
  then elaborated identically.
