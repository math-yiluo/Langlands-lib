# Square integrability of restrictions of elements of `A^2_P`

Module `Langlands.Global.AdelicInducedRestrictionMemLpStatement` states one
proposition, `Langlands.Global.InducedRestrictionMemLpStatement`. It proves
nothing and asserts nothing. The proposition is a premise of the bridge
`Langlands.Global.ImaginaryIntertwiningExistenceBridgeStatement`, which derives
the existence of the operators `M(w, λ) : H_P → H_{P'}` on the imaginary axis
from the published unitarity statement
`Langlands.Global.IntertwiningImaginaryUnitarityStatement`.

## Statement

`InducedRestrictionMemLpStatement` says the following. Take:

- a number field `F` and a connected reductive group `G` over `F`;
- a parabolic subgroup `P` with presentation `r`, rational Levi `l : M → P`,
  unipotent radical `iU : U → P` with `P = M ⋉ U`
  (`IsIso (subgroupMultiplication l iU)`), and Levi projection `π`
  (`l ≫ π = 𝟙`);
- a maximal compact subgroup `K` of `G(𝔸)` with `P(𝔸)K = G(𝔸)`
  (`IsIwasawaCompact`), the data `rho`, `hsmooth`, `hcalc` that define
  automorphic forms (with `rho` a closed embedding);
- a Haar measure `μ_M` on `M(𝔸)` compatible with the Iwasawa decomposition
  (`IsIwasawaCompatibleMeasure`);
- linear coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, and a continuous, compactly
  supported, nonnegative function `β` on `ℝⁿ`.

Then for every `φ ∈ A^2_P` (`IsSquareIntegrableInducedForm`), the restriction
`(k, m) ↦ φ(m k)` (`inducedRestriction K p l φ`, read at the chosen coset
representatives of `M(F) \ M(𝔸)`) lies in `L²` (`MemLp … 2`) for the measure
`β(y(m)) δ_P(m)⁻¹ dk dm` on `K × M(F) \ M(𝔸)` (`inducedL2Measure`). Here
`y(m)` are the `e`-coordinates of `H_P(m)`.

The hypotheses on `P` and `K` are the `P`-side hypotheses of
`ImaginaryIntertwiningExistenceStatement` (module
`Langlands.Global.AdelicSpectralTransformInputs`), in the same order. MemLp
has two parts: almost-everywhere strong measurability of the restriction, and
finiteness of the weighted `L²` norm.

## Sources and why the statement is true

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §2, p.311
  (PDF page 320). `A^2_P` is the space of automorphic forms `φ` on
  `U(𝔸) M(F) \ G(𝔸)` with `φ(a g) = δ_P(a)^{1/2} φ(g)` for `a ∈ A_M` and
  `‖φ‖²_P = ∫_{A_M U(𝔸) M(F) \ G(𝔸)} |φ(g)|² dg < ∞`.
- J. Arthur, *An introduction to the trace formula* (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, §7, p.32 (PDF
  page 44): the Hilbert space `H_P` with norm
  `‖φ‖² = ∫_K ∫_{M_P(F) \ M_P(𝔸)¹} |φ(mk)|² dm dk`. The statement says that
  `A^2_P` lies in the realization of `H_P` used in the Library
  (`inducedHilbertSpace`, module `Langlands.Global.AdelicSpectralTransformSpaces`).

The statement is a reformulation of the finiteness of `‖φ‖_P`. The map `H_P`
identifies the split component `A_M` of `M(𝔸)` with `𝔞_P`. The function
`m ↦ δ_P(m)⁻¹ |φ(mk)|²` is `A_M`-invariant, by the `A^n_P` condition
(`IsSplitComponentEquivariant`). Integrating over `M(F) \ M(𝔸)` in two stages,
`A_M` and then `A_M M(F) \ M(𝔸)`, gives

`∫_K ∫_{M(F)\M(𝔸)} β(y(m)) δ_P(m)⁻¹ |φ(mk)|² dm dk = c · ∫_{ℝⁿ} β(y) dy · ‖φ‖²_P`.

Here `c > 0` depends only on the normalizations of the Haar measures. The right
side is finite because `β` is continuous with compact support; the last factor
is finite because `φ ∈ A^2_P`, and it is the integrability condition in
`IsSquareIntegrableInducedForm`. Measurability holds because `φ` is
continuous and left `M(F)`-invariant. Its restriction is therefore the descent
of a continuous function on `K × M(𝔸)` to `K × M(F) \ M(𝔸)`, and its value does
not depend on the chosen representatives.

## Provenance

Internal formulation of a standard fact: elements of `A^2_P` define elements
of the induced Hilbert space (Lapid 2011, §2; Arthur 2005, §7, p.32). It is
stated in the Library's coordinates (`inducedRestriction`,
`inducedL2Measure`). It is needed because a Gram identity for the inner
products `(·,·)_P` alone does not make a restriction square integrable for the
measure of `H_P`.
