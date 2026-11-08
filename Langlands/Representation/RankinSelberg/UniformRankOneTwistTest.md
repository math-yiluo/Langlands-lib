# The twisted principal test of Jacquet–Shalika §2.5 and its Fourier support

Author: Worker 1807. Worker 1836 specified the exact statement of
`twistedEpsilonWeight` and `coefficientIota_eq_of_fourierIntegral_ne_zero`,
for use in their epsilon module.

This internal helper module serves the proof of
`Langlands.RankinSelberg.UniformRankOneTwistStatement`. It builds the
Godement–Jacquet test function used to compute the epsilon monomial of a
highly ramified twist, and it locates the support of that test's Fourier
transform. It then evaluates the inverse-transpose transform of a suitable
function on that support. The module states no zeta integral, convergence,
functional equation or representation-theoretic fact. Its last result is a
pointwise identity for an arbitrary complex function on `GL_(n+1)(F)` with
the stated central and `K_(m')` transformation law.

Everything is over the canonical topology, valuation and Borel structure of
the supplied p-adic field `F`, with the local instances used elsewhere in the
Library. `𝓛 i` is the canonical additive lattice `{x | v(x) ≤ exp i}`, which
is `ϖ^(-i) O`. The matrices are square of size `n + 1`.

## Objects

- `matrixLattice F n i`: the additive subgroup of matrices with every entry in
  `𝓛 i`. For `i = -j` this is `ϖ^j M_(n+1)(O)`.
- `principalSet F n j`: the set `{y | y - 1 ∈ matrixLattice F n (-j)}`, that
  is `1 + ϖ^j M(O)`, inside *all* square matrices. It is compact
  (`isCompact_principalSet`).
- `inverseDetTwist F χ y`: `χ(det y)⁻¹` if `det y ≠ 0`, and `0` otherwise.
- `twistedPrincipalFun F χ j`: the indicator of `principalSet F n j` times
  `inverseDetTwist F χ`, that is `1_{1 + ϖ^j M(O)}(y) · χ(det y)⁻¹`.
- `twistLevel k = max 1 ⌈k/2⌉`, computed as `max 1 ((k + 1) / 2)`. It is
  positive, and `k ≤ 2 · twistLevel k`.
- `twistedPrincipalTest F n χ`: `twistedPrincipalFun F χ j` packaged as a
  `GodementJacquet.MatrixTestFunction`, at `j = twistLevel (a(χ))`, where
  `a(χ)` is the canonical multiplicative conductor exponent
  `multiplicativeConductor χ`. Local constancy is
  `isLocallyConstant_twistedPrincipalFun` (it needs `0 < j` and `a(χ) ≤ 2j`),
  and compact support is `hasCompactSupport_twistedPrincipalFun`.
- `twistedEpsilonWeight F χ ω g`, for `g ∈ GL_(n+1)(F)` and a character
  `ω : F^× → ℂ^×`: the value `ω(g₀₀)⁻¹ · χ(g₀₀)^(n+1) · χ(det g)⁻¹` when
  `g₀₀ ≠ 0`, and `0` when `g₀₀ = 0`. The case split keeps the definition free of
  choices. Only the case `g₀₀ ≠ 0` is used, through
  `twistedEpsilonWeight_of_ne`.

## Results

Valuation and determinant lemmas:

- `mul_mem_lattice`, `valuation_lt_one_of_mem`, `valuation_one_add`,
  `mem_principalUnits_of_sub_one_mem`, `div_mem_lattice_of_valuation_eq_one`
  and `valuation_eq_exp_of_le_of_not_le` are elementary facts about the
  lattices `𝓛 i` and the principal unit groups.
- `det_one_add_sub_trace_mem`: for `Z ∈ ϖ^j M(O)`,
  `det(1 + Z) - 1 - tr Z ∈ ϖ^(2j) O`.
- `det_add_sub_det_mul_mem`: for `Y, a ∈ ϖ^j M(O)`,
  `det(1 + Y + a) - det(1 + Y)(1 + tr a) ∈ ϖ^(2j) O`.
- `det_one_add_sub_one_mem` and `valuation_det_one_add`: for `j ≥ 1` and
  `Y ∈ ϖ^j M(O)`, `det(1 + Y) ≡ 1` modulo `ϖ^j`, so it is a valuation unit.

Translation law of the test:

- `twistedPrincipalFun_add`: if `0 < j`, `a(χ) ≤ 2j`, `a ∈ ϖ^j M(O)` and `u`
  is the unit `1 + tr a`, then for every matrix `y`,
  `Φ(y + a) = χ(u)⁻¹ · Φ(y)`, where `Φ = twistedPrincipalFun F χ j`.

Fourier support, for an arbitrary unitary additive character `ψ` and scalar
additive Haar measure `ν`, with `Φ^ = rectangularFourierIntegral ψ ν Φ` (the
plus transpose-pairing convention used by `GodementJacquet.MatrixFourierPair`):

- `fourierIntegral_twistedPrincipalFun_eq`: under the same hypotheses,
  `Φ^(x) = χ(u)⁻¹ · ψ(⟨a, x⟩) · Φ^(x)` for every matrix `x`.
- `character_eq_of_fourierIntegral_ne_zero`: where `Φ^(x) ≠ 0`,
  `ψ(⟨a, x⟩) = χ(1 + tr a)` for every `a ∈ ϖ^j M(O)`.
- `entry_character_eq`: the special case where `a` is the matrix unit
  `t · E_(r,c)`. Then `ψ(t · x_(r,c))` equals `χ(1 + t)` if `r = c`, and `1`
  otherwise.
- `fourierIntegral_twistedPrincipalFun_support`: if `ψ` has conductor exponent
  `0`, `0 < j`, `a(χ) ≤ 2j` and `j < a(χ)`, then every `x` with `Φ^(x) ≠ 0`
  satisfies `v(x₀₀) = exp(a(χ))`, so `|x₀₀| = q^(a(χ))`, and
  `x₀₀⁻¹ · x ∈ principalSet F n (a(χ) - j)`, that is
  `x ∈ x₀₀ (1 + ϖ^(a(χ) - j) M(O))`.

Dual side. Here `K_a` is `Conductor.principalLevelSubgroup F.Carrier n a`,
the principal congruence subgroup of level `a` of `GL_(n+1)(F)`, and
`ι g = (g⁻¹)ᵀ` is `GeneralLinear.inverseTranspose`:

- `exists_mem_principalLevelSubgroup_of_mem_principalSet`: for `a > 0`, every
  matrix in `principalSet F n a` is the underlying matrix of an element of `K_a`.
- `det_inverseTranspose_eq`: `det (ι y) = (det y)⁻¹` in `F^×`.
- `inverseTranspose_scalar_eq`: `ι (z · 1) = z⁻¹ · 1` for `z ∈ F^×`.
- `coefficientIota_eq_of_fourierIntegral_ne_zero`: suppose `ψ` has conductor
  exponent `0`, `1 ≤ m'` and `2m' ≤ a(χ)`, and suppose
  `f : GL_(n+1)(F) → ℂ` satisfies `f(z · y) = ω(z) χ(det y) f(1)` for all
  `z ∈ F^×` and `y ∈ K_(m')`. Take `j = twistLevel (a(χ))` and
  `Φ = twistedPrincipalFun F χ j`. Then every `g` with `Φ^(g) ≠ 0` satisfies
  `GodementJacquet.coefficientIota f g = f(1) · twistedEpsilonWeight F χ ω g`,
  that is `f(ι g) = f(1) ω(g₀₀)⁻¹ χ(g₀₀)^(n+1) χ(det g)⁻¹`, and
  `ord(det g) = -(n+1) a(χ)`, so `|det g| = q^((n+1) a(χ))`. Here `ord` is
  `PadicField.TopologicalData.ord`, the integer `-log v`.

## Proof outline

The first-order determinant expansion writes `Z = ϖ^j M` with `M` integral and
applies Mathlib's `Matrix.det_one_add_smul` over the integer ring. The
remainder is `ϖ^(2j)` times an integer. The translation law follows from
this: the ratio `det(y + a) / (det y · (1 + tr a))` is a principal unit of
level `2j ≥ a(χ)`, so `χ` is trivial on it. Translation invariance of the
additive Haar measure (`integral_add_left_eq_self`) then gives the Fourier
identity.

For the support, take matrix units in that identity. Off-diagonal entries `x_(r,c)`
satisfy `ψ(t · x_(r,c)) = 1` for all `t ∈ ϖ^j O`. Since `ψ` has conductor
exponent `0`, this gives `x_(r,c) ∈ ϖ^(-j) O`. In the same way, each `x_(r,r) - x₀₀`
lies in `ϖ^(-j) O`. On `ϖ^k O` with `k = a(χ)`, `χ(1 + t) = 1`, so
`ψ(t · x₀₀) = 1` and `x₀₀ ∈ ϖ^(-k) O`. Conductor minimality gives a unit
`w ∈ 1 + ϖ^(k-1) O` with `χ(w) ≠ 1`, so `x₀₀ ∉ ϖ^(-(k-1)) O`. Hence
`v(x₀₀) = exp k`, and dividing by `x₀₀` puts every entry of `x₀₀⁻¹ x - 1` in
`ϖ^(k-j) O`.

For the dual side, write `k = a(χ)`. From `1 ≤ m'` and `2m' ≤ k` we get
`j = (k+1)/2` (`twistLevel_eq`), `j < k ≤ 2j` and `m' ≤ k - j`. The support
lemma gives `v(g₀₀) = exp k` and `g₀₀⁻¹ g ∈ 1 + ϖ^(k-j) M(O)`. Since `k - j > 0`,
the second fact gives an element `y ∈ K_(k-j)` with `g = z · y`, where `z = g₀₀`.
The bridge between the two descriptions of the level is the Library's
`UnequalRankMirabolicUnitTest.exists_mem_principalLevelSubgroup` together with
`RankOneBox.levelSet_eq_additiveLattice`. Then
`ι g = z⁻¹ · ι y`. Here `ι y ∈ K_(k-j) ⊆ K_(m')`, by
`Conductor.inverseTranspose_mem_principalLevelSubgroup` and
`Conductor.principalLevelSubgroup_antitone`, so the hypothesis on `f` gives
`f(ι g) = ω(z)⁻¹ χ(det ι y) f(1)`. Finally, `det ι y = (det y)⁻¹` and
`det g = z^(n+1) det y` (Mathlib's `Matrix.GeneralLinearGroup.det_scalar`), so
`det ι y = z^(n+1) (det g)⁻¹`. This gives the first identity. For the order,
`det y = det(1 + Y)` with `Y ∈ ϖ^(k-j) M(O)` is a valuation unit
(`valuation_det_one_add`). So `v(det g) = v(g₀₀)^(n+1) = exp((n+1)k)`, and
`ord(det g) = -(n+1)k`.

## Provenance

The test is the Godement–Jacquet adaptation of Jacquet–Shalika, *A lemma on
highly ramified ε-factors*, Math. Ann. 271 (1985), §2.5 (printed pages
321–322; registered source `jacquet-shalika-1985-ramified-factors`).
JS85 set `K_j = 1 + ϖ^j M_r(O)` with `j = ⌈k/2⌉` (§2.5 (2)). They observe that
`det(1 + a) ≡ 1 + Tr(a)` modulo `ϖ^(2j)`, so that `χ(det h) = ψ(Tr(c a))` for
`h = 1 + a ∈ K_j` and a suitable `c ∈ ϖ^(-k) O` (§2.5 (3), (4)). The inner
integral over `K_j / K_k` then vanishes unless `g x ∈ c K_(k-j)`.

JS85 use the Fourier transform of `f(x⁻¹) χ(det x)⁻¹ φ(det x)` for a
`GL_1`-pair test `φ`. Here the test `1_{K_j} χ⁻¹(det)` lives directly on full
matrices. The implemented proof never constructs JS85's element `c`: it
derives the support from translation invariance alone, with `x₀₀` playing
the role of `c`. The level `max 1 ⌈k/2⌉` agrees with JS85's `j` for `k ≥ 1`.

The dual-side identity corresponds to JS85 §2.5 (9)–(12) (printed page 322).
For `g ∈ c K_(k-j)`, they evaluate their Fourier transform as `f(g) χ(det g)`
times `|det g|^(-r)` and an explicit constant `ω⁻¹(c) χ⁻¹(c^r) η(χ, r)`. This
uses only that the matrix coefficient `f` is bi-invariant under `K_i` with
`i < k - j`. Here the transform sits on the test, not on the coefficient, so the
analogous step evaluates `f(ι g)` on the support. The Lean hypothesis on `f`
(centre by `ω`, `K_(m')` by `χ ∘ det`) is the form the epsilon module supplies.
The weight `twistedEpsilonWeight`, with `g₀₀` in place of JS85's `c`, plays the
role of their `ω⁻¹(c) χ⁻¹(c^r)` factor.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
