# Splitting of dual Whittaker functions at an unramified place, through the contragredient

Module `Langlands.Global.RankinSelberg.ContragredientDualSplit`, namespace
`Langlands.Global.RankinSelbergGlobal.ContragredientDualSplit`.

Let `T` be an actual cuspidal realization, `Td` a realization of its contragredient and
`Pd` a spectral presentation of `Td`. This module proves that the dual
`W̃(g) = W(w ᵗg⁻¹)` of the Whittaker function `W` of a vector of `T` spherical outside
`S` splits at every finite `v ∉ S` where `ψ_v` has conductor `𝒪_v`. The local factor is
the spherical Whittaker function of the Satake parameter `a` of `Pd` at `v`, with the
inverse character. The Library's `UnequalDualEulerFactorizationReduction` derives this
splitting from the open premise `ContragredientDualWhittakerStatement`, which supplies a
vector of `Td` with Whittaker function `W̃`. Here it is proved without that statement and
without any vector of `Td`. It uses only the Hecke action of `T` at `v`.

Notation: `ι_v(h) = localPoint F n v h`, `g_v = finiteComponent F n v g`, `w` the long
Weyl element, `ᵗg⁻¹ = inverseTranspose g`, `ϖ = placeUniformizer v` (through
`LocalPointFactorization.isUniformizingElement_canonical v`), `q_v` the residue
cardinality, and `W°(h; a)` (`UnequalDualEuler.sphStd v ψ_v r a`) and `W°⁻(h; a)`
(`UnequalDualEuler.sphInv v ψ_v r a`) the Library spherical Whittaker functions at `ϖ`
with the standard and the inverse standard character of `ψ_v`.

## Main results

- `dualWhittaker_split`. Let `Td.realization.IsContragredientOf T.realization`,
  `Pd : CuspidalSpectralPresentation Td` with `Pd.exceptional ⊆ S`, and `x` spherical
  outside `S`. Let `v ∉ S`, and let `ψ_v` be the canonical finite additive component of `ψ`
  at `v` with additive conductor `0`. Let `a` be a tuple whose multiset is the presented
  spectrum of `Pd` at `v`. Then for every `g` with `g_v = 1` and every `h`:
  - `W̃(g ι_v(h)) = W̃(g) W°⁻(h; a)` for `W̃ = dualFunction (cuspWhittaker F T ψ x)`;
  - `W̃(g ι_v(h)) = W̃(g) W°(h; a)` for `W̃ = dualFunction (cuspWhittaker F T ψ⁻¹ x)`.

## Auxiliary results

Local duality (section `Local`, over a valued field `K` with uniformizer `ϖ`):

- `sphericalWhittaker_weylLong_mul_inverseTranspose`. Let `θ`, `θ'` be integrally
  trivial characters of the upper unipotent group with `θ(w₀ ᵗu⁻¹ w₀) = θ'(u)`
  (`Whittaker.reflectedUnipotent`). Then `W°_θ(w₀ ᵗg⁻¹; x) = W°_θ'(g; x⁻¹)`. The function
  `f(g) = W°_θ(w₀ ᵗg⁻¹; x)` is `(N, θ')`-equivariant and right `GL(𝒪)`-invariant. On the
  torus, `w₀ ϖ^(-λ) = ϖ^(λ*) w₀` with `λ*_i = -λ_(n-1-i)` (`dualWeight`). Hence
  `f(ϖ^λ) = W°_θ(ϖ^(λ*); x)`. This is `δ^(1/2)(ϖ^λ) s_λ(x⁻¹)` for antitone `λ` and `0`
  otherwise, by `antitone_dualWeight_iff`, `halfModulus_dualWeight` and `satakeSchur_inv`.
  Uniqueness of such functions (`eq_cellFunction`, `cellFunction_congr`) gives
  `f = W°_θ'(·; x⁻¹)`.

Global points (section `Points`):

- `finiteComponent_weylLong`: `(w)_v = w_v`.
- `finiteComponent_dualPoint`: `(w ᵗg⁻¹)_v = w_v` when `g_v = 1`.
- `dualPoint_mul_localPoint`: `w ᵗ(g ι_v(h))⁻¹ = (w ᵗg⁻¹) ι_v(ᵗh⁻¹)`.
- `dualFunction_mul_localPoint`. If `W(g ι_v(h)) = W(g) φ(h)` whenever `g_v = 1`, and
  `φ(w_v) = 1`, then `W̃(g ι_v(h)) = W̃(g) φ(w_v ᵗh⁻¹)` whenever `g_v = 1`. Write
  `w ᵗg⁻¹ = p ι_v(w_v)` with `p_v = 1`.

Splitting through Hecke scalars (section `Global`):

- `ofTuple_map_inv`: the multiset of `a⁻¹` is the multiset of `a` inverted.
- `cuspWhittaker_mul_localPoint_of_corner`. This is the statement of the Library's
  `UnramifiedWhittaker.cuspWhittaker_mul_localPoint`, with a hypothesis on the standard
  Hecke scalars of the spherical vectors of `T` at `v` in place of a spectral
  presentation of `T`. For `x` fixed by `GL_(r+1)(𝒪_v)`, `g_v = 1` and a character `θ` of
  the local unipotent group that agrees with the global generic character:
  `W_x(g ι_v(h)) = W_x(g) W°_θ(h; a)`. The proof is the Library's: the Whittaker functional
  at `g` is a local `θ`-Whittaker functional, and
  `UnramifiedWhittaker.coefficientMap_eq_smul_of_corner` gives Shintani's formula.
- `whittaker_split_of_corner`. The two halves of `UnramifiedWhittakerFactorizationStatement`
  at `ϖ` (for `ψ` and for `ψ⁻¹`), for `x` spherical outside `S`, `v ∉ S`, `ψ_v` of
  conductor `𝒪_v`, and the Hecke scalars of `T` at `v` given by the tuple `a`.
- `sphStd_inv_weylLong_mul_inverseTranspose`: `W°(w_v ᵗh⁻¹; a⁻¹) = W°⁻(h; a)`.
  `sphInv_inv_weylLong_mul_inverseTranspose`: `W°⁻(w_v ᵗh⁻¹; a⁻¹) = W°(h; a)`. Both are
  local duality, with `Whittaker.standardCharacter_reflected` and
  `Whittaker.inverseStandardCharacter_reflected`.
- `sphStd_weylLong`, `sphInv_weylLong`: `W°(w_v; a) = W°⁻(w_v; a) = 1`, because `w_v` is
  integral.

## Proof of `dualWhittaker_split`

By `CuspidalOperatorRealization.corner_eq_smul_of_contragredient_presentation` (module
`Langlands.Automorphic.ContragredientHeckeTransfer`) and `ofTuple_map_inv`, every
spherical vector of `T` at `v` has the standard Hecke scalars of `a⁻¹`. So
`whittaker_split_of_corner` gives `W(g ι_v(h)) = W(g) W°(h; a⁻¹)` for the `ψ`-Whittaker
function and `W(g ι_v(h)) = W(g) W°⁻(h; a⁻¹)` for the `ψ⁻¹`-Whittaker function, when
`g_v = 1`. `dualFunction_mul_localPoint`, with `sphStd_weylLong` and `sphInv_weylLong`,
turns these into `W̃(g ι_v(h)) = W̃(g) W°(w_v ᵗh⁻¹; a⁻¹)` and
`W̃(g) W°⁻(w_v ᵗh⁻¹; a⁻¹)`. Local duality rewrites the factors as `W°⁻(h; a)` and
`W°(h; a)`.

## Provenance

Cogdell 2004 (J. W. Cogdell, *Analytic theory of L-functions for GL_n*, registered as
`cogdell-2004-analytic-theory-gln`, PDF page = printed page + 3), §2.2, printed p.207,
states that `W̃(g) = W(w_n ᵗg⁻¹)` lies in the `ψ⁻¹`-Whittaker model of `π̃`. Shintani's
formula is on p.206. At an unramified place this gives the splitting above, with the
normalized spherical function of `π̃_v`. The relation `W°(w ᵗg⁻¹; x) = W°⁻(g; x⁻¹)` is the
classical local identity for the normalized unramified Whittaker function. Cogdell uses it
with the local functional equation (Theorems 3.2–3.3, printed pp.214–215). The route
here is internal: Hecke scalars of `T` from the presentation of `Td`
(`ContragredientHeckeTransfer`), Shintani's formula for `T` with parameter `a⁻¹`, then
local duality. It avoids the multiplicity-one input of the Library's
`ContragredientDualWhittakerReduction`.
