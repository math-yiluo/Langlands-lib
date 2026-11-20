# Open subgroups of `GL_n(𝔸_K,f)` and induction over local factors

Author: Worker 3657.

Lean module: `Langlands.Global.FiniteAdelicGL.OpenSubgroupInduction`. It
imports `Langlands.Global.FiniteAdelicGL.RestrictedProduct` and
`Langlands.Representation.Smooth.Definitions` and changes no published file.

`K` is a number field and `n : ℕ`. `FiniteAdelicGL K n` is `GL_n(𝔸_K,f)`
with its restricted-product topology, `localProjection K n v` and
`localInclusion K n v` are the projection to and the inclusion of the local
factor `GL_n(K_v)` at a finite place `v`, and `localIntegral K n v` is the
subgroup `GL_n(𝒪_v)`. These are the Library's names from
`Langlands.Global.FiniteAdelicGL.RestrictedProduct`.

## Declarations

- `ofIntegral y`: the finite adelic matrix with local components
  `y v ∈ GL_n(𝒪_v)`, i.e. `fromRestrictedProduct` applied to the structure
  map `∏_v GL_n(𝒪_v) → ∏'_v GL_n(K_v)`.
  `localProjection_ofIntegral`: its component at `v` is `y v`.
  `continuous_ofIntegral`: it is continuous for the product topology on
  `∏_v GL_n(𝒪_v)` (Mathlib's `RestrictedProduct.isEmbedding_structureMap`
  composed with the Library's `continuous_fromRestrictedProduct`).
- `exists_finset_forall_mem L`: for every open subgroup `L` there is a finite
  set `T` of finite places such that `L` contains every `ℓ` with
  `localProjection v ℓ ∈ GL_n(𝒪_v)` for all `v` and
  `localProjection v ℓ = 1` for `v ∈ T`.
- `localProjection_inv_localInclusion_mul_of_ne`,
  `localProjection_inv_localInclusion_mul_self`: the components of
  `(ι_v g)⁻¹ d` are `d_w` at `w ≠ v`, and `1` at `v` when `g = d_v`.
- `induction_localInclusion P L hL hstep d`: if `P` holds on the open
  subgroup `L` and `P d → P (ι_v(g) * d)` for all `v`, `g`, `d`, then `P d`
  for every `d`.
- `eventually_fixed_localIntegral hρ x`: for a smooth representation `ρ` of
  `GL_n(𝔸_K,f)` (Library `Langlands.IsSmooth`: every vector has an open
  stabilizer), every vector `x` is fixed by `ι_v(GL_n(𝒪_v))` for all but
  finitely many `v`.

## Proofs

- `exists_finset_forall_mem`: the preimage of `L` under `ofIntegral` is an
  open set of the product `∏_v GL_n(𝒪_v)` containing `1`, so by
  `isOpen_pi_iff` it contains a basic open box `∏_{v∈I} u_v × ∏_{v∉I}`
  (everything) around `1`, with `I` finite. Take `T = I`. For `ℓ` as in the
  statement, the family `y v = ℓ_v` lies in the box (it is `1` on `I`) and
  `ofIntegral y = ℓ` (`ext_localProjection`), so `ℓ ∈ L`.
- `induction_localInclusion`: let `T` be as above for `L`. By finset
  induction on `S`, `P d` holds whenever every `v ∉ S` has `d_v ∈ GL_n(𝒪_v)`
  and `d_v = 1` if `v ∈ T`: for `S = ∅` this is `d ∈ L`; for `insert w S`
  write `d = ι_w(d_w) * ((ι_w(d_w))⁻¹ d)`, where the second factor has
  component `1` at `w` and the same components as `d` elsewhere, and use
  `hstep`. Apply this to `S = T ∪ {v | d_v ∉ GL_n(𝒪_v)}`, which is finite by
  the Library's `eventually_localIntegral`.
- `eventually_fixed_localIntegral`: the stabilizer `L` of `x` is open; take
  `T` for `L`. For `v ∉ T` and `g ∈ GL_n(𝒪_v)`, `ι_v(g)` has component `g` at
  `v` and `1` elsewhere, hence lies in `L`.

## Provenance

The Lean arguments derive consequences of the restricted-product topology
on `GL_n(𝔸_K,f)`. Example 2 and the proof of Theorem 2 in Flath,
*Decomposition of representations into tensor products* (1979), p. 181
(PDF p. 177), use products of compact open subgroups to study smooth
representations of the restricted product. The registered source is
`flath-1979-tensor-products`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

## Use

`Langlands.Automorphic.OperatorSubquotientPlaceGeneration` reduces finite
adelic translations to local translations with `induction_localInclusion`.
`eventually_fixed_localIntegral` gives the smoothness hypothesis of
`Langlands.CommutingFamily.exists_linearEquiv_of_isotypic` at the finite
places.

## Check

The draft Lake build `cc2bf284` with `OperatorSubquotientPlaceGeneration`
reported zero errors and zero warnings.
