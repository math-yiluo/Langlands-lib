# The local Weil transfer square in a tower of embeddings

Module `Langlands.ClassFieldTheory.Local.WeilTransferReciprocityTower`, namespace
`Langlands.LocalClassField`.

## Setting

`F : PadicField.{u} p`, `K : PadicField.{v} p` and `E : PadicField.{w} p` are p-adic
field packages with `Padic p`-algebra embeddings `fK : F → K`, `fE : F → E` and
`g : K → E`. The Library attaches to each embedding `f : F → L` a chosen embedding
`extensionFieldEmbedding F L f : L → F̄` into the algebraic closure of `F`, a chosen
isomorphism of algebraic closures `extensionClosureLift F L f : F̄ → L̄`, and the
injective maps `extensionGaloisMap F L f : G_L → G_F` and
`extensionWeilMap F L f : W_L → W_F` built from that isomorphism. The tower is
*compatible* if

  `hg : ∀ x, extensionFieldEmbedding F E fE (g x) = extensionFieldEmbedding F K fK x`,

that is, `K` and `E` sit inside `F̄` so that `g` becomes an inclusion. The Galois and
Weil maps of `fE` and of `fK ∘ g` still need not agree, because the three closure
isomorphisms are chosen independently; this module measures the difference.

`N` denotes the subgroup `(extensionWeilMap F E fE).range.comap (extensionWeilMap F K fK)`
of `W_K`: the elements whose image in `W_F` lies in the image of `W_E`. On `N`,
`InductionAlong.rangeInverse` of `extensionWeilMap F E fE` composed with
`subgroupComap` gives a homomorphism `N → W_E`. `R_K` and `R_E` are
`LocalFactor.RankOne.reciprocityUnits` for reciprocity candidates `eK`, `eE`.

## Statements

Conjugation (section `Conjugation`, for one field `K`):

- `profiniteIntegers_mul_comm`: `ProfiniteIntegers` is commutative (the integers
  are dense in it).
- `localResidueDegree_conj`: `localResidueDegree K (γ σ γ⁻¹) = localResidueDegree K σ`.
- `weilConj K γ : W_K →* W_K`, `(σ, m) ↦ (γ σ γ⁻¹, m)` for `γ ∈ G_K`, with
  `localProjection_weilConj`, `localDegree_weilConj`, `weilConj_weilConj`,
  `weilConj_one`, `weilConj_inv_weilConj`, `weilConj_weilConj_inv`,
  `weilConj_localProjection` (for `γ` the image of `v ∈ W_K`, `weilConj` is
  `w ↦ v w v⁻¹`) and `continuous_weilConj_apply` (continuity in `γ`).
- `projection_weilConj`: `weilConj K γ y` and `y` have the same image in
  `WeilQuotients.projection (localResidueDegree K)`, the quotient by the closed
  commutator subgroup.
- `reciprocityUnits_weilConj`: `R_K (weilConj K γ y) = R_K y` for every reciprocity
  candidate; no property of the candidate is used.

Tower (section `Tower`):

- `comp_apply_eq_of_fieldEmbedding`: `hg` implies `g (fK x) = fE x`.
- `towerClosureAut F K E fK fE g hgf ∈ G_F`: the automorphism
  `(extensionClosureLift F E fE)⁻¹ ∘ extensionClosureLift K E g ∘ extensionClosureLift F K fK`
  of `F̄`, with `extensionClosureLift_towerClosureAut`.
- `exists_extensionGaloisMap_tower` (from `hg`): there is `γ ∈ G_K` with
  `extensionGaloisMap F E fE σ = extensionGaloisMap F K fK (γ * extensionGaloisMap K E g σ * γ⁻¹)`
  for all `σ ∈ G_E`.
- `extensionWeilMap_weilConj_tower`: for such `γ`,
  `extensionWeilMap F K fK (weilConj K γ (extensionWeilMap K E g x)) = extensionWeilMap F E fE x`.
- `mem_range_iff_weilConj_mem`: `l` is in the image of `extensionWeilMap K E g` if
  and only if `weilConj K γ l ∈ N`.
- `transfer_weilConj_tower`: the transfer to `N` of `R_E ∘ (N → W_E)` at
  `weilConj K γ y` equals the transfer to the image of `extensionWeilMap K E g` of
  `R_E ∘ rangeInverse` at `y`.
- `extensionWeilTransferReciprocity_tower` (main theorem): assume
  `hsq : ExtensionWeilTransferReciprocityStatement.{v, w}`, the compatibility `hg`,
  and `GeometricWeilReciprocityRelation` for `eK` and `eE` (canonical topological
  data). Then for every `y : W_K`

  `MonoidHom.transfer (R_E ∘ rangeInverse (extensionWeilMap F E fE) ∘ (extensionWeilMap F K fK).subgroupComap _) y = Units.map g (R_K y)`.

  The finite-index instance on `N` is `extensionWeilMap_range_finiteIndex F E fE`
  (Mathlib's comap instance gives it on `N`), and the topologies are those of the
  canonical topological data.
- `exists_fieldEmbedding_tower`: if
  `extensionIntermediateField F K fK ≤ extensionIntermediateField F E fE`, a
  compatible `g : K →ₐ[Padic p] E` exists.

## Provenance

The square for a single embedding is the published
`ExtensionWeilTransferReciprocityStatement` (Serre, *Local Fields*, Chapter XI, §3,
diagram (2), printed p.170; see its Markdown). This module adds no new arithmetic
input: it is internal infrastructure, written for this project, that transports the
published square to the subgroup `N` cut out by a compatible tower `F → K → E`. That
is the form needed for the transfer part of the local restriction formula for
relative Weil groups (Tate, *Number theoretic background*, (1.6.1), (2.3.5)), where
the local fields come from completions with independently chosen closure
embeddings. `profiniteIntegers_mul_comm` and the conjugation lemmas are standard
facts proved here because the Library does not contain them.

## Proof

`profiniteIntegers_mul_comm` uses `ProfiniteGrp.ProfiniteCompletion.denseRange` twice:
the two sides are continuous in each variable and agree on the image of the integers.
`localResidueDegree_conj` follows from it. `weilConj` is the product map
`MulAut.conj γ × id` restricted to the pullback subgroup; the residue degree
condition is preserved by `localResidueDegree_conj`. The algebraic lemmas are
`projection_injective` followed by `group`.

`projection_weilConj`: let `C` be the topological closure of the commutator subgroup.
The set of `δ ∈ G_K` with `(weilConj K δ y)⁻¹ y ∈ C` is closed (preimage of a closed
set under a continuous map, by `continuous_weilConj_apply`). It contains the image of
`W_K` (`localProjection_denseRange` is dense): for `δ = localProjection v`,
`(v y v⁻¹)⁻¹ y = ⁅v, y⁻¹⁆` lies in the commutator subgroup. So it is all of `G_K`,
and `QuotientGroup.eq` gives the equality of classes. `reciprocityUnits_weilConj`
unfolds `reciprocityUnits` to the candidate applied to that class.

`exists_extensionGaloisMap_tower`: `towerClosureAut` fixes the image of `K` in `F̄`
(`mem_extensionIntermediateField`, `extensionClosureLift_fieldEmbedding` and `hg`), so
by `extensionGaloisMap_range` it equals `extensionGaloisMap F K fK γ` for some `γ`.
The identity `ι_{fE}(σ) τ = τ ι_{fK}(ι_g σ)`, with `τ = towerClosureAut`, is checked
after applying the injective `extensionClosureLift F E fE`, using
`extensionClosureLift_galoisMap` three times and `extensionClosureLift_towerClosureAut`
twice. The Weil statement follows on Galois components through `projection_injective`
(degrees agree by definition).

`transfer_weilConj_tower` applies `GroupTheory.Transfer.transfer_comp_eq_prod_of_conj`
(module `Langlands.GroupTheory.TransferDoubleCoset`) to `ψ = weilConj K γ` and
`H = N`, with a single double coset (`ι = Unit`, representative `1`) and stabilizer
the image of `extensionWeilMap K E g` (by `mem_range_iff_weilConj_mem`). Covering
holds because `weilConj K γ` is bijective. The required identity of the coefficient
maps reduces, after `rangeInverse_apply` and injectivity of `extensionWeilMap F E fE`,
to `extensionWeilMap_weilConj_tower`.

`extensionWeilTransferReciprocity_tower`: take `γ` from
`exists_extensionGaloisMap_tower` and apply `transfer_weilConj_tower` at
`weilConj K γ⁻¹ y`. This rewrites the left side as the transfer for the single
embedding `g` at `weilConj K γ⁻¹ y`. `hsq` for `K`, `E`, `g` turns it into
`Units.map g (R_K (weilConj K γ⁻¹ y))`, and `reciprocityUnits_weilConj` removes the
conjugation.

`exists_fieldEmbedding_tower` composes `extensionIntermediateFieldEquiv` for `K`,
`IntermediateField.inclusion` and the inverse of `extensionIntermediateFieldEquiv` for
`E`. It is a `Padic p`-algebra map because both field embeddings into `F̄` are
`Padic p`-linear (`extensionFieldEmbedding_comp` together with `fK.commutes` and
`fE.commutes`).
