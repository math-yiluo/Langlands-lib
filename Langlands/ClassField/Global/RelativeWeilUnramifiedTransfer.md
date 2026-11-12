# The transfer at a local relative Weil map of ramification index one

Author: Worker 5137.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.presentedDeterminantMultipleAssociation`
computes the transfer `W_{E/F} → C_F` on the image of a Frobenius-type element under a
local relative Weil map, at a place of ramification index one. Classically
(Tate, *Number theoretic background*, §1; Weil, *Sur la théorie du corps de classes*),
the composite `W_{F_z} → W_{E/F} → W_{F/F} = C_F` is the local reciprocity map followed
by the inclusion `F_zˣ → C_F`; here only the consequence needed for twisting is proved,
directly from the defining properties of `IsLocalRelativeWeilMap`, without local class
field theory beyond what that predicate already supplies.

## `Langlands.Weil.Local.ord_reciprocityUnits_of_localDegree_eq_one`

If `eF` is a reciprocity candidate satisfying the geometric Weil reciprocity relation
`heF` for a p-adic field `F`, and `g ∈ W_F` has degree one, then the reciprocity unit
`reciprocityUnits F eF g` has normalized order one. The first component of `heF` says
that the order of the reciprocity unit equals the degree of `g`.

## Places above `z` (section `Places`)

Here `z` is a finite place of `F` and `placeEmbedding z u : E → \bar{F_z}` is the
embedding of `E` through the completion at a place `u` above `z`.

- `finitePlaceEquiv_eq_of_placeEmbedding`: if `σ ∈ Gal(E/F)`, places `u, u'` above `z`
  and `ρ ∈ G_{F_z}` satisfy `placeEmbedding z u ∘ σ = ρ ∘ placeEmbedding z u'`, then
  `σ` moves `u` to `u'` (`finitePlaceEquiv σ u = u'`). Proof: set `q = σ*u`; composing
  the completed transport `E_q → E_u` with the closure embedding at `u` and with
  `ρ⁻¹` gives an `F_z`-embedding of `E_q`, which by
  `exists_eq_comp_completionClosureEmbedding` is the closure embedding at `q` followed by
  some `τ ∈ G_{F_z}`; then `eq_of_placeEmbedding_eq` identifies `q` with `u'`.
- `completionClosureEmbedding_finiteCompletionEquiv`: under the same compatibility (with
  `u' = σ*u`), the completed transport `E_{σ*u} → E_u` followed by the closure embedding
  at `u` is the closure embedding at `σ*u` followed by `ρ`. Both sides are
  `F_z`-algebra maps that agree on the image of `E`, which generates the completion
  (`subalgebra_eq_top_of_algebraMap_mem` applied to their equalizer).
- `exists_ofAdicCompletion_eq_of_eq`: reading a unit at a place `w` as a unit at an
  equal place `q` (a `subst` bookkeeping lemma).

## `ofAdicCompletion_injective`

The map `E_wˣ → C_E` sending a local unit to the class of the idele with that component
at `w` and `1` elsewhere is injective. If such an idele is principal, `x ∈ Eˣ`, then the
infinite component shows that `x = 1` (the map `E → E_∞` is injective), and then the
`w`-component shows that the unit is `1` (`ideleCoordinate_ofAdicCompletion_self`).

## Descent (section `Descent`)

`exists_completionMap_eq_of_ideleClassEquiv`: let `w` lie over `z` with ramification
index one (`he`), let `y ∈ W_{F_z}` have degree one (`hy`), let `σ ∈ Gal(E/F)` satisfy
`placeEmbedding z w ∘ σ = ρ ∘ placeEmbedding z w` for the Galois image `ρ` of `y`
(`hσ`), and let `b ∈ E_wˣ` have an idele class fixed by `σ` (`hb`). Then `b` comes from
`F_z`.

- `σ` fixes `w` (first lemma of section `Places`); by injectivity of
  `E_wˣ → C_E`, the completed transport of `σ` fixes `b`; hence
  `β = completionClosureEmbedding z w b ∈ \bar{F_z}` is fixed by `ρ`.
- `β` lies in the image of `E_w`, so it is fixed by the image of `G_{E_w}`
  (`extensionGaloisMap_range`, `mem_extensionIntermediateField`).
- Every `g ∈ W_{F_z}` is `y ^ d · h` with `d` the degree of `g` and `h` of degree zero;
  by `mem_completionWeilMap_range_iff` (ramification index one) `h` comes from
  `W_{E_w}`. So the Galois image of every element of `W_{F_z}` fixes `β`.
- Every element `τ ∈ G_{F_z}` differs from the image of some `ℓ ∈ W_{F_z}` by an
  element fixing the image of `E`, hence by an element of the image of `G_{E_w}`
  (`exists_localProjection_placeEmbedding`, `placeEmbedding_fixed_iff`); therefore `τ`
  fixes `β`.
- By infinite Galois theory (`InfiniteGalois.mem_range_algebraMap_iff_fixed`), `β`
  comes from `F_z`, and injectivity of the closure embedding gives `a ∈ F_z` with
  `completionMap z w a = b`.

## The transfer (section `Transfer`)

`exists_transfer_eq_inv_ofAdicCompletion`: let `E / F` be Galois, `c` a class family with
`FundamentalClass.Restriction c` (`h`), `w` a place of `E` above `z` with ramification
index one (`he`), and `ι : W_{F_z} →ₜ* W_{E/F}` a local relative Weil map for `w` with
reciprocity candidate `e` (`hι : IsLocalRelativeWeilMap z w e ι`). For every
`y ∈ W_{F_z}` of degree one there is `a ∈ F_zˣ` with `v(a) = exp (-1)` and
`transfer c F E (ι y) = [a]_z⁻¹`.

Proof, with `f` the residue degree of `E_w / F_z`:

1. `y ^ f` has degree `f`, so by `mem_completionWeilMap_range_iff` it is the image of
   some `h₀ ∈ W_{E_w}`, of degree one. Let `b` be the reciprocity unit of `h₀` and
   `X = [b]_w ∈ C_E`. The third component of `hι` gives `ι (y ^ f) = X⁻¹` in `W_{E/F}`.
2. `ι y` commutes with `ι (y ^ f) = X⁻¹`, so conjugation by `ι y` fixes `X`; through
   `conjugation` this says that `σ = projection (ι y)` fixes `X` in `C_E`. The second
   component of `hι` is the compatibility `hσ`, so the descent lemma gives
   `a ∈ F_zˣ` mapping to `b`.
3. `b` has order one (`ord_reciprocityUnits_of_localDegree_eq_one`, as `h₀` has degree
   one); since the ramification index is one, `v(a) = v(b) = exp (-1)`
   (`discreteValuation_padicFieldAt`, `FiniteExtension.valuation_completionMap`).
4. It remains to show that the inclusion `C_F → C_E` sends `[a]_z⁻¹` to the transfer
   `W_{E/F} → C_E` of `ι y` (`eq_transfer_of_ideleClassInclusion_eq`,
   `ideleTransfer_apply`). The double cosets `C_E \ W_{E/F} / ι(W_{F_z})` are indexed by
   the places `u` above `z`, with representatives `x u = placeRepresentative c E z w u`
   (covering `exists_eq_mul` and disjointness `place_eq_of_mul_eq` from the Library,
   with `mem_range_restrictionInclusion_self_iff`). The Library double-coset formula
   `Langlands.GroupTheory.Transfer.transfer_comp_eq_prod_of_normal` (for the normal
   subgroup `C_E`) writes the transfer of `ι y` as the product over `u` of the
   transfers at `y` of the characters `ℓ ↦ (x u)⁻¹⁻¹ ι(ℓ) (x u)⁻¹` of
   `ι⁻¹(C_E)`.
5. `ι⁻¹(C_E)` is the set of elements of `W_{F_z}` whose degree is divisible by `f`
   (`mem_ideleClassSubgroup_iff` and `mem_completionWeilMap_range_iff`), so
   `transfer_eq_of_degree` from `TransferCyclicQuotient` evaluates each factor at
   `y ^ f`: the factor at `u` is `σ_u(X)⁻¹`, where `σ_u = projection (x u)`.
6. Each `σ_u` moves `u` to `w`, and exactly one `u` is moved to `w` for each place `q`
   above `z`; so the Library lemma `prod_relativeIdeleClassAut_ofAdicCompletion` gives
   `∏ σ_u(X) = [a]_z` in `C_E`, and the product of the inverses is `[a]_z⁻¹`.
