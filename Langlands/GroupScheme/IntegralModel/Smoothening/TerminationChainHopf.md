# Termination of the smoothening sequence: Hopf structure on the members

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. In the source each
dilatation is again a group scheme (Proposition A.5.3). Here the corresponding statement is proved
for subalgebras of `B = integralFunctions R K A`. The argument is internal to this project and
follows the construction of the Hopf structure on `B` in Worker 50's module `Smoothening.Hopf`.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

Setting: `R` is a discrete valuation ring with fraction field `K`, and `A` is a commutative Hopf
algebra over `R`. `S` is a subalgebra of `B`.

## Generalities on subalgebras of `B`

- `subIsTorsionFree` and `subFlat` (instances): `S` is torsion-free, hence flat over the Dedekind
  domain `R` (`IsDedekindDomain.flat_iff_torsion_eq_bot`).
- `inclSub S hS : A →ₐ[R] S` is the inclusion of `A`, given `hS : (incl R K A).range ≤ S`, with
  `val_inclSub`.
- `algHom_ext_sub`: two algebra maps from `S` to a flat `R`-algebra that agree on the image of `A`
  are equal. For `s ∈ S` there is `r ≠ 0` with `r s` in the image of `A`
  (`exists_smul_eq_one_tmul`), and flat targets are torsion-free.
- `tensorVal : S ⊗ S → B ⊗ B` is the map induced by the inclusion. It is injective
  (`tensorVal_injective`, `TensorProduct.map_injective_of_flat_flat`), and its range contains
  `pureSpan R K A S S` (`pureSpan_le_range`).

## The structure maps

Assume `hcomul`: the comultiplication of `B` maps `S` into `pureSpan R K A S S`. Assume `hanti`:
`S` is stable under the antipode `antipodeInt` of `B`.

- `comulSub S hcomul : S →ₐ[R] S ⊗ S` is the comultiplication of `B` restricted to `S`, pulled
  back along the injective map `tensorVal`. The lemma `tensorVal_comulSub` gives its value.
- `counitSub S` is the counit of `B` restricted to `S`.
- `antipodeSub S hanti` is the antipode of `B` restricted to `S`.
- `comulSub_comp_inclSub`, `counitSub_comp_inclSub` and `antipodeSub_inclSub` (with linear map
  variants): on the image of `A` the structure maps are those of `A`.
- `bialgSub S hS hcomul : Bialgebra R S` is built with `Bialgebra.ofAlgHom`. Coassociativity and
  the counit laws hold after composition with `inclSub`, because they hold for `A`
  (`coassoc_simps`). They then hold everywhere by `algHom_ext_sub`, since `S ⊗ S` is flat.
- `hopfSub S hS hcomul hanti : HopfAlgebra R S` is built with `HopfAlgebra.ofAlgHom`. The antipode
  laws are checked on the image of `A` using Worker 50's `lift_antipodeAlgHom_comp_comul` and
  `lift_id_antipodeAlgHom_comp_comul`.
- `chainHopf hϖ n : HopfAlgebra R (chain R K A ϖ n)` applies this to the members of the smoothening
  sequence, using `range_incl_le_chain`, `comul_mem_pureSpan` and `antipodeInt_mem`
  (`TerminationChain`).

These structures are not global instances. Downstream modules pass them explicitly.
