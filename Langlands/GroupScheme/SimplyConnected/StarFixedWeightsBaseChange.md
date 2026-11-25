# Star-fixed weights: comparison with `IsStarFixedWeight` and base change

This module connects the star-fixed weight subgroups of `SimplyConnected/StarFixedWeights`
to two other parts of the Library. The first is the predicate `IsStarFixedWeight` of
`Reductive/InnerStarWeights`. The second is the base change of Galois pinning data to an
intermediate field, `Reductive/GaloisPinningBaseChange`. It supports the transfer clause
for the Tits obstruction: a weight `λ` fixed by `Γ_F = F.fixingSubgroup` becomes a star-fixed weight
of the base change of `G` to `F`. It constructs no Tits algebra, Brauer class or
corestriction.

Throughout, `k ⊆ K` are fields in one universe, `G` is an affine, locally finite type group
scheme over `Spec k`, and `d : GaloisPinningData k K G`. The integral weights are the
characters of the split torus `T_K` (`characterLattice d.toSplitPinning.torus`).
`d.starAction σ` is the full star action of `σ : K ≃ₐ[k] K` on the based root datum.

## Comparison with `IsStarFixedWeight`

* `mem_starFixedWeights_iff_isStarFixedWeight`: `λ ∈ d.starFixedWeights ↔
  d.IsStarFixedWeight λ`. Both say that `(d.starAction σ).weightEquiv λ = λ` for every
  `σ : K ≃ₐ[k] K`. So the subgroup `starFixedWeights` has exactly the weights that satisfy
  the Library predicate.
* `coe_starFixedWeights`: the same statement as an equality of sets.
* `starFixedWeights_eq_top_of_inner`: if `G` is simply connected and the star action fixes
  every simple vertex (`d.IsInnerStarAction`), then `d.starFixedWeights = ⊤`. Every
  integral weight is then star fixed. The proof applies the Library's
  `isStarFixedWeight_of_inner` to each weight.

## Base change to an intermediate field

Let `F` be an intermediate field of `K / k`, and let `Γ_F = F.fixingSubgroup` be the
subgroup of `K ≃ₐ[k] K` fixing `F` pointwise. `d.baseChange F : GaloisPinningData F K G_F`
is the base change of the pinning data to `F`, with the same `K`.
`d.weightTransport F` is the `ℤ`-linear isomorphism from the weights of `d` to those of
`d.baseChange F`. Both come from `Reductive/GaloisPinningBaseChange`.

* `weightTransport_mem_starFixedWeights_iff`: `d.weightTransport F λ ∈
  (d.baseChange F).starFixedWeights ↔ λ ∈ d.fixedWeights Γ_F`. The left side quantifies over
  all `σ : K ≃ₐ[F] K`. The right side quantifies over the elements of `Γ_F` in
  `K ≃ₐ[k] K`. The proof combines `mem_starFixedWeights` with the Library's
  `forall_fixingSubgroup_starAction_iff`. That theorem compares the two quantifiers by
  restriction of scalars and uses the star compatibility of the weight transport.
* `weightTransport_symm_mem_fixedWeights_iff`: the same statement for the inverse
  transport. A weight `μ` of the base change is star fixed iff its inverse transport is
  fixed by `Γ_F`.
* `weightTransport_mem_starFixedWeights`: a star-fixed weight of `d` transports to a
  star-fixed weight of every base change, because `starFixedWeights ≤ fixedWeights Γ_F`.
* `map_fixedWeights_fixingSubgroup`: the image of `d.fixedWeights Γ_F` under the weight
  transport is exactly `(d.baseChange F).starFixedWeights`.
* `fixedWeightsBaseChangeEquiv : d.fixedWeights Γ_F ≃+ (d.baseChange F).starFixedWeights`:
  the weight transport restricted to these subgroups, as an additive equivalence. Its
  values and inverse values are the transport and its inverse (`_apply`, `_symm_apply`).

The Tits obstruction is defined on the star-fixed weights. The transfer clause evaluates
the obstruction of `G_F` over `F` at the base-changed weight `λ_F`. This equivalence shows
that the transported weight lies in that domain, and that every weight in that domain
arises this way.

## Provenance

Internal. All statements are reformulations of Library results: the definitions of
`starFixedWeights` and `IsStarFixedWeight`, `isStarFixedWeight_of_inner`, and the star
compatibility `forall_fixingSubgroup_starAction_iff` of the weight transport. Tits (1971),
Proposition 5.1, compares the obstruction of `G` over `k` with that of `G` over the fixed
field `k₁` of a stabilizer. This module supplies only the lattice-level identification of
the weights involved. It proves no Brauer identity.
