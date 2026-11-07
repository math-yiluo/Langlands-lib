# Weight projectors of a finite comodule and openness of weight windows

Author: Worker 1421.

This module provides the open "weight window" conditions on the scheme of
homomorphisms from a diagonalizable group to an affine group, used in the chart
construction of task `45ac6e52-a4d8-4414-91f1-03c3be35223e`. Geometrically, a
homomorphism `D(M) → Spec A` over `Spec C` makes every comodule `V` of `A` into
an `M`-graded `C`-module. The set of points where all weights lie in a given set
`T` is open. This is the classical correspondence between representations of
diagonalizable groups and gradings, e.g. Milne, *Algebraic Groups* (2017),
Remark 12.13 (registered source `milne-2017-algebraic-groups`). The proofs here
are direct computations.

Notation: `R` is a commutative ring, `A` a commutative `R`-bialgebra, `C` a
commutative `R`-algebra and `M` an additive commutative group. `β : A →ₐ[R]
C[M]` is an algebra map, and a Hopf point (`HopfPointExtension.IsHopfPoint`)
where stated. `V` is an `R`-module with a right coaction
`δ : V →ₗ[R] V ⊗[R] A`.

## Coefficients and convolution

- `coeffForm β l : A →ₗ[R] C`, `a ↦ (β a).coeff l`.
- `coeff_inlMap_mul_inrMap`: the `(l, μ)`-coefficient of
  `inlMap x * inrMap y` is `x_l y_μ`.
- `coeff_pairMap`: the `(l, l)`-coefficient of `pairMap β t` is the product
  `mul'` of `coeffForm β l ⊗ coeffForm β l` applied to `t`.
- `mul'_map_coeffForm_comul`: for a Hopf point, `coeffForm β l` is idempotent
  for convolution. Compare `(l, l)`-coefficients in `pairMap β ∘ Δ = diagMap ∘ β`.

## Projectors

- `IsCoassoc δ`: `assoc ∘ (δ ⊗ id) ∘ δ = (id ⊗ Δ) ∘ δ`.
- `coeffSwap β l : V ⊗ A → C ⊗ V`, `v ⊗ a ↦ β(a)_l ⊗ v`.
- `proj δ β l : C ⊗[R] V →ₗ[C] C ⊗[R] V`: the `C`-linear extension of
  `coeffSwap β l ∘ δ`. This is the projection onto the weight-`l` part.
  `proj_tmul` computes it on pure tensors.
- `proj_coeffSwap`: `proj` applied after `coeffSwap` equals the convolution
  expression `convSwap` applied to the double coaction. Proved on pure tensors.
- `proj_proj` (needs `IsCoassoc δ` and `IsHopfPoint β`): `proj` is idempotent.
  Coassociativity turns the double coaction into `(id ⊗ Δ) ∘ δ`, and the
  convolution identity collapses it.
- `counitV ι : C ⊗[R] V →ₗ[C] C`, for `ι : V →ₗ[R] A`: the `C`-linear extension
  of `algebraMap ∘ ε ∘ ι`.
- `counitV_proj`: if `ι` is a comodule map (`Δ ∘ ι = (ι ⊗ id) ∘ δ`), then
  `counitV ι (proj δ β l (1 ⊗ v)) = (β (ι v))_l`. Proof: the counit law
  `(ε ⊗ id) ∘ Δ = 1 ⊗ id` (Mathlib's `rTensor_counit_comul`).
- `rTensor_proj`: projectors commute with change of coefficients
  `ψ : C →ₐ[R] D`, for the Hopf point `mapAlgHom M ψ ∘ β`.

## Openness

- `exists_smul_eq_zero_of_idempotent`: let `e` be an idempotent endomorphism of
  a finite `C`-module, and `p` a prime with `e ⊗ κ(p) = 0`. Then `f • e = 0`
  for some `f ∉ p`. Proof: the range `P` of `e` is a direct summand, so
  `κ(p) ⊗ P` is a retract of `κ(p) ⊗ N` on which `e` acts as the identity;
  hence `κ(p) ⊗ P = 0`. By Mathlib's
  `Module.mem_support_iff_nontrivial_residueField_tensorProduct`, `p` is not in
  the support of `P`. By `Module.mem_support_iff_of_finite`, the annihilator of
  `P` is not contained in `p`.
- `cancelBaseChange_tmul_eq`: `cancelBaseChange (k ⊗ z) = k • (ψ ⊗ id) z` for
  the residue map `ψ`.
- `exists_mul_coeff_eq_zero` (needs `V` finite, `IsCoassoc δ`, `IsHopfPoint β`
  and a comodule map `ι`): if the weight projector for `l` of the residue-field
  Hopf point at `p` vanishes, then some `f ∉ p` satisfies
  `f * (β (ι v))_l = 0` for all `v`. Combine the base-change lemma with
  `cancelBaseChange` to get `proj ⊗ κ(p) = 0`, then apply the previous lemmas.

## Coaction and finiteness

- `exists_coaction` (needs `Module.Flat R A`): a right subcomodule `V ⊆ A`, in
  the sense of `FiniteSubcomodule.IsRightSubcomodule`, carries a coaction `δ`
  with `IsCoassoc δ` and `Δ ∘ V.subtype = (V.subtype ⊗ id) ∘ δ`. Lift `Δ`
  through the map `V ⊗ A → A ⊗ A`, which is injective by flatness. Check
  coassociativity after the map `V ⊗ (A ⊗ A) → A ⊗ (A ⊗ A)`, also injective by
  flatness (Mathlib: tensor products of flat modules are flat).
- `WeightsIn δ β T`: every weight projector for `l ∉ T` vanishes.
- `exists_finite_weightsIn` (needs `V` finite): some finite `T` works. Only the
  supports of the coefficients occurring in `δ v`, for generators `v`, can carry
  nonzero projectors.
- `support_subset_of_weightsIn`: if the weights lie in `T`, then every
  `β (ι v)` is supported in `T` (by `counitV_proj`).

## Pushforward

- `coeff_mapDomain_eq_sum`: the `l`-coefficient of `mapDomain π x` is the sum
  of the coefficients of `x` at the points of a finite set `S ⊇ supp x` lying
  over `l`.
- `weightsIn_mapDomain`: if the weights of `β` lie in `T`, the weights of
  `mapDomain π ∘ β` lie in `π '' T`. The weight-`l` projector of the pushforward
  is the sum of the weight-`χ` projectors of `β` over the finitely many
  relevant `χ` with `π χ = l`, and each such `χ` lies outside `T`.
