# The closed-immersion locus of a Hopf point is open

Author: Worker 1421.

For a Hopf point `α : A →ₐ[R] C[M]` (`HopfPointExtension.IsHopfPoint`), the
homomorphism `D(M) → Spec A` over `Spec C` is a closed immersion exactly when
the `C`-linear extension `C ⊗[R] A → C[M]` is surjective. This module shows
that this surjectivity spreads from a residue field to a principal open
neighbourhood. It is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. The Library has a version for
bialgebra maps over the base ring,
`CommutativeAlgebra.DiagonalCoalgebraLocus.exists_away_surjective`; this module
adapts its certificate argument to Hopf points over an arbitrary coefficient
algebra `C`.

## Definitions and lemmas

- `scalarExt α : C ⊗[R] A →ₐ[C] C[M]`, with `scalarExt_tmul`:
  `c ⊗ a ↦ c • α a`.
- `coeff_pairMap_pair`: the `(l, μ)`-coefficient of `pairMap β t` is
  `mul' ((coeffForm β l ⊗ coeffForm β μ) t)`.
- `isCoassoc_comul`: the comultiplication is a coassociative coaction of `A` on
  itself, so `HopfPointWeightWindow.proj comul α χ` is defined on `C ⊗ A`.
- `scalarExt_proj`: for a Hopf point, `scalarExt α (proj comul α χ x)` equals
  `single χ ((scalarExt α x)_χ)`. Coefficientwise this is the
  `(ψ, χ)`-coefficient of `pairMap α ∘ Δ = diagMap ∘ α`.
- `exists_coeff_not_mem`: suppose the residue-field scalar extension at `p` is
  surjective. Then in every degree `m` some `a ∈ A` has `(α a)_m ∉ p`;
  otherwise every element of the image would have vanishing `m`-coefficient.
- `coeff_scalarExt_one_tmul`, `single_mem_range_of_isUnit`: if `(α a)_m` is a
  unit, then `single m 1` lies in the range of `scalarExt α`, namely as the
  image of `v • proj_m (1 ⊗ a)`.
- `exists_away_surjective` (needs `AddMonoid.FG M`): if the residue-field
  scalar extension at `p` is surjective, then for some `f ∉ p` the scalar
  extension over `Localization.Away f` is surjective. Take the product `f` of
  the coefficients `(α (a_m))_m` over a finite generating set of degrees. The
  degree-`m` monomials then lie in the range, and the Library's
  `surjective_of_generators_mem` concludes.
- `adjoin_range_eq_top`: if `scalarExt α` is surjective, then the values of `α`
  generate `C[M]` as a `C`-algebra. This is the hypothesis of
  `HopfPointRigidity.closure_support_eq_top`.
- `exists_coeff_ne_zero_of_field`: this is the field-point version of
  `exists_coeff_not_mem`. Suppose `φ : C →ₐ[R] K` is a homomorphism to a field
  and the specialization `mapAlgHom φ ∘ α` has surjective scalar extension.
  Then in every degree `m` some `a ∈ A` has `φ ((α a)_m) ≠ 0`. Otherwise every
  element of the image would have vanishing `m`-coefficient, which contradicts
  hitting `single m 1`.
- `exists_away_surjective_of_field` (needs `AddMonoid.FG M`): the same openness
  statement around an arbitrary field point `φ`. Some `f` with `φ f ≠ 0` has
  surjective scalar extension over `Localization.Away f`. Take `f` to be the
  product of the nonvanishing coefficients over a finite generating set of
  degrees, then argue as in `exists_away_surjective`.

## Change of coefficients and kernels

- `scalarExt_mapAlgHom_map`: for `ψ : C →ₐ[R] D`, the scalar extension of
  `mapAlgHom ψ ∘ α` applied to `(ψ ⊗ id) y` equals `mapAlgHom ψ` of the scalar
  extension of `α` applied to `y`. The proof is by induction on `y`.
- `surjective_scalarExt_mapAlgHom`: change of coefficients preserves
  surjectivity of the scalar extension. Every monomial `single χ 1` has a
  preimage over `C`, and its image under `ψ ⊗ id` is a preimage over `D`. Then
  `surjective_of_generators_mem` applies with all degrees as generators.
- `ker_scalarExt_le_of_localization`, `ker_scalarExt_eq_of_localization`: the
  inclusion (equality) of the kernels of the scalar extensions of
  `α₁, α₂ : A → C[M]` follows from the corresponding inclusion (equality) after
  localizing `C` at every maximal ideal. Each coefficient of the image of a
  kernel element of `α₁` vanishes after every such localization, by
  `scalarExt_mapAlgHom_map`, so it vanishes (`eq_zero_of_localization`).
