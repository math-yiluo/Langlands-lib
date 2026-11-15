# The unipotent part of the unit group of a split finite free algebra

Module `Langlands.GroupScheme.FiniteFreeAlgebraUnipotentUnits`.

Namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart`, except
for the last section (namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits`).

The module studies the kernel `1 + J` of the unit-group map of an algebra
homomorphism `π : A → B` with an adapted basis, where `J = ker π`. It shows that
this kernel is a smooth connected unipotent group scheme, and that it is the
unipotent radical when the unit group of `B` is a torus and `π` has an algebra
section. It also shows that the unit group of `R^N` is a split torus. The
intended consumer is the special fibre of the Iwahori model of `GL_N`, where
`B = 𝓀^N` is the diagonal quotient.

## Setting

Let `R` be a commutative ring, `A` and `B` possibly noncommutative `R`-algebras
and `π : A →ₐ[R] B` an algebra homomorphism. Let
`b : Module.Basis (Fin N ⊕ Fin d) R A` be a basis adapted to `π`: the vectors
`b (inl i)` map to a basis `b'` of `B` (`hb' : π (b (inl i)) = b' i`), and the
vectors `e_j = b (inr j)` lie in the kernel (`hb : π (b (inr j)) = 0`). The
kernel `J` of `π` is then spanned by the `e_j`. The hypothesis `hnil` says that
the universal radical element `Σ_j X_j ⊗ e_j` of
`MvPolynomial (Fin d) R ⊗[R] A` is nilpotent; it holds when `J` is a nilpotent
ideal.

## Coordinates and points

- `radicalPart b c = Σ_j c_j ⊗ e_j` in `S ⊗[R] A` for `c : Fin d → S`;
  `map_radicalPart` (it is killed by `id ⊗ π`), `radicalPart_eq_map` and
  `isNilpotent_radicalPart` (it is nilpotent, as the image of the universal
  element).
- `coords b x` are the `inr` coordinates of `x` in the base-changed basis
  `Algebra.TensorProduct.basis S b`. `eq_radicalPart_of_map_eq_zero`: every `x`
  killed by `id ⊗ π` equals `radicalPart b (coords b x)`, because the `inl`
  coordinates of `x` are the coordinates of `(id ⊗ π) x` in the basis
  `1 ⊗ b'`. `coords_radicalPart`, `coords_add`, `coords_sub`, `coords_tmul`,
  `coords_sum`, `radicalPart_mul_radicalPart` and `coords_mul_radicalPart`
  compute coordinates.
- `kerSubgroup π S` is the kernel of the unit map of `id ⊗ π` on
  `(S ⊗[R] A)ˣ`. `pointOf c = 1 + radicalPart b c` (a unit by nilpotency) and
  `coordsOf u = coords b (u - 1)` are inverse bijections between
  `Fin d → S` and `kerSubgroup π S` (`pointOf_coordsOf`, `coordsOf_pointOf`).
  `coordsOf_pointOf_mul` is the group law in coordinates:
  `(c, c') ↦ c + c' + (m ↦ Σ_{a,a'} c_a c'_{a'} c^m_{a a'})`, where
  `c^m_{a a'} = structureConst b a a' m` is the `m`-th kernel coordinate of
  `e_a * e_{a'}`.

Auxiliary lemmas: `map_smul_tensor` (`id ⊗ π` is `S`-linear), `mem_kerSubgroup`
(membership means `(id ⊗ π) u = 1`) and `pointOf_val` (the underlying element
of `pointOf c`).

## Nilpotency from weights

- `RadicalOfWeight b w n x`: `x = radicalPart b c` with `c m = 0` unless
  `n ≤ w m`. `radicalOfWeight_mul_radicalPart`: multiplying by a radical part
  with coefficients of weight at least `1` raises the weight bound by `1`, when
  the weights are adapted to the products of the kernel basis
  (`b.repr (e_a * e_{a'}) (inr m) ≠ 0 → w a + w a' ≤ w m`).
- `isNilpotent_universalRadical_of_weights`: with weights `w ≥ 1` adapted in
  this sense, the universal radical element is nilpotent (its
  `(Σ_m w m + 1)`-st power is zero), so `hnil` follows from the weights.

## The group scheme

- `kerMap` (with `map_comm`, `kerMap_val`, `kerMap_pointOf`) and `functor`:
  `S ↦ kerSubgroup π S`, a functor `CommAlgCat R ⥤ GrpCat`.
- `corepresentableBy`: the functor is corepresented by
  `coordinateAlgebra = MvPolynomial (Fin d) R`, through `pointOf` and
  `coordsOf`.
- `groupScheme π b hnil hb b' hb'`, the corresponding affine group scheme over
  `Spec R` (Library `Corepresented.groupScheme`). `groupScheme_hom`: its
  structure morphism is `Spec` of `R → MvPolynomial (Fin d) R`.
  `groupScheme_isAffineHom`, `smooth`, `geometricallyIrreducible` (by the
  published `FiniteFreeAlgebraUnits.geometricallyIrreducible_spec_coordinateRing`)
  and `geometricallyConnected`.

## Comparison with the actual kernel

- `flatBasis b`, the basis reindexed by `Fin (N + d)`, and
  `unitMap π b b' = FiniteFreeAlgebraUnits.map (flatBasis b) b' π`, the
  unit-group map of `π` from `Langlands.GroupScheme.FiniteFreeAlgebraUnitsQuotient`.
- `unipotentPointsEquiv` (with `unipotentPointsEquiv_naturality`): points of `groupScheme` are the
  elements of `kerSubgroup π Γ(T)`.
- `comp_unitMap_eq_one_iff`, `actualKernelPointsEquiv` (with
  `actualKernelPointsEquiv_val` and `actualKernelPointsEquiv_naturality`): points of the actual group-scheme kernel
  `kernel (unitMap π b b')` (module `Langlands.AbelianScheme.Kernel`) are also
  the elements of `kerSubgroup π Γ(T)`.
- `kernelIso : groupScheme π b hnil hb b' hb' ≅ kernel (unitMap π b b')`, by the
  Library's `isoOfPointModels`.

## Comultiplication and unipotence

- `comul_X`: the comultiplication of the coordinate bialgebra
  (`AffineLinearEmbedding.comul`) is
  `X m ↦ X m ⊗ 1 + 1 ⊗ X m + Σ_{a,a'} c^m_{a a'} • (X a ⊗ X a')`, read off from
  the product of the two universal points (`AffineLinearEmbedding.pt_comul`).
- `TotalWeightLE w F s` and its closure lemmas (`zero`, `mono`, `add`, `sum`,
  `mul`, `C_of`, `one`, `pow`, `prod`, `X_var`, `C_X`, `C_C`): the
  general-weight version, for any index type and weight `w`, of the
  `Pos N`-specific `TotalWeightLE` of
  `Langlands.GroupScheme.UnitriangularUnipotent.WeightCore`. The proofs follow
  that file.
- `comulPolyJ c`: the comultiplication in polynomial form, inner variables
  `C (X q)` for the left factor and outer variables `X q` for the right factor:
  `X m ↦ C (X m) + X m + Σ c a a' m C (X a) X a'`. (`comulPolyJ_X`) With weights
  `w : Fin d → ℕ` such that `c a a' m ≠ 0 → w a + w a' ≤ w m`:
  `totalWeightLE_comulPolyJ` (total weight at most the weight of the input;
  from `totalWeightLE_comulPolyJ_X` and `totalWeightLE_comulPolyJ_monomial`),
  `map_constantCoeff_comulPolyJ` (setting inner variables to zero gives back
  the input) and `coeff_comulPolyJ_of_weight_le` (if all weights are at least
  `1`, the outer coefficient at a monomial of maximal weight is the constant
  coefficient).
- `structureConst`, `kappa` and `comul_eq_kappa_comp`: the comultiplication
  factors as `kappa ∘ comulPolyJ (structureConst b)`.
- Over a field `k` (`R = CommRingCat.of k`), with weights `w ≥ 1` adapted to
  the structure constants: `oneMemStable` (every nonzero finite-dimensional
  right-translation stable subspace contains `1`, by the maximal-weight
  argument of `UnitriangularUnipotent.oneMemStable_of_coordinates`, reusing its
  general `rid_lTensor_eval₂Hom`) and `isUnipotent`, by the Library's
  `Unipotent.isUnipotent_of_oneMemStable`.

## The unipotent radical

- `radicalInclusion = (kernelIso ...).hom ≫ kernelι (unitMap π b b')`, the
  unipotent kernel as a subgroup of the unit group of `A`, and
  `connectedSpace` (its underlying space is the spectrum of a polynomial ring).
- `isUnipotentRadical`: over a field, with weights as above, an algebra
  section `s` of `π` (`π.comp s = id`) and `hD : IsTorus` for the unit group
  of `B`, `radicalInclusion` is the unipotent radical (`IsUnipotentRadical`)
  and `unitMap π b b'` is the fppf quotient by its range. It combines the
  Library's `IsUnipotentRadical.of_torus_quotient`,
  `SubgroupFunctor.range_iso_comp`, the closed immersion
  `kernelι_isClosedImmersion` and `isFppfQuotient_map_of_section`.

## Units of `R^N` form the split torus

Namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits`, for `R : CommRingCat`
and `N : ℕ`, with the standard basis `Pi.basisFun R (Fin N)` of `R^N`.

- `tensorPiEquiv R N S : S ⊗[R] R^N ≃ₐ[R] S^N`, Mathlib's
  `Algebra.TensorProduct.piRight` followed by `Algebra.TensorProduct.rid` in each
  coordinate, with `tensorPiEquiv_tmul` (`s ⊗ v ↦ (v_i • s)_i`) and
  `tensorPiEquiv_natural` (it commutes with `f ⊗ id` for algebra maps `f`).
- `piUnitsPointsEquiv R N T`: the points over `T` of the published unit group
  scheme `groupScheme (Pi.basisFun R (Fin N))` are families, indexed by
  `ULift (Fin N)`, of units of `Γ(T, ⊤)`. It composes the published
  `pointsEquiv`, the units of `tensorPiEquiv`, Mathlib's `MulEquiv.piUnits` and
  the reindexing `MulEquiv.arrowCongr Equiv.ulift.symm`.
  `piUnitsPointsEquiv_apply` and `piUnitsPointsEquiv_naturality` (restriction
  along `T' ⟶ T` is the Library's `splitTorus.unitsRestrict`).
- `piUnitsIso : groupScheme (Pi.basisFun R (Fin N)) ≅ splitTorus (Spec R) (ULift (Fin N))`,
  by the Library's `isoOfPointModels` with the Library's
  `splitTorus.pointsEquiv` and `splitTorus.pointsEquiv_naturality` on the torus
  side.
- `isSplitTorus_pi`: the unit group scheme of `R^N` is a split torus
  (`IsSplitTorus.of_iso` and `isSplitTorus_splitTorus`); `isTorus_pi`: over a
  field `k` it is a torus (`IsSplitTorus.isTorus`).

## Provenance

Internal infrastructure for the reductive quotient of the special fibre of
the published Iwahori model of `GL_N`. The unipotence argument is the weight
argument of Milne (2017), *Algebraic Groups*, proof of Theorem 14.5, as
implemented for the unitriangular group in the Library
(`Langlands.GroupScheme.UnitriangularUnipotent.WeightCore` and
`UnitriangularUnipotent.oneMemStable_of_coordinates`). Here it is applied to
the coordinates of `1 + J`, with weights adapted to the products of the kernel
basis. The general `TotalWeightLE` is needed because the published one is
stated for the index type `Pos N` with its fixed weight; its closure lemmas
follow the published proofs. `rid_lTensor_eval₂Hom` is reused from the Library.
The decomposition of the unit group as radical and torus quotient is the
Library's `IsUnipotentRadical.of_torus_quotient`. No external statement is
formalized and no external code is adapted.

## Not claimed

`isUnipotentRadical` takes as a hypothesis that the unit group of `B` is a
torus. The only torus proved here is the unit group of `R^N`. No specific
algebra `A` is treated. The weight and nilpotency hypotheses are not verified
for any example. The Iwahori instance is in a separate module.
