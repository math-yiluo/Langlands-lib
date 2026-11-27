# Weight spaces of a central split torus are stable

Let `k` be a field, `G` an affine group scheme over `Spec k` whose structure
morphism is locally of finite type, `l : M ⟶ G` a homomorphism, `T` a
commutative group scheme whose underlying group is a split torus, and
`a : T ⟶ M` a central homomorphism (`IsCentral a`). The theorem
`Langlands.GroupScheme.isAdjointStable_weightSpace_of_isCentral` proves that
for every character `χ` of `T` the weight space `weightSpace (a ≫ l) χ` of
`Lie(G)(k)` satisfies `Lie.IsAdjointStable G (weightSpace (a ≫ l) χ) l`. For
every commutative `k`-algebra `A` and every `A`-point `m` of `M`, the adjoint
operator `adjoint G A (m ≫ l)` therefore preserves the image of
`A ⊗[k] weightSpace (a ≫ l) χ` in `Lie(G)(A)`.

Over a field and for `A = k`, this is the familiar statement that elements
commuting with a torus preserve its weight spaces. The scheme-theoretic version
needs every test algebra `A`. There the eigenvalue equation cannot be solved
pointwise, and the module instead reads weights off the universal point of the
torus.

## The universal adjoint coefficients over a test algebra

The auxiliary declarations are in the namespace
`Langlands.GroupScheme.splitTorus` and concern a homomorphism
`i : splitTorus (Spec k) I ⟶ G` from the standard split torus with finite
index type `I`.

- `extendedUniversalPoint I A` is the universal point of the split torus over
  the group algebra `A[ℤ^I]`, the image of `universalPoint I` under
  `AddMonoidAlgebra.mapAlgHom (Algebra.ofId k A)`.
  `characterValue_extendedUniversalPoint` shows that the character with
  exponent vector `n` takes the monomial `single n 1` there.
- `extendedUniversalAdjoint G I i A y` is the adjoint action of this point
  (through `i`) on the image in `Lie(G)(A[ℤ^I])` of `y ∈ Lie(G)(A)`.
- `HasUniversalWeight G I i A n y` says that this action multiplies `y` by
  the monomial `single n 1`. The property is closed under sums and
  `A`-multiples (`HasUniversalWeight.add`, `HasUniversalWeight.smul`,
  `HasUniversalWeight.zero`). It holds for the image in `Lie(G)(A)` of every
  vector of `weightSpace i` of the character with exponent `n`
  (`hasUniversalWeight_of_mem_weightSpace`), by the definition of the weight
  space at the universal point.
- `kernelCoefficient_of_hasUniversalWeight`: for `y` of universal weight `n`,
  the `m`-th group-algebra coefficient `Lie.kernelCoefficient G A (I → ℤ) m`
  of `extendedUniversalAdjoint y` is `y` if `n = m` and `0` otherwise
  (`Lie.kernelCoefficient_monomial`).
- `HasUniversalWeight.map_adjoint`: if a point `g` of `G` over `A` commutes,
  after extension to `A[ℤ^I]`, with the universal torus point, then
  `adjoint G A g` preserves universal weights (by `adjoint_naturality`).
- `universalWeightProjection m y` is the `m`-th coefficient of
  `extendedUniversalAdjoint y`. It is additive, and by
  `universalWeightProjection_mem` it lies in the range of
  `Lie.subspaceExtension G (weightSpace i χ_m) A` for every `y`, where `χ_m` is
  the character with exponent `m`. The proof writes `y` as a sum of `c • v_A`
  with `v` in `Lie(G)(k)` (surjectivity of `Lie.kernelScalarExtension`). It
  then decomposes `v` along the internal direct sum of the weight spaces
  (`isInternal_weightSpace`, module
  `Langlands.GroupScheme.Torus.WeightDecomposition`) and applies the previous
  coefficient formula to each summand.
- `adjoint_mem_range_of_commute`: combining these facts, for `g` as above
  and `x` in `A ⊗[k] weightSpace i χ_m`, the image `adjoint G A g x` has
  universal weight `m`. It is therefore equal to its own projection
  `universalWeightProjection m`, which lies in the extended weight space.

## The central case

For `isAdjointStable_weightSpace_of_isCentral`, choose an isomorphism
`e : T ≅ splitTorus (Spec k) I` (`IsSplitTorus`). The weight spaces of
`a ≫ l` are those of `e.inv ≫ a ≫ l` after reindexing the characters by
`characterLattice.comapIso e` (`weightSpace_comapIso`). For an `A`-point `m`
of `M`, centrality of `a` (`mem_center`) at the point
`extendedUniversalPoint I A ≫ e.inv` of `T` over `A[ℤ^I]` shows that its image
in `M` commutes with the extension of `m`. Composing with `l` (`MonObj.mul_comp`)
gives the commutation hypothesis of `adjoint_mem_range_of_commute` for
`g = m ≫ l`.

## Provenance

The module is derived. It implements the standard argument that points
commuting with a diagonalizable group preserve its weight spaces. The weights
are read through the Library's universal-point coefficients
(`Lie.kernelCoefficient`, module
`Langlands.GroupScheme.Lie.GroupAlgebraCoefficientMaps`), which play the role
of the coaction of the torus. The weight decomposition used is the one proved
in the module `Langlands.GroupScheme.Torus.WeightDecomposition`. The module
assumes no smoothness, connectedness or reductivity of `G` or `M`.
