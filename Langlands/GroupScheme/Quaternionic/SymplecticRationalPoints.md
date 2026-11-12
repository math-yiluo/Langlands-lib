# Rational points of quaternionic symplectic groups as matrices

Module `Langlands.GroupScheme.Quaternionic.SymplecticRationalPoints`.

Setting as in `SymplecticPoints`. Rational points are the published `rationalPoints G`
(sections over `Spec K`). The base affine test `baseAffineTest K` and the algebra equivalence
`baseSectionsTensorEquiv K D : Γ(baseAffineTest K) ⊗ D ≃ D` are those of the published
`CentralSimpleBinaryGeneration`.

## Comparisons

- `rationalCoeffEquiv_eq_comp'`: the published `GaloisPointComparison.rationalCoeffEquiv` is
  precomposition with the canonical isomorphism `ringTestSelfIso`.
- `mem_carrier_iff_rationalCoeffEquiv`: hence a rational point lies in a subgroup functor iff
  its base affine point does.
- `affine_base_matrix_eq`: for a base affine point of the unit group of `M_n(D)`, its
  affine unit coordinates followed by `K ⊗ M_n(D) ≃ M_n(D)` equal its matrix over
  `Γ ⊗ D` read through `baseSectionsTensorEquiv`. This is the `n × n` version of the published
  binary `affine_base_matrix`, with the same proof.
- `rationalPointsEquiv_eq`: consequently the published `FiniteAlgebraUnits.rationalPointsEquiv`
  of a rational point is the section matrix of its base affine point.
- `FirstKindInvolution.baseSectionsTensorEquiv_baseChange`,
  `baseSectionsTensorEquiv_includeRight`: the comparison intertwines `σ.baseChange` with `σ` and
  is the identity on `1 ⊗ d`.
- `FirstKindInvolution.mem_range_unitaryGroupι_baseAffine_iff`: a base affine point lies in
  the unitary group of `H` iff its section matrix `M ∈ GL_n(D)` satisfies `M H ᵗM^σ = H`.

## The rational matrix

- `FirstKindInvolution.rationalMatrix σ H : rationalPoints (σ.symplecticGroup H) →* GL_n(D)`:
  `rationalPointsEquiv` after the inclusion `symplecticAmbientι H`.
  `rationalMatrix_injective` (the inclusion is a monomorphism) and `rationalMatrix_mem` (its
  values satisfy `g H ᵗg^σ = H`, i.e. lie in `σ.unitaryMatrixGroup H`).
- **`FirstKindInvolution.exists_rationalMatrix_eq_of_contracting`**: let `a ≠ b` and
  `hH : ∀ i j, H₀ i j ≠ 0 → pairWeight a b i + pairWeight a b j = 0`. Every
  `u ∈ σ.unitaryMatrixGroup H₀` with `IsContracting (pairWeight a b) u` equals
  `σ.rationalMatrix H₀ y` for a rational point `y` in
  `Dynamic.unipotent (σ.symplecticCocharacter H₀ a b hH)`.

  Proof. Let `z` be the rational point of the unit group with matrix `u`. Its base affine matrix
  has contracting shape, so `z` lies in the dynamic unipotent subgroup of the ambient
  cocharacter (`mem_unipotent_of_contracting`). It lies in the unitary group because `u` is an
  isometry (`mem_range_unitaryGroupι_baseAffine_iff`). Since the unitary group is closed, its
  lift `z_U` is contracting for the cocharacter of the unitary group
  (`Dynamic.unipotent_eq_comap_of_isClosedSubgroup`). The reduced norm composed with this
  cocharacter is the trivial cocharacter of `𝔾_m`, whose dynamic unipotent subgroup is trivial
  (`Dynamic.unipotent_trivialCocharacter`, `𝔾_m` separated). Functoriality
  (`Dynamic.unipotent_le_comap`) therefore gives reduced norm `1`, so `z_U` comes from a point
  `y` of the symplectic group. Closedness of the kernel puts `y` in the dynamic unipotent
  subgroup of the symplectic cocharacter.

## Provenance

Internal. These are comparisons between the published rational-point, affine-point and
all-test point conventions, together with the dynamic functoriality lemmas of the Library. They
follow the binary template `CentralSimpleBinaryGeneration`.
