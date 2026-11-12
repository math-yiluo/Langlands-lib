# Points of the quaternionic symplectic group in the unit group of `M_n(D)`

Module `Langlands.GroupScheme.Quaternionic.SymplecticPoints`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`.

Setting: `K` a field, `D` a finite-dimensional central division `K`-algebra,
`σ : FirstKindInvolution K D`, `n` a nonempty finite index type and `H : Matrix n n D`. The
published `σ.unitaryGroup H` and `σ.symplecticGroup H` (module `Quaternionic.GroupSchemes`)
are closed subgroups of the unit group scheme of `M_n(D)`. For a test scheme `T`, `R` denotes
its coefficient ring `Γ(T)`.

## Algebra

- `conj_isometry_iff`: for an involution of the first kind `τ` of an `R`-algebra `B` and units
  `q, x`, `q x q⁻¹` preserves `q h τ(q)` iff `x` preserves `h`
  (`y h' τ(y) = h'` with `y = q x q⁻¹`, `h' = q h τ(q)`).

## Inclusion and membership

- `ambientUnits K D n`: the unit group scheme `CentralSimpleUnits.groupScheme K (M_n(D))`.
- `symplecticAmbientι H := σ.symplecticGroupι H ≫ σ.unitaryGroupι H`.
- Instances `mono_unitaryGroupι`, `mono_symplecticAmbientι`; theorems
  `isClosedSubgroup_symplecticGroupι` (the reduced-norm kernel is closed because `𝔾_m` is
  separated), `isClosedSubgroup_symplecticAmbientι`, `isRepresentedBy_symplecticAmbientι`.
- `mem_range_symplecticGroupι_iff`: a point of the unitary group lies in the symplectic group
  iff its reduced norm is `1`.
- `mem_range_symplecticAmbientι_iff`: a point of the unit group lies in the symplectic group iff
  it lies in the unitary group and its reduced norm is `1`.

## Matrix coordinates

- `coefficientEquiv_matrix_baseChange`: the comparison `R ⊗ M_n(D) ≃ M_n(R ⊗ D)`
  (`MatrixPoints.coefficientEquiv`) carries `(σ.matrix n).baseChange R` to the conjugate
  transpose for `σ.baseChange R`.
- `coefficientEquiv_one_tmul_eq_map`: `1 ⊗ M` corresponds to `M` with entries `1 ⊗ M i j`.
- `isometry_iff_coefficientEquiv`: the isometry equation `X (1 ⊗ H) τ(X) = 1 ⊗ H` of
  `mem_range_unitaryGroupι_iff` is the isometry equation of the corresponding matrix over
  `R ⊗ D`.

## Conjugation by a constant unit

Fix `P ∈ GL_n(D)`.

- `conj_comp_gm_eq_one_iff`: conjugation does not change a value in `𝔾_m`.
- `constPoint P T`: the point `1 ⊗ P` on `T`. `pointsEquiv_constPoint`; `comp_constPoint`: it is
  compatible with restriction.
- `conjPoints P T`: conjugation by `constPoint P T` on `T`-points (natural,
  `conjPoints_naturality`), and `conjIso P := isoOfPoints (conjPoints P) _`, an automorphism of
  the unit group scheme. `comp_conjIso_hom` gives its value on points.
- `comap_conjIso`: the preimage under `conjIso P` of the symplectic group of `P H ᵗP^σ` is the
  symplectic group of `H` (isometry by `conj_isometry_iff`, reduced norm by
  `conj_comp_gm_eq_one_iff`).
- **`symplecticGroupCongr P H : σ.symplecticGroup H ≅ σ.symplecticGroup (P H ᵗP^σ)`**, from the
  published `IsRepresentedBy.isoOfComap`.

## Provenance

Internal. This contains elementary consequences of the published definitions of the unitary
and symplectic groups (`IsometryCut`, `CentralSimpleNormOne`, the kernel construction) and of the
represented-subgroup transport API (`RepresentedSubgroupTransport`). A change of basis of the form
gives isomorphic groups, because conjugation by `P` carries the isometries of `H` to those of
`P H ᵗP^σ` (`conj_isometry_iff`) and preserves the reduced norm.
