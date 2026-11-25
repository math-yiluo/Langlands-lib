# Maximal isotypic quotients and the big theta lift of a representation of `G × H`

**GKT §13.2.2** (pp. 391–393: (13.1), Lemma 13.4, (13.2), (13.4), Lemma 13.6, Proposition 13.7,
Corollary 13.8) and **Proposition 13.18** (p. 400), for any representation `ω` of a product of
groups `G × H`, independent of where `ω` comes from (the Weil representation of a dual pair is one
case, `Langlands.Theta.Correspondence.ThetaLift`).

The module `Langlands.Representation.Smooth.IsotypicQuotient` constructs the kernel `S(π)` of the
maximal `π`-isotypic quotient of `ω` and the big theta lift `Θ_ω(π) = (S ⊗ π^∨)_G`, and proves the
statements of GKT §13.2.2 that relate them.

## Content

Let `ω` be a complex representation of `G × H` on `S`, `π` one of `G` on `V`;
`restrictLeft ω`, `restrictRight ω` are the restrictions to `G` and `H`, and `outerTensor π σ` is
`π ⊠ σ` on `V ⊗ W` (`Representation.tprod (π ∘ fst) (σ ∘ snd)`).

- `isotypicKernel ω π = ⋂_{f ∈ Hom_G(ω, π)} ker f` ((13.1)); `isotypicKernel_stable`,
  `isotypicKernelSubrep`: it is a subrepresentation of `G × H` (Lemma 13.4: `f ∘ ω(1, h)` is again
  a `G`-map, `intertwiningCompInr`).
- `BigThetaSpace ω π`: the `G`-coinvariants (Mathlib's `Representation.Coinvariants`) of
  `thetaTensor ω π = ω|_G ⊗ π^∨`, `π^∨` the smooth contragredient (`smoothContragredient`);
  `bigTheta ω π`: `H` acting through `ω(1, h) ⊗ 1` ((13.2), (13.8)); `bigTheta_mk`,
  `mk_tmul_inl` (`[g s ⊗ λ] = [s ⊗ g⁻¹λ]`).

From here on `G` is a topological group with a cofinal family of compact open subgroups (`hG`),
`π` is admissible (`hπ`) and `ω` is smooth on `G` (`hω`).

- `homEquivThetaDual hω hπ hG : Hom_G(ω, π) ≃ₗ[ℂ] Θ_ω(π)^*`, `f ↦ (s ⊗ λ ↦ λ(f s))` (GKT (13.4),
  Lemma 13.6). The inverse sends `ℓ` to `s ↦` the vector `v` with `λ(v) = ℓ[s ⊗ λ]`: the functional
  `λ ↦ ℓ[s ⊗ λ]` on `π^∨` is smooth (`thetaFunctional`), and `π ≅ π^∨∨`
  (`admissibleBidualEquiv`, from the Library's admissible duality). `nontrivial_bigThetaSpace_iff`:
  `Θ_ω(π) ≠ 0` iff `π` is a quotient of `ω|_G` (Proposition 13.18).
- `homEquivThetaHom hG hπ hω : Hom_{G×H}(ω, π ⊠ σ) ≃ₗ[ℂ] Hom_H(Θ_ω(π), σ)` for every
  representation `σ` of `H` (Corollary 13.8): `F ↦ ([s ⊗ λ] ↦ (λ ⊗ 1)(F s))` (`contractLeft`,
  `homToThetaHom`); the inverse sends `L` to `s ↦` the unique tensor `x` with `(λ ⊗ 1) x = L[s ⊗ λ]`
  for all smooth `λ` (`thetaTensorOf`): it exists on `π^K ⊗ W` for `K` compact open fixing `s`,
  built on a basis of the finite-dimensional `π^K` and the dual basis lifted to `(π^∨)^K`
  (`contractLeft_sum_basis`, `smoothDualFixedRestriction_bijective`), and it is unique because the
  smooth dual separates `π ⊗ W` (`eq_zero_of_forall_contractLeft`).
- `isotypicQuotientMap ω π hG hπ hω : ω → π ⊠ Θ_ω(π)`, the map corresponding to the identity of
  `Θ_ω(π)`, `(λ ⊗ 1) φ(s) = [s ⊗ λ]`; `ker_isotypicQuotientMap`: its kernel is `S(π)`;
  `isotypicQuotientMap_surjective`: it is onto when `π` is irreducible; `isotypicQuotientEquiv :
  S / S(π) ≃ₗ[ℂ] π ⊗ Θ_ω(π)` (Proposition 13.7). For the surjectivity the book uses Lemma 13.1
  (submodules of `π ⊗ σ`); here: `φ(s) = ∑ᵢ bᵢ ⊗ [s ⊗ μᵢ]`, the image is stable under the group
  algebra of `G`, and the density theorem (`exists_asAlgebraHom_eq`, Mathlib's
  `jacobson_density` with Schur's lemma `exists_eq_smul_of_isAdmissible`: an endomorphism of an
  admissible irreducible representation has an eigenvalue on a finite-dimensional `π^K`) moves
  `φ(s)` to `v ⊗ [s ⊗ μⱼ]` for every `v`.

## Declarations

- `Langlands.restrictLeft`, `restrictRight`, `inl_mul_inr_comm`, `isotypicKernel`,
  `mem_isotypicKernel`, `intertwiningCompInr`, `isotypicKernel_stable`, `isotypicKernelSubrep`,
  `outerTensor`.
- `Langlands.contractLeft`, `contractLeft_tmul`, `contractLeft_add`, `contractLeft_smul`,
  `contractLeft_map`, `contractLeft_map_right`.
- `Langlands.thetaTensor`, `BigThetaSpace`, `thetaTensorRight`, `bigTheta`, `bigTheta_mk`,
  `mk_tmul_inl`, `smoothContragredient_apply_apply`, `homPairing`, `homPairing_tmul`,
  `homPairing_comp`, `homToThetaDual`, `homToThetaDual_mk`.
- `Langlands.smoothBidual_apply_apply`, `admissibleBidualEquiv`, `admissibleBidualEquiv_apply`,
  `admissibleBidualEquiv_map`, `thetaFunctional`, `thetaFunctional_apply`, `thetaFunctional_map`,
  `thetaDualToHom`, `homEquivThetaDual`, `homEquivThetaDual_apply`,
  `nontrivial_bigThetaSpace_iff`.
- `Langlands.fixedVectors_mono`, `range_map_fixedVectors_mono`,
  `exists_mem_range_map_fixedVectors`, `eq_zero_of_forall_contractLeft`, `contractLeft_sum_basis`,
  `exists_contractLeft_eq`, `homBilin`, `outerTensor_inl`, `outerTensor_inr`, `dual_comp_eq`,
  `homToThetaHom`, `homToThetaHom_mk`, `thetaTensorOf`, `contractLeft_thetaTensorOf`,
  `eq_thetaTensorOf`, `thetaHomToHom`, `homEquivThetaHom`, `homEquivThetaHom_apply_mk`.
- `Langlands.isotypicQuotientMap`, `contractLeft_isotypicQuotientMap`, `ker_isotypicQuotientMap`,
  `isotypicQuotientMap_eq_iff`, `exists_eq_smul_of_isAdmissible`, `exists_asAlgebraHom_eq`,
  `isotypicQuotientMap_surjective`, `isotypicQuotientEquiv`, `isotypicQuotientEquiv_mk`.

## Dependencies

`Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof` (smooth contragredient,
bidual, `smoothDualFixedRestriction_bijective`); Mathlib: `RepresentationTheory.Coinvariants`,
`RepresentationTheory.Irreducible`, `LinearAlgebra.Eigenspace.Triangularizable`,
`Analysis.Complex.Polynomial.Basic`; `RingTheory.SimpleModule.Basic` (`jacobson_density`) through
them.
