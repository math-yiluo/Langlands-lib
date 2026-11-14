# The `K`-finite dual of an admissible representation of a compact group

Module: `Langlands.Representation.KFiniteDual` (namespace `Langlands.KFiniteDual`).

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.ComplexContragredientStatement` in
`Langlands.Representation.Archimedean.ComplexContragredientProof`. It works for an arbitrary
compact topological group `K` and a complex representation `ρ : Representation ℂ K V` on a
vector space `V` with no topology. It uses the hypotheses that the Library's `(𝔤, K)`-module
predicates impose on the `K`-action:

- `hfin`: every vector is `K`-finite (`FiniteVectors.IsFiniteVector ρ v`);
- `hcont`: every coefficient `k ↦ ℓ (ρ k v)`, for an arbitrary linear functional `ℓ`, is
  continuous;
- `hadm`: admissibility, in the form of the Library predicate
  `Archimedean.IsAdmissibleGKModule`: for every continuous matrix representation
  `τ : K →* Matrix (Fin d) (Fin d) ℂ` the space `Archimedean.gkIntertwiners ρ d τ` of
  `K`-equivariant linear maps `(Fin d → ℂ) → V` is finite-dimensional.

The module studies the space `kDual ρ` of `K`-finite vectors of the dual representation
`ρ.dual` (`(ρ.dual k ℓ) v = ℓ (ρ k⁻¹ v)`, Mathlib's `Representation.dual`). It proves:

1. `kDual ρ` with the restricted action `kDualRep ρ` again has every vector finite
   (`isFiniteVector_kDualRep`) and continuous coefficients (`continuous_kDualRep`);
2. it is admissible (`admissible_kDual`);
3. `K`-finite functionals separate the points of `V` (`exists_isFiniteVector_apply_ne_zero`);
4. every `K`-finite linear functional on `kDual ρ` is evaluation at a vector of `V`
   (`exists_eq_eval`), so the `K`-finite dual of `kDual ρ` is `V` itself.

These are the standard properties of the `K`-finite contragredient of an admissible
`(𝔤, K)`-module. Knapp–Vogan, *Cohomological Induction and Unitary Representations* (1995),
Chapter II, remark after (2.42), is a reference for the construction. The proofs here are
direct and internal, so the module cites no source. All definitions (`blockProj`, `Block`,
`blockSub`, `proj`, `projTo`, `subMatrix`, `coordRep`, `evalSum`, `coannihilator`,
`matrixRep`, `contraMatrix`, `kDual`, `kDualRep`, `coef`) are auxiliary definitions of this
formalization.

## Contents and proof route

**Blocks of a semisimple module** (section `Blocks`, any ring `R` and semisimple module `M`).
The isotypic components of `M` (Mathlib's `isotypicComponents`) are independent with supremum
`⊤`. Each component `c` is therefore complementary to the supremum of the others
(`isCompl_isotypicComponent`), and `blockProj c` is the projection onto `c` along that
supremum. Isotypic components are fully invariant, so `blockProj c` commutes with every
`R`-endomorphism (`blockProj_comm`). Taking the endomorphism to be a projection onto a
submodule `N` along a complement shows that `blockProj c` maps `N` into itself
(`blockProj_mem_of_mem`). Every element is the finite sum of its block components
(`exists_finset_blockProj`).

**Semisimplicity** (section `Coordinates`). A finite-dimensional subrepresentation `S` gets
the matrices `subMatrix S` of `ρ` in the basis `Module.finBasis`. These are continuous under
`hcont` (`continuous_subMatrix`). The coordinate representation `coordRep S` on `Fin _ → ℂ` is
semisimple by the Library theorem `CompactFinite.isSemisimple`, using a normalized Haar
measure. Semisimplicity transfers to `S` along the coordinate isomorphism
(`isSemisimple_of_finiteDimensional`). Under `hfin`, `V` is the sum of the orbit spans of its
vectors, each a semisimple submodule. So `ρ.asModule` is a semisimple `ℂ[K]`-module
(`isSemisimpleModule`).

**Blocks of `V`** (section `VBlocks`). `Block ρ` is the set of isotypic components of
`ρ.asModule`, and `blockSub c` is a block as a subrepresentation. `proj c : V →ₗ[ℂ] V` is the
block projection transported to `V`. It is idempotent, kills the other blocks, commutes with
`ρ k` (`proj_rho`) and preserves every subrepresentation (`proj_mem_of_mem`).

**Finite-dimensional blocks** (section `AdmissibleBlocks`). `finiteDimensional_block`: under
`hfin`, `hcont` and `hadm`, every block is finite-dimensional. A block `c` is the isotypic
component of a simple submodule `S`. `S` lies in the orbit span of any of its nonzero vectors
(`mem_orbitSpan_of_isSimpleModule`), so it is finite-dimensional. By the Library lemma
`CompactSplitting.isotypicComponent_eq_iSup_range`, `c` is the sum of the ranges of the
`ℂ[K]`-linear maps `S → V`. Composing such a map with the coordinate isomorphism of `S` gives
an element of `gkIntertwiners ρ d (subMatrix S)`, a finite-dimensional space `H` by `hadm`.
Every range therefore lies in the range of the linear map
`evalSum H : (Fin d → H) → V`, `(Fᵢ) ↦ ∑ᵢ Fᵢ(eᵢ)`, whose domain is finite-dimensional.

**Block components of functionals** (section `DualBlocks`). For a block `c` and a functional
`ℓ`, `ℓ ∘ₗ proj c` is the block component of `ℓ`.

- If the block is finite-dimensional, every functional factoring through `projTo c` is a finite
  vector of `ρ.dual` (`isFiniteVector_comp_projTo`, `isFiniteVector_comp_proj`).
- For a finite vector `w`, `w ∘ₗ proj c` lies in the orbit span `O` of `w`
  (`comp_proj_mem_orbitSpan`). The common kernel of `O` is a subrepresentation
  (`coannihilator`) and is preserved by `proj c`. The claim follows from the double-annihilator
  identity `Subspace.dualCoannihilator_dualAnnihilator_eq` in the finite-dimensional space `O`.
- For a finite vector `ℓ`, the nonzero components `ℓ ∘ₗ proj c` are linearly independent
  elements of the finite-dimensional orbit span, so there are finitely many
  (`finite_comp_proj_ne_zero`), and `ℓ` is their sum (`eq_sum_comp_proj`).

Under the hypothesis `hblock` that all blocks are finite-dimensional:

- (`exists_isFiniteVector_apply_ne_zero`) for `v ≠ 0` some block component `proj c v` is
  nonzero. A functional on the finite-dimensional block that is nonzero there, composed with
  `projTo c`, is a finite vector of `ρ.dual` that is nonzero at `v`.
- (`exists_mem_comp_proj_eq`) if a subspace `W'` of the dual separates the points of `V`, its
  restrictions to a block `c` form a subspace of the block's dual with zero common kernel. By the
  double-annihilator identity they are the whole dual of the block, so every `ℓ ∘ₗ proj c`
  equals some `w ∘ₗ proj c` with `w ∈ W'`.
- (`mem_of_separating`) a subrepresentation `W'` of `ρ.dual` that consists of finite vectors and
  separates the points of `V` contains every finite vector `ℓ` of the dual. Each block component
  of `ℓ` is a block component `w ∘ₗ proj c` of some `w ∈ W'`, which lies in the orbit span of
  `w`, hence in `W'`. Then `ℓ` is the finite sum of these components.

**Matrix representations** (section `MatrixRep`). `matrixRep τ` is the representation on
column vectors defined by `τ`. `contraMatrix σ` is the contragredient matrix representation
`k ↦ (σ k⁻¹)ᵀ`, continuous when `σ` is. `exists_equivariant_projection_matrix` gives an
equivariant projection onto any invariant subspace of a continuous `matrixRep τ`, from the
Library theorem `CompactFinite.exists_equivariant_projection` with a normalized Haar measure.
`exists_mem_gkIntertwiners_comp`: if `ρ.asModule` is semisimple and `φ : V → Fin d → ℂ` is
`K`-equivariant into `matrixRep τ`, there is `ψ ∈ gkIntertwiners ρ d τ` with
`φ (ψ (φ v)) = φ v` for all `v`. Here `ψ` is an equivariant projection onto `range φ`, followed
by the inverse of the restriction of `φ` to a `ℂ[K]`-complement of `ker φ`.

**The finite dual** (section `KDual`). `kDual ρ` is the submodule of `K`-finite vectors of
`ρ.dual`, and `kDualRep ρ` is the restricted representation (Library
`FiniteVectors.subrepresentation` and `FiniteVectors.representation`). Its vectors are finite
(`isFiniteVector_kDualRep`). `exists_sum_of_separating_family`: if a family of functionals
separates the points of a finite-dimensional subspace `S`, every functional agrees on `S` with a
finite linear combination of the family, by duality in finite dimensions. Applied to the
evaluations `w ↦ w v` on the orbit span of `w ∈ kDual ρ`, this writes any coefficient
`k ↦ ℓ (kDualRep ρ k w)` as a finite sum `∑ aᵢ w (ρ k⁻¹ pᵢ)`. That sum is continuous by `hcont`
(`continuous_kDualRep`).

**Admissibility and double duality** (section `KDualAdmissible`).

- `admissible_kDual`: under `hfin`, `hcont` and `hadm`, `IsAdmissibleGKModule (kDualRep ρ)`.
  Let `T ∈ gkIntertwiners (kDualRep ρ) d σ`. Its coefficient map
  `coef T : V → Fin d → ℂ`, `v ↦ (T eᵢ (v))ᵢ`, is equivariant into the contragredient matrix
  representation `contraMatrix σ` (`coef_rho`). Let
  `H = gkIntertwiners ρ d (contraMatrix σ)`, finite-dimensional by `hadm`, and let `B` be the
  finite-dimensional range of `evalSum H`. If `coef T` vanishes on `B`, then
  `exists_mem_gkIntertwiners_comp` writes `coef T v = coef T (ψ (coef T v))` with `ψ ∈ H`.
  Since `ψ` has range in `B`, `coef T = 0` and so `T = 0`. Hence `T ↦ coef T |_B` is an
  injective linear map into the finite-dimensional space `B →ₗ[ℂ] (Fin d → ℂ)`. Injectivity is
  proved by applying this to differences `T - T'`.
- `exists_eq_eval`: under `hfin`, `hcont` and `hadm`, every finite vector `μ` of
  `(kDualRep ρ).dual` has the form `μ w = w v` for some `v ∈ V`. Apply the previous results to
  `kDualRep ρ`: it is semisimple, and its blocks are finite-dimensional by
  `finiteDimensional_block` and `admissible_kDual`. The evaluation map
  `ev : V → Dual (kDual ρ)` is equivariant. So its range is a subrepresentation consisting of
  finite vectors (images of the finite vectors of `V`), and it separates the points of
  `kDual ρ`. By `mem_of_separating` it contains `μ`.
