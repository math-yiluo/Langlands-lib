# Transport of quadratic pairs to division-form quadratic forms

Author: Worker 1383, for Task 6507 (`f0045927-f50c-4853-9944-3c98c7ea5daf`), in collaboration
with Worker 74. This module is the orthogonal counterpart of the comparison
`SymplecticInnerForm.normOneGroupAlgEquivIso` in `SymplecticInnerForm/AlgebraTransport`, and
it reuses that module's `tensor_adjoint_compatibility` and `FiniteAlgebraUnits.algEquivIso`.

## Setting

All declarations are in the namespace `Langlands.GroupScheme.OrthogonalInnerForm`. Fix a field
`K`, a `K`-algebra `A`, a division `K`-algebra `D` (all in universe `u`) and a finite index type
`m : Type`, with:

- an involution of the first kind `τ` of `A` and one, `σ`, of `D`;
- a `K`-algebra isomorphism `φ : A ≃ₐ[K] M_m(D)` and a matrix `H ∈ M_m(D)` with
  `hφ : ∀ x, φ (τ x) * H = H * σ.matrix m (φ x)`, that is, `φ (τ x) = H ᵗ(φ x)^σ H⁻¹` when `H`
  is invertible.

For `a₀ : A`, the class `[φ(a₀) * H]` is an element of Tits's space of `σ`-quadratic forms
`σ.QuadraticForms m = M_m(D) ⧸ {x - ᵗx^σ}` (`Quaternionic/Forms`). For a commutative
`K`-algebra `R` write `E = Algebra.TensorProduct.map (AlgHom.id R R) φ.toAlgHom`, the
extension of `φ` to `R ⊗[K] A → R ⊗[K] M_m(D)`.

## Results on the quadratic form

- `polar_mk_mul τ σ φ H hφ hHσ ha₀`: if `σ.matrix m H = H` and `a₀ + τ a₀ = 1`, then
  `σ.polar [φ(a₀) * H] = H`. Proof: the polar matrix is `Q + ᵗQ^σ` (`polar_mk`). With
  `Q = φ(a₀) H`, `ᵗQ^σ = ᵗH^σ ᵗ(φ a₀)^σ = H ᵗ(φ a₀)^σ = φ(τ a₀) H` by `hφ`. So the polar matrix
  is `φ(a₀ + τ a₀) H = H`.
- `isNondegenerateQuadratic_mk_mul`: if moreover `H` is a unit, `[φ(a₀) * H]` is
  nondegenerate, since nondegeneracy means that the polar matrix is a unit.

## Results over coefficient algebras

- `defect_tensor_map τ σ φ H hφ R a₀ y`: for `y : R ⊗[K] A`,
  `defect (σ.matrix m) (φ a₀ * H) (E y) = E (defect τ a₀ y) * (1 ⊗ H)`. Here
  `IsometryCut.defect τ Q y = y (1 ⊗ Q) τ_R(y) - 1 ⊗ Q`. Proof: write
  `1 ⊗ (φ(a₀) H) = E(1 ⊗ a₀) (1 ⊗ H)`. Then move `1 ⊗ H` past `σ*_R(E y)` with
  `tensor_adjoint_compatibility` (`E(τ_R y) (1 ⊗ H) = (1 ⊗ H) σ*_R(E y)`) and use that `E` is
  multiplicative.
- `tensor_map_mul_mem_baseChange_iff τ σ φ H hφ R hHσ hH z`: for hermitian invertible `H` and
  `z : R ⊗[K] A`, `E z * (1 ⊗ H) ∈ R ⊗ {x - ᵗx^σ}` if and only if `z ∈ R ⊗ {a - τ a}`. Proof:
  `IsometryCut.alternatingSubspace_baseChange` describes both base-changed subspaces as
  `{w - ν_R w}` for the extended involutions `ν_R`. For every `v`, `tensor_adjoint_compatibility`
  and `ᵗH^σ = H` give `E(v - τ_R v) (1 ⊗ H) = w - σ*_R w` with `w = E v (1 ⊗ H)`. This proves
  the reverse direction. For the forward direction, any `w` has this form with
  `v = E⁻¹(w (1 ⊗ H)⁻¹)`; here `E` is the algebra equivalence
  `Algebra.TensorProduct.congr AlgEquiv.refl φ` and `1 ⊗ H` is a unit. Cancelling the unit
  `1 ⊗ H` and using injectivity of `E` gives `z = v - τ_R v`.

## The group-scheme isomorphism

Now assume `A` and `D` finite-dimensional over `K`, `σ.matrix m H = H` (`hHσ`) and `IsUnit H`
(`hH`).

- `isRepresentedBy_inclusion_alternatingSubspace τ a₀` and `isRepresentedBy_isometryGroupι σ q`:
  the inclusions `IsometryCut.inclusion isStable_alternatingSubspace a₀` and
  `σ.isometryGroupι q` represent their ranges. They are monomorphisms because they are
  closed immersions over the base (`isClosedSubgroup_inclusion`,
  `isClosedSubgroup_isometryGroupι`, `Over.mono_of_mono_left`).
- `comap_algEquivIso_isometryGroupι`: the pullback of the range of
  `σ.isometryGroupι [φ(a₀) * H]` along `(FiniteAlgebraUnits.algEquivIso φ).hom` is the range
  of the isometry-cut inclusion of `a₀` modulo `{a - τ a}`. Proof on each relative test `T`
  with `R = Γ(T)`: `mem_range_isometryGroupι_iff` with representative `φ(a₀) H`,
  `mem_range_inclusion_iff` and `pointsEquiv_comp_algEquivIso_hom` reduce membership to
  `defect σ* (φ a₀ H) (E u) ∈ R ⊗ {x - ᵗx^σ}` versus `defect τ a₀ u ∈ R ⊗ {a - τ a}`. The two
  previous results identify these conditions.
- `isometryCutAlgEquivIso τ σ φ H hHσ hH hφ a₀ :
  IsometryCut.groupScheme (τ := τ) (M := τ.alternatingSubspace) isStable_alternatingSubspace a₀ ≅
  σ.isometryGroup [φ(a₀) * H]`. This is `SubgroupFunctor.IsRepresentedBy.isoOfComap` applied to
  the two representing inclusions, `FiniteAlgebraUnits.algEquivIso φ` and the comap identity.
  The points of the source over `R` are the units `u` of `R ⊗[K] A` with
  `u a₀ τ(u) - a₀ ∈ R ⊗ {a - τ a}`. This needs neither `a₀ + τ a₀ = 1` nor central
  simplicity; with `a₀ + τ a₀ = 1` the target is the isometry group of a nondegenerate form
  (`isNondegenerateQuadratic_mk_mul`).
- `isometryCutAlgEquivIso_hom_comp`: the isomorphism intertwines the two inclusions with
  `(FiniteAlgebraUnits.algEquivIso φ).hom`.

## Provenance

Provenance: derived. The construction is the matrix form of the description of quadratic
pairs in M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (AMS
Colloquium Publications 44, 1998; source `knus-merkurjev-rost-tignol-1998-book-of-involutions`).
Proposition (5.7) (printed p.56, PDF p.79) gives an element `ℓ` with `ℓ + σ(ℓ) = 1`, unique
modulo `Alt(A, σ)`. Proposition (5.8) (printed pp.56–57, PDF pp.79–80) multiplies `ℓ` by the
symmetric Gram element `g` to obtain `a = gℓ` with `a + τ(a) = g`. The remark after (5.8)
identifies classes in `A ⧸ Alt(A, τ)` with quadratic forms. Here `φ(a₀)` plays the role of `ℓ`
and `H` the role of `g`, with the factors in the opposite order (`Q = φ(a₀) H`), because `φ`
carries `τ` to `y ↦ H ᵗy^σ H⁻¹`. The class `[Q]` is a quadratic form in the sense of J. Tits,
*Formes quadratiques, groupes orthogonaux et algèbres de Clifford*, Invent. Math. 5 (1968)
(source `tits-1968-formes-quadratiques-clifford`), §2.2, printed p.21 / PDF p.4. The proofs
above are direct matrix computations. The group-scheme comparison follows the pattern of
`SymplecticInnerForm/AlgebraTransport`.
