# Hermitian duality for normalized induction

Lean module: `Langlands.Representation.Aubert.General.NormalizedInductionHermitianDuality`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques* (2026 version, literature
ID `renard-2026-representations-groupes-reductifs-padiques`):

- (IV.2.1.2), PDF p.103: when `H \ G` is compact, the hermitian dual of a normalized
  induction is the normalized induction of the hermitian dual, `(i_H^G τ)^h = i_H^G(τ^h)`.
- IV.2.1, Remarque 1, PDF p.103: an admissible representation with a nondegenerate
  invariant hermitian form is isomorphic to its hermitian dual.

VII.1.3 (PDF pp.231–232) uses these two facts in the following form. Let `σ` be unitary
and `χ, χ'` characters with `χ' = conj(χ)⁻¹`. Then
`(i_P^G(σ ⊗ χ))^h ≃ i_P^G(σ ⊗ χ')`. So a unitary subrepresentation (resp. quotient) `W` of
`i_P^G(σ ⊗ χ)` gives a nonzero morphism `i_P^G(σ ⊗ χ') → W` (resp. `W → i_P^G(σ ⊗ χ')`).
The main theorem of this module states and proves this consequence for an abstract
semidirect decomposition `P = M ⋉ U` of a locally compact nonarchimedean group `G`.

The Library has no conjugate (hermitian-dual) representation, and this module does not
construct one. Instead it combines:

- the smooth dual `SmoothDual` and the smooth contragredient;
- the conjugate-linear equivalence `InvariantPositiveForm.smoothDualEquiv`,
  `v ↦ b(v, -)`, from an admissible unitarizable representation to its smooth dual
  (module `Langlands.Representation.Unitary.HermitianDual`). This equivalence is
  equivariant (`toSmoothDual_apply_action`);
- the published natural isomorphism `exists_natural_of_compactSpace`
  (module `Langlands.Representation.Aubert.General.RationalInductionDualityAssembly`).
  For unimodular `G`, compact `P \ G` and the modular character of `P` equal to the
  Haar modulus of `P` acting on `U`, it identifies
  `(i_P^G A)^∨ ≅ i_P^G(A^∨)` for admissible `A`.

A linear intertwiner between two equivariant conjugate-linear maps composes with them
to a linear intertwiner. This replaces the use of `W ≃ W^h` and
`(i_P^G(σ ⊗ χ))^h ≃ i_P^G(σ ⊗ χ')`.

## Declarations

### Conjugate-linear sandwiches

Namespace `Langlands`.

- `conjugateSandwich A hA B C hC`: let `A : V₁ →ₗ⋆[ℂ] V₂` and `C : V₃ →ₗ⋆[ℂ] V₄` be
  conjugate-linear and `G`-equivariant (`hA`, `hC`), and `B` an intertwiner from `ρ₂` to
  `ρ₃`. Then `C ∘ B ∘ A` is a (linear) intertwiner from `ρ₁` to `ρ₄`. It is linear because
  conjugation composed with itself is the identity. `conjugateSandwich_apply` is its value.

### Pointwise conjugate-linear maps on induced functions

Namespace `Langlands.Induction`. Let `P` be a subgroup of a topological group `G`, and
`ρ`, `τ` representations of `P`.

- `smoothFunctionsConjMap P T hT`: a conjugate-linear `T : V →ₗ⋆[ℂ] W` with
  `T(ρ(p) v) = τ(p) T(v)` induces the conjugate-linear map `f ↦ T ∘ f` from
  `SmoothFunctions P ρ` to `SmoothFunctions P τ`. Covariance of `T ∘ f` follows from that
  of `f` and `hT`. A compact open subgroup fixing `f` under right translation also fixes
  `T ∘ f`.
- `eval_smoothFunctionsConjMap`: its value at `x` is `T(f(x))`.
- `smoothFunctionsConjMap_smoothInduced`: it commutes with right translation by `g ∈ G`.
  This holds by definition.
- `smoothFunctionsConjEquiv P T hT`: the same construction for a conjugate-linear
  equivalence `T`, with inverse induced by `T⁻¹`. `smoothFunctionsConjEquiv_apply`
  identifies its forward map.

### Isomorphisms of smooth representations

- `SmoothRep.hom_inv_hom_apply e x`: for an isomorphism `e : A ≅ B`,
  `e.inv (e.hom x) = x`, read from `e.hom_inv_id`.

### Hermitian duality

Namespace `Langlands.Aubert.General`. Let `G` be a locally compact nonarchimedean group,
`P = M ⋉ U` a semidirect decomposition (`h : IsSemidirectDecomposition P M U`) with `U`
closed (`hU`), and `δ_P^{1/2}` the half modulus `HaarModulus.closedHalfCharacter`.

- `smoothDualEquiv_inducingRepresentation`: let `σ` be an admissible representation of
  `M` with invariant positive form `b`, and let `χ, χ'` have open kernels with
  `χ'(m) · conj(χ(m)) = 1`. Then `v ↦ b(v, -)` intertwines the inducing representation of
  `P` for `σ ⊗ χ'` with that for `σ^∨ ⊗ χ⁻¹`. The inducing representation acts by
  `δ_P^{1/2}(p) · χ'(m_p) · σ(m_p)`, where `m_p` is the Levi projection of `p`.
  Conjugate-linearity pulls the two scalars out conjugated. The half modulus is real, so
  it is unchanged. `conj(χ'(m))` equals `χ(m)⁻¹` by the hypothesis. What remains is the
  equivariance `toSmoothDual_apply_action`.

- `normalizedInduction_hermitianDuality`: assume `P` closed, the Levi projection
  continuous (`hm`), `P \ G` compact, `P` locally compact, `G` unimodular (`hG`) and the
  modular character of `P` equal to the restricted Haar modulus on `U` (`hδ`). Let `σ`
  be admissible and unitarizable, and `χ, χ'` open-kernel characters of `M` with
  `χ'(m) · conj(χ(m)) = 1`. Let `W` be a nonzero admissible unitarizable smooth
  representation of `G`. Write `I = normalizedInductionFunctor h hU`. Then:
  1. an injective morphism `W → I(σ ⊗ χ)` yields a morphism `I(σ ⊗ χ') → W` that is
     nonzero at some vector;
  2. a surjective morphism `I(σ ⊗ χ) → W` yields a morphism `W → I(σ ⊗ χ')` that is
     nonzero at some vector.

  Proof. `σ ⊗ χ` is admissible (`isAdmissible_twist_iff`). Compose the isomorphism of
  `exists_natural_of_compactSpace` at `σ ⊗ χ` with `I` applied to
  `contragredientTwistIso`. This gives `E' : I(σ ⊗ χ)^∨ ≅ D`, where
  `D = I(σ^∨ ⊗ χ⁻¹)`. Let `Φ : I(σ ⊗ χ') ≃ D` be `smoothFunctionsConjEquiv` of
  `b.smoothDualEquiv`; it is conjugate-linear and `G`-equivariant by definition, using
  `smoothDualEquiv_inducingRepresentation`. Let `T_W = bW.smoothDualEquiv : W ≃ W^∨`,
  conjugate-linear and equivariant. Compact open subgroups are cofinal in `M`
  (`compactOpenCofinal_of_isClosed`) and in `G` (`compactOpenCofinal_of_nonarchimedean`).
  Fix `w ≠ 0` in `W`.

  1. Let `f : W → I(σ ⊗ χ)` be injective, so `f(w) ≠ 0`. Smooth linear forms separate
     points (`exists_smoothDual_apply_ne_zero_of_compact_cofinal`), so some smooth `ℓ`
     has `ℓ(f(w)) ≠ 0`. Take `F = T_W⁻¹ ∘ f^∨ ∘ E'⁻¹ ∘ Φ`, a linear intertwiner by
     `conjugateSandwich`. It is nonzero at `Φ⁻¹(E'(ℓ))`, whose image is
     `T_W⁻¹(f^∨ ℓ)`. If this were zero, `f^∨ ℓ = ℓ ∘ f` would vanish, so `ℓ(f(w)) = 0`.
  2. Let `f : I(σ ⊗ χ) → W` be surjective. Take `F = Φ⁻¹ ∘ E' ∘ f^∨ ∘ T_W`, a linear
     intertwiner by `conjugateSandwich`. If `F(w) = 0`, then `f^∨(T_W w) = 0`, because
     `Φ⁻¹` and `E'` are injective. Since `f` is surjective, `T_W w` vanishes on all of `W`.
     So `T_W w = 0`, and `w = 0`, a contradiction.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Derived. The source facts are (IV.2.1.2) and IV.2.1, Remarque 1. The formulation through
smooth duals and conjugate-linear equivalences is internal to this module; it states
exactly the consequence used in VII.1.3.
