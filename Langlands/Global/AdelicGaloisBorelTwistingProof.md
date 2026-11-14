# Galois twisting of a split Borel pair from a Galois root action

This module proves the Library statement `GaloisBorelTwistingStatement` (module
`AdelicGaloisBorelTwisting`). It assumes the two Lemma S statements of module
`AdelicGaloisTwistSubgroup`, and `galoisBorelTwisting_of` makes them explicit hypotheses:

```
theorem galoisBorelTwisting_of (hS1 : GaloisTwistNormOneStatement.{u})
    (hS2 : GaloisTwistSubgroupStatement.{u}) : GaloisBorelTwistingStatement.{u}
```

All other inputs are proved results from the Library or from the helper modules of this
development. The argument is the Galois-twisting step of Springer's proof of compactness
(Springer 1994, §3.5): every `σ ∈ Gal(L/F)` acts on `G(𝔸_L)` and carries the split Borel pair
`(P_∅, T₀_L)` to its conjugate by a rational point. The Lean route is internal to this
development and is described below.

Notation: `L/F` is a finite Galois extension of number fields and `G` is an affine group over
`F`, locally of finite type. `T₀` is a commutative group over `F`, and
`T₀_L = (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀`. `i₀ : T₀ ⟶ G` is a
homomorphism, and `galoisTwist F L G σ` is the Galois twist on the upper adelic points of `G_L`
(module `AdelicGaloisTwistMap`).

## Torus inclusion

- `torusInclusion F L G T₀ i₀`: the base change `i₀_L : T₀_L ⟶ G_L`, an abbreviation for
  `(GroupScheme.baseChange (algebraBaseMap F L)).map i₀`.
- `galoisTwist_map_torusInclusion`: `galoisTwist σ (i₀_L t) = i₀_L (galoisTwistLie σ t)`. This is
  `galoisTwist_comp_baseChange` (module `AdelicGaloisTwistTorus`).

## Conjugation by rational points

- `rationalCoeffEquiv_eq_basePointEquiv`: for a rational point `m` of `G_L`, the coefficient
  point `rationalCoeffEquiv L G_L m` is the base point `basePointEquiv m`. The proof compares the
  underlying morphisms (`Over.OverMorphism.ext`, `rationalCoeffEquiv_left`).
- `rationalSection_eq_rational_basePointEquiv`: hence `rationalSection F L G m` is the principal
  adelic point `rational L G_L (basePointEquiv m)`.
- `map_eq_rationalSection_conj`: let `T` be a commutative group over `L` and
  `i : T ⟶ G_L` a homomorphism. If `m⁻¹` normalizes `i` through `τ : T ≅ T`
  (`IsNormalizingPoint i m⁻¹ τ`), then for every adelic point `s` of `T`,
  `i s = m · i(τ s) · m⁻¹`, where `τ s` is the image of `s` under `τ.hom` (written
  `τ.symm.inv` in Lean). The proof
  inverts the normalizing relation (`IsNormalizingPoint.inv`) and applies the Library lemma
  `map_mul_rational_basePointEquiv` (module `AdelicNormalizerConjugation`).
- `exists_galoisTwist_torus_conj`: proves clause 3 of `IsGaloisBorelTwist` at one adelic torus
  point `t`. Its inputs are
  - a point `t₁` with `galoisTwist σ (i t) = i t₁`;
  - a normalizing point `m⁻¹` with automorphism `τ`;
  - preservation of the norm-one subgroup by `galoisTwist σ`;
  - for each simple root `β`, a simple root `β'` with `‖τ.hom ≫ β‖(t₁) = ‖β'‖(t)`, where
    `‖χ‖` is `PositiveRealTorus.normCharacter L T χ`.

  The witness is `t' = τ t₁`, the image of `t₁` under `τ.hom`, so that `galoisTwist σ (i t) = m · i t' · m⁻¹` by
  `map_eq_rationalSection_conj`. The image `i t'` is the `m⁻¹`-conjugate of a norm-one point,
  and the norm-one subgroup is normal (`normOneSubgroup_normal`). The norm identity
  `‖β‖(τ t₁) = ‖τ.hom ≫ β‖(t₁)` is `normCharacter_map_groupHom_inv`.

## The Galois root maps

The Library module `AdelicGaloisRootAction` defines the root map
`a σ = galoisRootMap F L T₀ τ σ : χ ↦ (τ σ).inv ≫ σ χ`, where `σ χ` is
`characterLattice.galoisRepresentation F L T₀ σ χ`, and the predicate
`IsGaloisRootAction F L G T₀ i ν m τ`.

- `galoisRootMap_injective`: each `a σ` is injective, since `characterAut (τ σ)` is injective
  and `σ⁻¹` inverts `σ` on characters.
- `galoisRootMap_galoisRepresentation_inv`: `a σ (σ⁻¹ ((τ σ).hom ≫ β)) = β`.
- Under `hR : IsGaloisRootAction F L G T₀ i ν m τ`:
  - `IsGaloisRootAction.galoisRootMap_galoisRootMap_inv`: `a σ (a σ⁻¹ β) = β` for every simple
    root `β`, by the action laws.
  - `IsGaloisRootAction.galoisRepresentation_inv_mem`: `σ⁻¹ ((τ σ).hom ≫ β)` is a simple root when
    `β` is. It equals `a σ⁻¹ β` by injectivity of `a σ`.
  - `IsGaloisRootAction.image_simpleRelativeRoots`: `a σ` maps the simple roots `Δ` onto `Δ`.
  - `IsGaloisRootAction.image_diff_singleton`: `a σ '' (Δ \ {β}) = Δ \ {a σ β}`.

## Core and final theorem

- `exists_normCharacter_galoisTwistLie`: under `hR`, with `i = torusInclusion`, for each simple
  root `β` the root `β' = σ⁻¹ ((τ σ).hom ≫ β)` is simple. Moreover
  `‖(τ σ).hom ≫ β‖(galoisTwistLie σ t) = ‖β'‖(t)`. This is `normCharacter_galoisTwist` at the
  character `β'`, rewritten with `σ (σ⁻¹ χ) = χ`.
- `hasGaloisBorelTwisting_of_rootAction`: let `hS1`, `hS2` be Lemma S and let
  `hR : IsGaloisRootAction F L G T₀ (torusInclusion F L G T₀ i₀) ν m τ`. Then
  `HasGaloisBorelTwisting F L G T₀_L (torusInclusion F L G T₀ i₀) ν` holds with
  `φ σ = galoisTwist F L G σ`, the rational points `m σ` and the root maps `a σ`. The clauses of
  `IsGaloisBorelTwist` are proved as follows.
  1. Rational sections: `galoisTwist_rationalSection`.
  2. Scalar extensions of ground norm-one points: `galoisTwist_scalarExtension`.
  3. The torus: `exists_galoisTwist_torus_conj`, using `t₁ = galoisTwistLie σ t`, `hR.1 σ`,
     `hS1` and `exists_normCharacter_galoisTwistLie`.
  4. The minimal parabolic `P_∅`: `hS2` with `f = g = parabolicHom i ν ∅`. Both are closed
     subgroups (`Standard.isClosedSubgroup_parabolicHom`), and the range condition is clause 3
     of `hR` at `J = ∅`, since `a σ '' ∅ = ∅`.
  5. Maximal parabolics: `a σ β` is simple (`hR.2.1`). The range identity is clause 3 of `hR`
     at `J = Δ \ {β}`, rewritten by `image_diff_singleton`.

  The identity and composition laws of `a` are the last two clauses of `hR`.
- `galoisBorelTwisting_of`: let `G` be connected reductive over a number field `F`. Then:
  - `maximalTorusExistence` gives a maximal torus `i₀ : T₀ ⟶ G`.
  - `torusFiniteGaloisSplitting` gives a finite Galois extension `L` over which `T₀` splits.
    `L` is a number field by `NumberField.of_module_finite`. `T₀` is affine and smooth by
    `IsTorus.isConnectedReductive_of_fieldSplitting`.
  - `maximalTorusBaseChange` shows that `i₀_L` is a maximal torus of `G_L`. This gives the
    model `D` with `D.carrier = L`, `D.torus = T₀_L` and `D.inclusion = i₀_L`.
  - `IsSplitTorus.exists_genericCocharacter` gives a generic cocharacter `ν` of `i₀_L`.
  - Lemma Q (`splitBorelGaloisRootAction`, module `AdelicGaloisRootActionProof`) gives `m`, `τ`
    and the Galois root action. `hasGaloisBorelTwisting_of_rootAction` then finishes the proof.
