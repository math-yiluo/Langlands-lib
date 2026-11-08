# A unitary criterion for contragredient realizations

This module proves that a positive definite invariant form, together with a
finiteness condition called joint admissibility, identifies the contragredient
of an actual automorphic realization with any realization obtained from it by
a conjugate-linear bijection. The abstract part is stated for a smooth
representation `ρ` of a topological group `G` and a representation `κ` of a
group `K` on the same complex vector space. The concrete part applies it to
the Library's full-operator realizations `OperatorRealization F n`, with
`ρ = S.finiteRepresentation` of `GL_n(𝔸_{F,f})` and
`κ = S.compactRepresentation` of the standard compact subgroup `K_∞` of
`GL_n(F ⊗ ℝ)`. Nothing here asserts that any cuspidal realization is unitary
or admissible. Those are separate inputs.

## Joint admissibility

- `jointMultiplicitySpace ρ κ L σ`, for a subgroup `L` of `G` and a
  representation `σ` of `K` on `Fin m → ℂ`, is the subspace of linear maps
  `φ : (Fin m → ℂ) → V` such that every value `φ v` is fixed by `L` under `ρ`
  and `φ (σ k v) = κ k (φ v)` for all `k`. These are the `K`-equivariant maps
  from `σ` into the `L`-fixed vectors `V^L`.
- `IsJointlyAdmissible ρ κ` says that for every open subgroup `L` of `G`,
  every `m` and every representation `σ` of `K` on `Fin m → ℂ`, the space
  `jointMultiplicitySpace ρ κ L σ` is finite-dimensional.
- `OperatorRealization.IsJointlyAdmissible S` is
  `IsJointlyAdmissible S.finiteRepresentation S.compactRepresentation`.

For the realizations used here this is the usual admissibility of a
`(𝔤, K_∞) × GL_n(𝔸_{F,f})`-module: for each open subgroup `L` and each
irreducible continuous representation `τ` of `K_∞`, the `τ`-isotypic part of
`V^L` is finite-dimensional. This equivalence is not proved in Lean, and only
the definition above is used. The reason it holds: every vector is
`K_∞`-finite and the compact group acts continuously on each finite orbit
span, so `V^L` is a direct sum of its isotypic parts. A map out of a
finite-dimensional `σ` lands in finitely many of them. Each multiplicity
space is a finite sum of spaces `Hom_K(σ, V^L[τ])`, and these are
finite-dimensional when the isotypic parts are; taking `σ = τ` gives the
converse. The Hom form needs no continuity or irreducibility of `σ`, and that
is why it is used.

`conjugateTransport γ σ` transports a representation `σ` along a
conjugate-linear equivalence `γ`, by `k ↦ γ ∘ σ k ∘ γ⁻¹`. Each such operator
is complex linear, because two conjugations cancel. The main proof uses it.

## Riesz representation on finite-dimensional subspaces

Let `b : InvariantPositiveForm ρ`, with `b.inner` conjugate-linear in the
first variable.

- `inner_add_left'`, `inner_smul_left'`, `inner_add_right'` and
  `inner_smul_right'` are the sesquilinearity rules.
- `eq_of_inner_eq`: two vectors of a subspace `U` that have the same inner
  products with every vector of `U` are equal. Their difference lies in `U`,
  and definiteness applies.
- `exists_inner_eq U hU l`: if `U` is finite-dimensional, every linear
  functional `l` on `V` agrees on `U` with `b.inner g ·` for some `g ∈ U`. The
  proof transports `U` into `b.NormedCarrier`, the inner product space carried
  by `V` (`Langlands/Representation/Unitary/Completion.lean`). There the
  finite-dimensional subspace is complete, and Mathlib's
  `InnerProductSpace.toDual` applies.
- `rieszVector U hU l` is the chosen `g`. By `eq_of_inner_eq` it is unique
  (`eq_rieszVector`). It is additive and conjugate-homogeneous in `l`, and
  these facts assemble into the conjugate-linear `rieszMap U hU`.
- `rieszVector_dual`: suppose `κ` preserves the form and `U` is
  `κ`-stable. Then the Riesz vector of `κ.dual k l` is `κ k` applied to the
  Riesz vector of `l`.

## The conjugate pairing

Let `c : V ≃ₛₗ[starRingEnd ℂ] W` be conjugate-linear. Then
`conjPairing b c y x = b.inner (c⁻¹ x) y` is complex bilinear in `(y, x)`.

- `symm_comm` passes commutation with `c` to `c⁻¹`.
- `conjPairing_invariant`: operators `α h` on `V` that preserve the form,
  and operators `β h` on `W` with `β h ∘ c = c ∘ α h`, leave the pairing
  invariant.
- `conjPairing_skew`: if `D` is skew for the form and `D' ∘ c = c ∘ D`, then
  `B (D y) x + B y (D' x) = 0`.
- `conjPairing_flip_injective`: `x ↦ B (·) x` is injective, by
  definiteness.
- `conjPairing_flip_dual` and `conjPairingIntertwining`: the partial map
  intertwines `β` with the dual of `α`.

## Every contragredient functional is represented

`exists_inner_eq_of_contragredient` has these hypotheses. `ρ` is smooth, `κ`
preserves `b`, `ρ` and `κ` commute, every vector is `κ`-finite, every open
subgroup of `G` contains a compact open subgroup, and `(ρ, κ)` is jointly
admissible. Then every `l` that is `ρ.dual`-smooth and `κ.dual`-finite has the
form `b.inner g ·` for a single vector `g`.

The Lean proof goes as follows.

1. Choose an open `L` fixing `l` and a compact open `L₀ ≤ L`. Let `Λ` be the
   `κ.dual`-orbit span of `l`, which is finite-dimensional. Choose a basis of
   `Λ` and compose its coordinates with complex conjugation. This gives a
   conjugate-linear `γ : Λ ≃ Fin m → ℂ`. Transport the action of `K` on `Λ`
   along `γ` to get `σ'` on `Fin m → ℂ`.
2. Let `U` be finite-dimensional, `κ`-stable and contained in `V^{L₀}`. By
   `rieszVector_dual`, the map `v ↦ rieszVector U (γ⁻¹ v)` is a
   complex-linear element of `jointMultiplicitySpace ρ κ L₀ σ'`.
3. Let `M` be that multiplicity space, which is finite-dimensional by joint
   admissibility. Let `W` be the span of the values of the maps in `M` on the
   standard basis vectors. Then `W` is finite-dimensional, `κ`-stable and
   contained in `V^{L₀}`, and every `φ ∈ M` takes all its values in `W`. Take
   `g = rieszVector W l`.
4. Fix `y`. An open subgroup fixes `y`, so the `L₀`-orbit of `y` is finite
   (`L₀` is compact), and its `κ`-orbit spans give a finite-dimensional
   subspace `U_y` containing `y`. Since `ρ` and `κ` commute, `U_y` is stable
   under `κ` and under `L₀`. Put `U = U_y ⊔ W`. The Riesz vector `g'` of `l`
   in `U` is `L₀`-fixed, because `l` and `b` are `L₀`-invariant and the Riesz
   vector is unique. So `g'` is also the Riesz vector of `l` in
   `U ∩ V^{L₀}`, which is `κ`-stable. By step 2 it is a value of an element of
   `M`, so `g' ∈ W`, and uniqueness gives `g' = g`. Finally
   `b.inner g y = b.inner g' y = l y`, since `y ∈ U`.

## The criterion for automorphic realizations

- `OperatorRealization.exists_compact_openSubgroup_le`: every open subgroup
  of `GL_n(𝔸_{F,f})` contains a compact open subgroup, namely its
  intersection with `GL_n(\hat{𝒪}_F)` (`FiniteAdelicGL.standardIntegral`).
- `OperatorRealization.isContragredientOf_of_unitaryForm b hA c hfin hcpt hlie`
  takes a unitary form `b : S.UnitaryForm` (`OperatorUnitaryForm.lean`), joint
  admissibility of `S`, and a conjugate-linear bijection
  `c : S.Space ≃ₛₗ[starRingEnd ℂ] T.Space`. The bijection must satisfy
  `T.finiteRepresentation d (c f) = c (S.finiteRepresentation d f)`, the same
  identity for `compactRepresentation k`, and the same for `lieAction X` for
  every real Lie algebra element `X`. The conclusion is
  `T.IsContragredientOf S`, through the pairing
  `B y x = b.inner (c⁻¹ x) y`.

  Invariance comes from `conjPairing_invariant`, applied to the finite form
  and the compact invariance of `b`, and from `conjPairing_skew` with
  `b.real_skew`. Each `B (·) x` is a contragredient functional: smoothness
  maps across the intertwiner (`isSmoothVector_map`) and finiteness across
  `IsFiniteVector.map`. Injectivity is `conjPairing_flip_injective`.
  Surjectivity is `exists_inner_eq_of_contragredient`, which gives
  `l = B (·) (c g)`. It uses the Library facts `finiteRepresentation_isSmooth`,
  `compactRepresentation_isFiniteVector` and
  `finiteRepresentation_compactRepresentation`.

## Provenance

The content is internal. It is the standard argument that a unitary
admissible representation has its complex conjugate as contragredient
(compare Borel–Jacquet 1979, §4.6, and Getz–Hahn 2024, §6.3, cited by the
target statement `CuspidalUnitaryContragredientExistenceStatement`). The proof
avoids orthogonal projections and Hilbert completions: it uses Riesz
representation only on finite-dimensional subspaces, and joint admissibility
bounds the subspaces needed. The definitions `jointMultiplicitySpace` and
`IsJointlyAdmissible` are introduced here as the form of admissibility that
this argument uses.
