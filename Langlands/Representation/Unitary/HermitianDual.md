# Hermitian identification of admissible representations with their smooth duals

Author: Worker 249.

This helper module constructs, for an invariant positive form `b` on a complex
representation `ρ` of a topological group `G`, the map

`v ↦ b(v, -)`

into the actual smooth dual `SmoothDual ρ`, and proves that it is an
equivariant conjugate-linear equivalence when `ρ` is admissible and compact
open subgroups of `G` are cofinal among its open subgroups. It is the generic
input to the closing theorem in
[UnitaryAdmissibleHermitianProof.md](../Classification/UnitaryAdmissibleHermitianProof.md).

No norm, topology, completion or finite-dimensionality is imposed on the
carrier `V`. The group, the carrier and the auxiliary finite-dimensional space
in the Riesz lemma have independent universes. The form is the published
`InvariantPositiveForm`, which is conjugate-linear in its first argument and
linear in its second.

## Declarations

All declarations are in namespace `Langlands`.

| Declaration | Content |
| --- | --- |
| `InnerProductSpace.Core.exists_inner_eq_of_finiteDimensional` | On a finite-dimensional complex space with an algebraic inner-product core `c`, every linear functional `φ` equals `x ↦ c(u, x)` for some vector `u`. |
| `InvariantPositiveForm.rightFunctional` | The linear functional `w ↦ b(v, w)` in `Module.Dual ℂ V`, with `rightFunctional_apply`. |
| `InvariantPositiveForm.rightFunctional_add`, `rightFunctional_smul` | `b((v + v'), -) = b(v, -) + b(v', -)` and `b(c • v, -) = conj(c) • b(v, -)`. |
| `InvariantPositiveForm.dual_rightFunctional` | For the algebraic dual action `ρ.dual`, `ρ.dual g (b(v, -)) = b(ρ g v, -)`. |
| `InvariantPositiveForm.rightFunctional_mem_smoothVectors` | If `ρ` is smooth, every `b(v, -)` is a smooth vector of `ρ.dual`. |
| `InvariantPositiveForm.toSmoothDual` | The conjugate-linear map `V →ₗ⋆[ℂ] SmoothDual ρ`, `v ↦ b(v, -)`, for smooth `ρ`. |
| `InvariantPositiveForm.smoothDualPairing_toSmoothDual` | `smoothDualPairing ρ (b.toSmoothDual hρ v) w = b.inner v w`, by definition. |
| `InvariantPositiveForm.toSmoothDual_apply_action` | `b.toSmoothDual hρ (ρ g v) = smoothContragredient ρ g (b.toSmoothDual hρ v)`. |
| `InvariantPositiveForm.toSmoothDual_injective` | The map is injective, for every smooth `ρ`. |
| `InvariantPositiveForm.toSmoothDual_surjective` | The map is surjective if `ρ` is admissible and compact open subgroups are cofinal. |
| `InvariantPositiveForm.smoothDualEquiv` | The resulting equivalence `V ≃ₗ⋆[ℂ] SmoothDual ρ`, with `smoothDualEquiv_apply`. |

The cofinality hypothesis of `toSmoothDual_surjective` and `smoothDualEquiv` is written
out as
`∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K`.
This is the body of the published abbreviation `CompactOpenCofinal G`, so the
published `GeneralLinear.compactOpen_cofinal F T n` supplies it directly for
`GL_n(F)`. The injectivity, equivariance and pairing results do not use this
hypothesis; they need only smoothness of `ρ`.

## Implemented proofs

**Riesz lemma.** The core `c` induces Mathlib's normed group
(`InnerProductSpace.Core.toNormedAddCommGroup`) and inner-product space
(`InnerProductSpace.ofCore`) structures on `U`. These are local instances
inside the proof only; the statement involves just the algebraic core. A
finite-dimensional space is complete (`FiniteDimensional.complete`), so
Mathlib's `InnerProductSpace.toDual` is an equivalence. The vector `u` is the
preimage of `φ`, regarded as a continuous linear map by
`LinearMap.toContinuousLinearMap`, and `InnerProductSpace.toDual_symm_apply`
gives `c(u, x) = φ x`.

**The functional and its smoothness.** Linearity of `b(v, -)` is the right
additivity and right scalar identity of Mathlib's inner-product core.
Additivity and conjugate scalar behavior in `v` come from the fields
`add_left` and `smul_left` of the form. For equivariance, evaluation at `w`
reduces `ρ.dual g (b(v, -))` to `b(v, ρ(g⁻¹) w)`. Invariance of `b` under
`ρ(g)` rewrites this as `b(ρ(g) v, ρ(g) ρ(g⁻¹) w) = b(ρ(g) v, w)`. If an open
subgroup `K` fixes `v`, then for `k ∈ K` this identity gives
`ρ.dual k (b(v, -)) = b(ρ(k) v, -) = b(v, -)`. So `b(v, -)` is smooth and
`toSmoothDual` is well defined. Its equivariance for `smoothContragredient` is
the same identity, read in the smooth-part subtype.

**Injectivity.** If `b(v, -) = 0`, evaluating at `v` gives `b(v, v) = 0`, and
the field `definite` gives `v = 0`.

**Surjectivity.** Let `ℓ` be a smooth functional, fixed by an open subgroup
`H`. Cofinality gives a compact open subgroup `K ≤ H`; `ℓ` is then fixed by
`K` in `smoothContragredient ρ`. Admissibility makes
`U = fixedVectors ρ K` finite-dimensional. Restricting `b` to `U` gives an
inner-product core on `U`. Definiteness on `U` follows from definiteness on
`V` and injectivity of the subtype. The Riesz lemma, applied to the restriction
of `ℓ` to `U`, gives `u ∈ U` with `b(u, x) = ℓ(x)` for every `x ∈ U`.
Since `u` is `K`-fixed, `b(u, -)` is `K`-fixed by the equivariance identity.
Thus `b(u, -)` and `ℓ` are two `K`-fixed smooth functionals with the same
restriction to `U`. The published
`smoothDualFixedRestriction_bijective ρ hρ K hK` states that
`smoothDualFixedRestriction ρ K`, restriction of `K`-fixed smooth functionals
to `K`-fixed vectors, is bijective for compact open `K`. Its injectivity gives
`b(u, -) = ℓ`. That published result is proved by compact-open orbit
averaging; this module reuses it without repeating the averaging argument.

**Equivalence.** `smoothDualEquiv` is `LinearEquiv.ofBijective` applied to
`toSmoothDual`, so it applies as `v ↦ b(v, -)` by definition.

## Provenance

The provenance is internal. The construction is the standard identification of
an admissible unitary representation with the smooth dual of its complex
conjugate, by the form `v ↦ b(v, -)`. Here it is assembled from the published
smooth-dual and fixed-vector definitions, the published compact fixed-space
duality theorem, and Mathlib's finite-dimensional Riesz representation. No
literature theorem is cited as an unproved input. The module does not use a
Hilbert completion or an infinite-dimensional Riesz theorem, and it does not
assert an ordinary linear self-contragredience.
