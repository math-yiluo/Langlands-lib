# Coefficient charts on a KP apartment

Author: Worker 47 (Task 6502).

This module supplies the generic part of a coefficient action on the reduced building
`ApartmentQuotient D.sharpFixerFamily` of a Kaletha–Prasad apartment datum
`D : KPApartmentData i ω`. Here `i : S → G` is a monomorphism from a commutative group scheme
over a field `k`. A *coefficient chart* along an automorphism `θ` of `G(k)` is explicit data
that transports apartment points along `θ`. The module proves that a family of such charts,
indexed by a group `Γ` acting on `G(k)` through `ρ : Γ →* MulAut G(k)`, is an instance of the
published `ApartmentQuotient.MovingSemilinearActionData D.sharpFixerFamily ρ`. That helper
structure (module `ApartmentQuotientMovingSemilinearAction`) then yields an action of `Γ` on the
reduced building.

Nothing here is specific to Galois groups or to unramified extensions. The intended use takes
`k = K`, a maximal unramified extension of a local field `F`, with `θ_σ` the conjugation
action of `σ ∈ Aut(K/F)` on `G(K)` and `s_σ = σ⁻¹` on `Kˣ`. Constructing the charts for that
case is separate work.

## Torus points (`section TorusPoints`)

- `torusCharacterValue χ t : kˣ` is the value of a character `χ ∈ X^*(S)` at a rational point
  `t ∈ S(k)`. It is defined as `rationalCharacterEval` of the rational character that
  corresponds to `χ` under `rationalCharacters.equivCharacterLattice S`.
- `torusCharacterValue_inv_comp`: precomposing `χ` with `e.inv` for an automorphism `e` of `S`
  evaluates `χ` at the image of `t` under `e.inv`.
- `torusCharacterValue_injective`: if `k` is infinite and `S` is a split torus, a character is
  determined by its values on `S(k)`. The proof uses `IsSplitTorus.hom_ext_kpoints`. That lemma
  needs `Gm` to be affine, which comes from `SplittingAssembly.isAffine_of_isTorus`.
- `rationalPoints_map_injective`: a morphism `i` whose underlying scheme map is a monomorphism
  is injective on rational points.
- `normalizerPoints_conj_map` and `normalizerPoints_inv_conj_map`: conjugation by `n` or by
  `n⁻¹`, for `n ∈ normalizerPoints i`, maps `i(S(k))` into itself. The image of `i t` under
  conjugation by `n` is `i` of the image of `t` under the normalizing automorphism
  `normalizingAut i n`.
- `weylAction_torusCharacterValue`: if `i t' = n⁻¹ (i t) n`, then
  `(weylAction i n χ)(t) = χ(t')`.
- `mem_normalizerPoints_of_conj`: over an infinite field, with `G` connected reductive and `i`
  a split subtorus, take `g ∈ G(k)` such that conjugation by `g` and by `g⁻¹` both map
  `i(S(k))` into itself. Then `g ∈ normalizerPoints i`. The proof uses the published
  description of the normalizer points over infinite fields, `normalizerPointsInfiniteField`.

## Charts (`structure KPApartmentData.CoefficientChart`)

For `θ : MulAut G(k)` and `s : kˣ → kˣ`, a chart `A : D.CoefficientChart θ s` has the following
fields:

- `c ∈ G(k)`, a correcting element. Write `Ψ(u) = c⁻¹ θ(u) c` (`A.conj`, built from
  `chartConj θ c`).
- `β : X^*(S) ≃ X^*(S)`, a relabelling of characters.
- `a : D.Apartment → D.Apartment`, the map on apartment points, subject to the transport
  formula `a_val`: `(a x)_b(Ψ u) = x_{β b}(u)` for every character `b` and every `u ∈ G(k)`.
  Here `x_b` is the root-function family of the apartment point `x`.
- `τ : S(k) ≃ S(k)`, subject to `torus`: `Ψ(i(τ t)) = i(t)`.
- `char`: `(β χ)(τ t) = s(χ(t))` for every character `χ` and `t ∈ S(k)`.

The structure has no fields about roots, root groups, normalizers or Weyl groups. Those
properties are proved from the fields above:

- `mem_relativeRoots_iff`: `β b` is a relative root if and only if `b` is. This uses the fact
  that an apartment point's family is `⊤` exactly away from the roots
  (`exists_ne_top`, `eq_top_of_not_mem_roots`), together with `Nonempty D.Apartment`.
- `conj_mem_rootGroupPoints_iff`: for a relative root `b`, `Ψ u ∈ U_b(k)` if and only if
  `u ∈ U_{β b}(k)`. This uses `eq_top_iff` and `eq_top_of_not_mem` of the root-datum
  valuations.
- `rootsEquiv`: the bijection of `relativeRoots i` induced by `β`.
- `val_eq_val_add_rootForm`: for any two apartment points,
  `x_α(g) = y_α(g) + rootForm α (x -ᵥ y)`.
- `rootForm_vsub`: `rootForm α (a x -ᵥ a y) = rootForm (β α) (x -ᵥ y)`.
- `norm_vsub`: when the relative roots are finite, `a` preserves the root-coordinate norm of
  differences, `‖a x -ᵥ a y‖ = ‖x -ᵥ y‖`, for the norm
  `RootTranslationMetric.normedAddCommGroup`. This follows from
  `RootTranslationMetric.norm_eq_of_rootForm_equiv`. It is the input the coefficient metric
  argument needs.
- `conj_mem_sharpFixer`: `Ψ` maps the sharp fixer of `{x}` into the sharp fixer of
  `{a x}`. The sharp fixer is the supremum of the root fixers, and `Ψ` maps the root fixer of
  `β b` at `x` into the root fixer of `b` at `a x`.
- Over an infinite field, with `G` connected reductive and `i` a split subtorus:
  - `conj_mem_normalizerPoints` and `normalizerMap`: `Ψ` maps `normalizerPoints i` into itself.
  - `β_weylAction`: `β (w(Ψ n) b) = w(n) (β b)`. Both sides are compared at torus points
    through `char`, `torus` and `torusCharacterValue_injective`.
  - `a_smul`: `a (n • x) = Ψ(n) • a x`.

## Coherence (`section Coherence`)

Take charts `A₁ : CoefficientChart θ₁ s₁`, `A₂ : CoefficientChart θ₂ s₂` and
`A₃ : CoefficientChart θ₃ s₃`, with `θ₃ = θ₁ ∘ θ₂`. Their defect is
`d = c₃⁻¹ θ₁(c₂) c₁` (`defect`).

- `conj_conj`: `Ψ₁(Ψ₂ u) = d⁻¹ Ψ₃(u) d`. This is pure algebra.
- `defect_conj_map` and `defect_inv_conj_map`: conjugation by `d` and by `d⁻¹` maps
  `i(S(k))` into itself.
- `defect_mem` and `defectPoint`: over an infinite field, `d ∈ normalizerPoints i`. Here
  `defectPoint A₁ A₂ A₃ hθ hG hi` is `d` as a normalizer point (`coe_defectPoint`).
- If moreover `s₃ = s₂ ∘ s₁`:
  - `β_comp`: `β₂ (β₁ (w(d⁻¹) b)) = β₃ b`. Both sides are compared as characters through their
    values on `S(k)`.
  - `a_mul`: `a₃ x = d • a₁ (a₂ x)`.

`refl D : D.CoefficientChart 1 id` is the identity chart (`c = 1`, `β = id`, `a = id`,
`τ = id`).

## Assembly

Let `k` be infinite, `G` connected reductive and `i` a split subtorus. Take a group `Γ`,
`ρ : Γ →* MulAut G(k)`, maps `s : Γ → kˣ → kˣ` with `s (σ τ) = s τ ∘ s σ`, and charts
`A σ : D.CoefficientChart (ρ σ) (s σ)` normalized by `(A 1).c = 1` and `(A 1).a = id`.
`CoefficientChart.movingSemilinearActionData` packages these as
`ApartmentQuotient.MovingSemilinearActionData D.sharpFixerFamily ρ`:

| helper field | value |
| --- | --- |
| `correction σ` | `(A σ).c` |
| `apartment σ` | `(A σ).a` |
| `normalizer_mem`, `normalizer_smul` | `conj_mem_normalizerPoints`, `a_smul` |
| `subgroup_mem` | `conj_mem_sharpFixer` |
| `defect σ τ` | `defectPoint (A σ) (A τ) (A (σ τ))` |
| `correction_mul`, `apartment_mul` | the definition of the defect, `a_mul` |

`coherent_hom` gives `ρ (σ τ) = ρ σ ∘ ρ τ` pointwise. The `@[simp]` lemmas
`movingSemilinearActionData_correction` and `movingSemilinearActionData_apartment` record
the first two fields.

The relation `s (σ τ) = s τ ∘ s σ` is the contravariant composition law. It holds for
`s_σ = σ⁻¹`, and `β_comp` needs it in this form: `s₃ = s₂ ∘ s₁` when `θ₃ = θ₁ ∘ θ₂`.

## Provenance

This module is internal infrastructure, not a formalization of a single statement in the
literature. It formalizes a standard step in the construction of the Galois action on the
Bruhat–Tits building of `G` over a maximal unramified extension (as used in Kaletha–Prasad's
unramified descent). An automorphism of the coefficients moves the reference torus. Correcting
by a group element returns it to the chosen apartment, and the corrections compose up to an
element of the normalizer. The Lean formulation is new. Correction elements, characters at
rational points, and normalizer-point defects replace the field-automorphism transport of whole
buildings, which the Library does not have for tori that are not defined over `F`.
