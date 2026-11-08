# Hermitian representations: statements

Author: Worker 6. Module `Langlands.Representation.Unitary.HermitianRepresentationStatements`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.2.1, Definition and Remarks 1–2, printed pp.96–97 / PDF pp.102–103. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This is a statement unit: nothing is proved.

## The source

For a complex vector space `V`, Renard writes `V̄` for `V` with the conjugated scalar multiplication. For a smooth representation `(π, V)`, `(π̄, V̄)` is `π` acting on `V̄`, and the hermitian contragredient is `(π^h, V^h) = (π̃̄, Ṽ̄)`, the conjugate of the smooth dual.

- **Definition.** `(π, V)` is hermitian if there is a nondegenerate hermitian form `⟨·,·⟩` on `V` with `⟨v, w⟩ = ⟨π(g) v, π(g) w⟩` for all `v, w ∈ V` and `g ∈ G`.
- **Remark 1.** If `(π^h, V^h)` is isomorphic to `(π, V)`, then `π` is hermitian: "the canonical duality between `V` and `V^h` gives such a form". Conversely, if `π` is admissible and hermitian, the form induces an injection `V̄ ↪ Ṽ`, and admissibility makes it an isomorphism `V̄ ≃ Ṽ`, so `(π^h, V^h) ≃ (π, V)`.
- **Remark 2.** If `π` is irreducible, admissible and hermitian, every other nondegenerate `G`-invariant hermitian form on `V` is a nonzero scalar multiple of `⟨·,·⟩`, by Proposition III.1.9 (Schur's lemma).

## Conventions in Lean

Lean has no separate type `V̄`. A `ℂ`-linear map out of `V̄` is a conjugate-linear map out of `V`, so the following translations are used.

- **Forms.** A sesquilinear form is `B : π →ₗ⋆[ℂ] π →ₗ[ℂ] ℂ`, conjugate-linear in the first variable and linear in the second, as for the published `InvariantPositiveForm`. It is *invariant hermitian nondegenerate* when:
  - `B y x = conj (B x y)` for all `x, y`;
  - `(∀ y, B x y = 0) → x = 0`;
  - `B (π g x) (π g y) = B x y` for all `g`, `x`, `y`.
  For a hermitian form, nondegeneracy in the first variable is equivalent to nondegeneracy in the second. These three conditions are Renard's Definition, which is not introduced as a separate Lean definition.
- **`π^h ≅ π`.** An isomorphism `V^h → V` of representations is a `ℂ`-linear `G`-isomorphism `Ṽ̄ → V`. Its inverse is a `G`-equivariant conjugate-linear bijection `e : π ≃ₗ⋆[ℂ] SmoothDual π.representation` with `e (π g x) = π̃ g (e x)`, where `π̃` is the published `smoothContragredient`. The statements use this form.

The group hypotheses are a Hausdorff, locally compact, totally disconnected topological group `G`, i.e. Renard's t.d. groups. Representations are `π : SmoothRep.{0, u, v} ℂ G`.

## The Lean statements

### `HermitianOfSelfDualStatement` (Remark 1, first assertion)

If some `e` as above exists, then some invariant hermitian nondegenerate `B` exists. No hypothesis is added to the source.

Renard's one-line argument takes the form `B₀(x, y) = e(x)(y)` given by the canonical duality. That form is invariant, sesquilinear and nondegenerate, but it need not be hermitian. The following route to a hermitian form is recorded for the proof; it is not formalized.

- The existence of `e` forces admissibility, because `e` maps `V^K` bijectively onto `Ṽ^K ≅ (V^K)*`.
- `B₀*(x, y) = conj B₀(y, x)` is another invariant nondegenerate form, so `B₀*(x, y) = B₀(T x, y)` for a `G`-equivariant linear automorphism `T` of `V`. `T` preserves every finite-dimensional `V^K`, so `V` is the direct sum of the generalized eigenspaces of `T`, which are subrepresentations. One checks `B₀(T x, T y) = B₀(x, y)`, so `B₀` pairs the generalized eigenspace for `c` only with the one for `1 / c̄`.
- On each `G`-stable sum of the generalized eigenspaces for `c` and `1 / c̄`, the hermitian form `t B₀ + t̄ B₀*` is nondegenerate except for finitely many `t` with `|t| = 1`. Choosing `t` piece by piece and adding the pieces orthogonally gives the required `B`.

### `SelfDualOfHermitianStatement` (Remark 1, converse)

Let `π` be admissible and let `B` be invariant hermitian nondegenerate. Then there is a `G`-equivariant conjugate-linear bijection `e : π ≃ₗ⋆[ℂ] SmoothDual π.representation` with `e x = B(x, ·)` for all `x`, i.e. `(e x) y = B x y`. This is Renard's isomorphism `V̄ ≃ Ṽ`, and hence `π^h ≅ π`.

### `HermitianFormUniquenessStatement` (Remark 2)

Let `π` be irreducible and admissible, and let `B` and `B'` be two invariant hermitian nondegenerate forms. Then there is a real `c ≠ 0` with `B' x y = c · B x y` for all `x, y`. Renard says "a nonzero scalar". The scalar is automatically real, because both forms are hermitian and `B ≠ 0` when `V ≠ 0`. When `V = 0`, any `c` works.

`HermitianRepresentationStatements` is the conjunction of the three statements.

## Not stated here

- (IV.2.1.1)–(IV.2.1.2), normalized induction `i_H^G τ = ind_H^G(τ ⊗ δ_{H\G}^{1/2})` from a closed subgroup with compact quotient `H \ G` and its compatibility with `~` and `h`, are not restated. The contragredient part, for a closed subgroup with compact quotient and a continuous section of the Levi projection, is the published `Induction.exists_integralDualEquiv_of_section` (module `Induction/CompactQuotientSmoothDuality`, a proved theorem). The hermitian part follows by complex conjugation, which commutes with induction.
- The positive-definite (unitary) case is the published `IsUnitarizable` and `InvariantPositiveForm` (module `Unitary/Basic`). Uniqueness of positive forms on irreducible admissible representations is in `Unitary/AdmissibleFormUniqueness`.
- The proofs are not formalized here.
