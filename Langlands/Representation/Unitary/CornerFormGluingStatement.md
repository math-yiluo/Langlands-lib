# Gluing corner-adjoint forms on fixed vectors

Authors: Worker 4713. The hypothesis interface was requested by Worker 5667.

This module states
`Langlands.CornerFormGluingStatement.{uG, uV}`
in `Langlands/Representation/Unitary/CornerFormGluingStatement.lean`.
**It is not proved here.** It is a Prop-valued definition. It has no axioms,
no `sorry` and no assumed structure fields. The group universe `uG` and the
carrier universe `uV` are independent level parameters.

## The Lean proposition

The statement quantifies over the following data, in this order.

- A group `G : Type uG` with a topology making it a topological group, and a
  measurable structure on `G` that is its Borel structure (`BorelSpace`). No
  Hausdorff, local compactness or total disconnectedness assumption is made.
- A measure `μ` with `μ.IsHaarMeasure` (a left Haar measure),
  `μ.IsMulRightInvariant` and `μ.IsInvInvariant`. So `μ` is a two-sided Haar
  measure invariant under inversion. For a locally compact group and a regular
  `μ`, the last property follows from the first two
  (`Langlands.isInvInvariant_of_isMulRightInvariant`).
- A complex vector space `V : Type uV` (only its additive group and its complex
  module structure, no norm or topology) and a representation
  `ρ : Representation ℂ G V` with `hρ : IsSmooth ρ`. Smoothness means that
  every vector is fixed by some open subgroup.
- An open subgroup `K₀` of `G` whose underlying set is compact.

Under the following hypotheses:

1. some nonzero vector `v₀` lies in `fixedVectors ρ K₀.toSubgroup`, the space
   `ρ^{K₀}` of `K₀`-fixed vectors;
2. for every compact open subgroup `K ≤ K₀`, the space `ρ^K` is
   finite-dimensional over `ℂ`;
3. for every compact open subgroup `K ≤ K₀`, the space `ρ^K` is a simple
   module (`IsSimpleModule`) over the corner algebra
   `Hecke.HeckeAlgebra.Corner μ K hK`, for the Library's actual corner module
   structure `Hecke.cornerModule μ ρ hρ K hK`;
4. for every compact open subgroup `K ≤ K₀`, there is a positive definite
   Hermitian form `b : InnerProductSpace.Core ℂ (fixedVectors ρ K.toSubgroup)`
   such that for every corner element `f` and all `x, y ∈ ρ^K`,
   `b.inner (cornerAction f x) y = b.inner x (cornerAction (star f) y)`.

The conclusion is `IsUnitarizable ρ`: the carrier `V` has a positive definite
Hermitian form `⟨-, -⟩` with `⟨ρ g v, ρ g w⟩ = ⟨v, w⟩` for all `g`, `v`, `w`.
No completion, norm or topology is chosen.

The Library objects have the following meaning.

- `Hecke.HeckeAlgebra.Corner μ K hK` is the corner `e_K H(G) e_K` of the Hecke
  algebra of locally constant compactly supported functions under
  `μ`-convolution, where `e_K = μ(K)⁻¹ 1_K`. Its elements are the
  `K`-bi-invariant test functions, and `e_K` is its unit.
- `Hecke.cornerAction μ ρ hρ K hK f` is the restriction to `ρ^K` of the
  integrated operator `v ↦ ∫ f(g) ρ(g) v dμ(g)`.
  `Hecke.cornerModule` is the module structure given by this action.
- `star f` is the corner involution of `Hecke/UnimodularStar.lean`, namely
  `f*(g) = conj (f(g⁻¹))`.
- `InnerProductSpace.Core` is Mathlib's algebraic inner-product structure:
  conjugate symmetry, nonnegative real part on the diagonal, additivity,
  conjugate-linearity in the first argument and definiteness.
  Hypothesis 4 is the adjoint relation `(ρ(f)x, y) = (x, ρ(f*)y)`. This
  relation reads the same in either sesquilinearity convention.

## Provenance

This is a derived statement. It isolates steps 4 and 5 ("Gluing" and
"Invariance") of the outline in
`Langlands/Representation/Unitary/CharacterLimitSubquotientsStatement.md`,
which adapts the proof of Theorem 2.7 in Marko Tadic, *Classification of
unitary representations in irreducible representations of general linear
group (non-archimedean case)*, Ann. Sci. ENS (4) 19 (1986), 335–382
(`tadic-1986-unitary`, printed p.349 / PDF p.16). Tadic builds compatible
inner products on the fixed spaces `V_0^{K_k}` of a descending basis of compact
open subgroups, together with the relation
"`(π₀(f)u, w) = (u, π₀(f*)w)` for `f ∈ H(G)`, `u, w ∈ V₀`". He concludes:
"From this one obtains directly that the inner product on `V₀` is
`G`-invariant."

The Lean statement differs from the source in these ways.

- *Forms are given level by level, without compatibility.* Tadic's limiting
  forms are compatible by construction. Here each `ρ^K` carries some
  corner-adjoint form, chosen independently at each level. Compatibility is
  not assumed. Hypotheses 1–3 replace it: on a finite-dimensional simple
  corner module, a corner-adjoint positive form is unique up to a positive
  scalar, so normalizing at `v₀` makes the forms compatible. This normalization
  step is step 4 of the outline, not a statement of Tadic.
- *General group.* In Theorem 2.7, `G` is the group of `F`-rational points
  of a connected reductive linear algebraic group over the non-archimedean
  local field `F` (§2.6, printed p.346 / PDF p.13). Tadic returns to
  `GL(n, F)` only in §2.9 (printed p.350), where Proposition 2.9 applies the
  theorem. The Lean statement uses only a topological group with a two-sided,
  inversion-invariant Haar measure and a compact open subgroup `K₀`. It
  assumes no algebraic-group structure.
- *Corners instead of `H(G)`.* The adjoint relation is assumed only for the
  corners `e_K H(G) e_K` with `K ≤ K₀`, not for all of `H(G)`. Step 5 of the
  outline uses only elements `e_L ⋆ δ_g ⋆ e_L` of such corners.

## Why the statement is true (outline for the proof)

Normalize the form at each level `K ≤ K₀` so that `⟨v₀, v₀⟩_K = 1`. If
`L ≤ K ≤ K₀`, then the restriction of the `L`-form to `ρ^K ⊆ ρ^L` is
corner-adjoint for the `K`-corner, because the `K`-corner sits inside the
`L`-corner and acts compatibly. By uniqueness it equals the `K`-form. Define
`⟨v, w⟩` as the value of the form at any compact open `K ≤ K₀` fixing `v` and
`w`; smoothness provides such `K`. For `g ∈ G`, take `L ≤ K ∩ gKg⁻¹`. The
corner element `e_L ⋆ δ_g ⋆ e_L` acts on `ρ^L` as `ρ(g)` followed by the
projection to `ρ^L`. Its involution acts as `ρ(g⁻¹)` followed by the same
projection. This uses the right invariance of `μ`. The adjoint relation on
`ρ^L` then gives `⟨ρ(g)v, ρ(g)w⟩ = ⟨v, w⟩`.

## Consumer

The intended consumer is the proof of
`Langlands.UnitaryCharacterLimitSubquotientsStatement` (steps 4 and 5 of its
outline). That proof is used for the end-point clause of
`Langlands.Classification.ComplementarySeriesUnitarity` (Tadic 1986,
Proposition 2.9). There `ρ` is an irreducible admissible subquotient `τ`, and
`K₀` is any compact open subgroup with `τ^{K₀} ≠ 0`. Hypothesis 3 then follows
from `CompactCoefficientClass.isSimpleModule_fixedVectors`, and hypothesis 2
from admissibility.

## Validation

`lean_check` diagnostic `26ee08c4-52f0-44db-877e-5024c7ecb8f1` compiled this
module without errors or warnings. It reported a proposition-valued definition
with level parameters `uG` and `uV`. The only axioms were `propext`,
`Classical.choice` and `Quot.sound`. This check provides neither a proof nor
semantic acceptance.
