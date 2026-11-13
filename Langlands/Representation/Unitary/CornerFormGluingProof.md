# Proof of the corner-form gluing statement

Author: Worker 4713.

The theorem `Langlands.CornerFormGluing.cornerFormGluing` has type
`Langlands.CornerFormGluingStatement.{uG, uV}`. It proves the published
statement in `Langlands/Representation/Unitary/CornerFormGluingStatement.lean`.

## Scope

The premises are exactly those of the statement:

- a topological group `G` with a Haar measure `μ` that is right invariant
  and inversion invariant;
- a smooth complex representation `ρ` on `V`;
- a compact open `K₀` with a nonzero `K₀`-fixed vector `v₀`;
- for every compact open `K ≤ K₀`: `ρ^K` is finite-dimensional, simple over
  the corner `e_K H(G) e_K` with the Library's `cornerModule`, and carries
  some corner-adjoint `InnerProductSpace.Core`.

The forms at different levels are not assumed compatible. The conclusion is
`IsUnitarizable ρ`.

## Dependencies

- `Langlands/Representation/Unitary/CornerFormGluing.lean` (submitted with
  this proof): `isUnitarizable_of_compatibleCornerForms` glues a
  corner-adjoint family that is compatible under restriction.
- `Langlands.PositiveTraceForms.StarInvariantForm.inner_mul_inner_eq` in
  `Langlands/LinearAlgebra/PositiveTraceForms.lean`, by Worker 5219. If `A` is
  a complex `*`-algebra and `V` is a finite-dimensional simple `A`-module,
  then any two `*`-invariant positive definite forms `b, b'` on `V` satisfy
  `b(v₀,v₀) b'(x,w) = b'(v₀,v₀) b(x,w)`.

## Helper constructions

In namespace `Langlands.CornerFormGluing`:

- `scaleCore b r hr` is the form `r · b` for a real `r > 0`. It is again an
  `InnerProductSpace.Core`.
- `comapCore b e he` is the pullback of `b` along an injective linear map
  `e`.
- `inner_self_eq_ofReal_re` and `re_inner_self_pos`: diagonal values are
  real, and positive at nonzero vectors.
- `normalizeCore b hx = scaleCore b (re b(x,x))⁻¹`. By
  `normalizeCore_inner_self`, it takes the value `1` at `(x, x)`.
- `star_inclusion`: the involution commutes with
  `Corner.inclusion : Corner K → Corner L` for `L ≤ K`. Both sides have the
  same image in `H(G)`.
- `toStarInvariantForm` packages a corner-adjoint form as a
  `StarInvariantForm` for the corner module. Then `inner_mul_inner_eq`
  specializes Worker 5219's uniqueness theorem to `ρ^K`, using
  `cornerModule_isScalarTower`.
- `fixedInclusion ρ hLK : ρ^K →ₗ ρ^L` is the inclusion of fixed spaces, and
  `fixedInclusion_injective` shows it is injective.
- `comapCore_adjoint`: if a form on `ρ^L` is adjoint for the `L`-corner, its
  pullback to `ρ^K` is adjoint for the `K`-corner. The inclusion intertwines
  the `K`-corner action with the action of its image in the `L`-corner
  (`cornerAction_refinement`). With `star_inclusion`, the `L`-adjointness
  transfers.

## Implemented proof

Choose a form `b K` at every level (`choose`).

1. *Normalization.* For compact open `K ≤ K₀`, `v₀` lies in `ρ^K` and is
   nonzero. Put `B K = normalizeCore (b K)` at `v₀`, so
   `B K (v₀, v₀) = 1`. `B K` is a positive real multiple of `b K`, so it is
   still corner-adjoint (`hB`).
2. *Compatibility.* Let `L ≤ K ≤ K₀` be compact open. The pullback of `B L`
   along `ρ^K → ρ^L` is corner-adjoint for the `K`-corner (`comapCore_adjoint`).
   Since `ρ^K` is finite-dimensional and simple, `inner_mul_inner_eq` applied
   to `B K`, this pullback and the vector `v₀` gives
   `B K(v₀,v₀) · B L(v,w) = B L(v₀,v₀) · B K(v,w)`. Both diagonal values are
   `1`, so `B L(v,w) = B K(v,w)` for `v, w ∈ ρ^K`.
3. *Gluing.* Apply `isUnitarizable_of_compatibleCornerForms` to the family
   `B` with `hB` and the compatibility from step 2.

## Provenance

The statement's Markdown records its derivation from steps 4 and 5 of the
outline in `CharacterLimitSubquotientsStatement.md` and from Tadic 1986,
proof of Theorem 2.7 (printed p.349). The normalization in steps 1–2 above
replaces Tadic's compatibility by construction. It is the route described in
the statement's Markdown. The gluing and invariance arguments are in
`CornerFormGluing.md`.

## Validation

`lean_check` diagnostic `69c731ca-4353-498b-a13b-3b644e55c619` compiled this
module and `CornerFormGluing` without errors or warnings. The axioms of
`Langlands.CornerFormGluing.cornerFormGluing` were `propext`,
`Classical.choice` and `Quot.sound`.
