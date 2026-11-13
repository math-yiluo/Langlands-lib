# The identity component of the split orthogonal group is semisimple

This internal module proves that, over every field `k` and for an index type `l` with at
least two elements, the identity component of the split orthogonal group
`OrthogonalMatrix.groupScheme l k` is semisimple and nontrivial. It also reduces absolute
almost simplicity over every field to almost simplicity over algebraically closed fields.
Semisimplicity uses the published root-datum criterion (Milne, *Algebraic Groups*,
Proposition 21.48 with Definition C.34, formalized as `splitSemisimpleRootDatum`): a split
connected reductive group is semisimple when its roots span a subgroup of finite index of
the character lattice.

## Root span

- `two_smul_mem_span_roots`: twice every character of the diagonal torus lies in the
  `ℤ`-span of its roots. For each index `a` pick `b ≠ a`; then
  `2e_a = (e_a - e_b) + (e_a + e_b)` is a sum of two roots (`mem_roots_iff` from
  `OrthogonalMatrix.Roots`, with `w(inl a) = e_a`, `w(inr b) = -e_b`). The characters `x`
  with `2x` in the span form a subgroup containing the coordinate basis `e_a`, hence
  everything.
- `finite_quotient_rootSpan`: for any root datum `P` whose roots are the roots of the
  diagonal torus, the quotient `X ⧸ P.rootSpan ℤ` is finite. The map
  `(l → ZMod 2) → X ⧸ P.rootSpan ℤ`, `n ↦ [Σ_a val(n_a) e_a]`, is surjective: a character
  with coordinates `c` differs from the image of `c mod 2` by `2 · Σ_a ⌊c_a / 2⌋ e_a`.

## Semisimplicity and nontriviality

- `isSemisimple_identityComponent l k`: the identity component is semisimple. It is
  connected reductive (`isConnectedReductive_identityComponent`, module
  `OrthogonalMatrix.Reductive`), the diagonal torus factored through it is a split maximal
  torus (`isMaximalTorus_identityTorus`), the published `rootDatumExistence` gives a root
  datum whose roots are those of the diagonal torus (`roots_identityTorus`), and the
  quotient of the character lattice by its root span is finite.
- `range_id_identityComponent_ne_bot l k`: the identity component is nontrivial. The
  constant point of `upper(E_ab - E_ba)` for `a ≠ b` lies in the identity component
  (`constantPoint_upper_mem`), and its matrix has entry `1` at `(inl a, inr b)`, where the
  identity matrix has `0`. Since the global sections of `Spec k` form a field, the
  point is not the identity.

## Base change

- `isAbsolutelyAlmostSimple_of_isAlmostSimple l h K`: if the identity component of the
  split orthogonal group is almost simple over every algebraically closed field, then over
  every field `K` it is absolutely almost simple. The base change of the identity
  component to an algebraic closure of `K` is identified with the identity component of the
  model over that closure (published `IdentityComponent.baseChangeIso`,
  `IdentityComponent.mapIso` applied to `baseChangeModelIso`, and `IsAlmostSimple.of_iso`).
  Almost simplicity then descends to `K` (published `IsAlmostSimple.of_fieldExtension`).
