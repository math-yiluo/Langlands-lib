# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`

Ported for task `22877948-227b-4ad5-bdb3-e13f5ea18c3d` (separated commutative group algebraic
spaces over a field are schemes). Proof module (FLT `P2M/Sol/`) of finite-set Stacks Lemma
39.24.1 (Tag 03JE): invariant affine open neighbourhoods for a finite locally free equivalence
relation.

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation.lean` (SHA-256
`1cd32b6298149a1a0e8d7ded7c9308203ff40395bc14fc7e91d2f8c94f58f86c`) from the Anthropic Lean
formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`;
project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at
6e837e75355538c7f80bab5b956861e86c4eacc2", literature id
`anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the
changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped. The
  file uses none of its commands.
- No other change: the declarations, statements and proofs are the FLT text. With the project
  Mathlib it compiles with linter and deprecation warnings only (`haveI`/`letI` style,
  `Set.mem_setOf_eq`, `TensorProduct.induction_on`).

## Content

Setting: schemes `X`, `R` and `s t : R ⟶ X`. The hypothesis `hequiv` says that for every
scheme `T`, the relation "`x` and `y` are `s` and `t` of some `φ : T ⟶ R`" is an
equivalence relation on `T ⟶ X`.

- `cls s t w` is the orbit `t(s⁻¹{w})`. With `hequiv`, `mem_cls_self`, `exists_inv`,
  `cls_symm`, `cls_trans` and `cls_eq_of_mem` show that the orbits partition `X`.
- For `t` finite and an open `U`, `W' s t U` is the complement of the image under `t` of the
  complement of `s⁻¹U ∩ t⁻¹U`; it is open since `t` is a closed map. `mem_W'_iff`, `W'_le`, `cls_subset_W'` and
  `preimage_W'_le` show that `W' ⊆ U`, that it contains every orbit inside `U`, and that
  `s⁻¹ W' ⊆ t⁻¹ U`.
- `exists_norm` (section `S4`): for a finite projective `A`-algebra `B` there is a function
  `N : B → A` with `N b ∉ p` exactly when `b` lies in no prime of `B` over `p`. Here `N b`
  is the determinant of multiplication by `b`, extended to a free module through a
  splitting.
- `exists_basicOpen_of_finite`: prime avoidance; a finite subset `F` of an affine open `U`
  that lies in an open `V` lies in a basic open `D(f) ⊆ V` of `U`.
- `mem_basicOpen_iff_notMem`, `fromSpec_mem` and `primeIdealOf_fromSpec` (section `core`)
  translate between points of an affine open and primes of its sections.
- `exists_basicOpen_forall`: for `s` finite, flat and locally of finite presentation, an
  affine basic open `D = D(f)` with `s⁻¹D ⊆ t⁻¹U`, there is `g` on `D` whose basic open
  consists of the points `w ∈ D` with `t r ∈ D` for all `r` with `s r = w`. It takes `g`
  to be `N` (from `exists_norm`, for `Γ(X, D) → Γ(R, s⁻¹D)`) of the restriction of `t♯ f` to
  `s⁻¹D`.
- `main_finite`: if `s` and `t` are finite, flat and locally of finite presentation,
  `hequiv` holds, `S` is finite, `U` is an affine open and `t r ∈ U` whenever `s r ∈ S`,
  then some affine open `W ⊆ U` contains `S` and satisfies `s⁻¹ W = t⁻¹ W`. The union `C`
  of the orbits of `S` is finite (finite fibres of `s`) and lies in `W' s t U`. Prime
  avoidance gives `D(f) ⊆ W'` containing `C`, and `exists_basicOpen_forall` gives
  `W = D(g)`: the points of `D(f)` whose whole orbit lies in `D(f)`. This `W` is affine,
  and invariant because orbits partition `X`.
- `solution` restates `main_finite`.

This follows the proof of Stacks Lemma 39.24.1 (Tag 03JE): the orbit is finite, prime
avoidance gives a basic open, and a norm along the finite locally free `s` cuts out the
invariant part.

## Declarations

Names, namespaces and statements are the FLT ones. All declarations are in the FLT namespace
`P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation.Q1NBHDfin`, except `solution`, which is in `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`.

- def `cls`
- theorem `mem_cls_self`, `exists_inv`, `cls_symm`, `cls_trans`, `cls_eq_of_mem`
- def `W'`
- theorem `mem_W'_iff`, `W'_le`, `cls_subset_W'`, `preimage_W'_le`
- theorem `exists_norm`
- theorem `exists_basicOpen_of_finite`
- theorem `mem_basicOpen_iff_notMem`, `fromSpec_mem`, `primeIdealOf_fromSpec`,
  `exists_basicOpen_forall`
- theorem `main_finite`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation.solution`

## Dependencies

Imports only `Mathlib`.
