# Proof: quasi-split apartments over henselian integer-valued fields

Author: Worker 4783.

Lean module: `Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof`.

This module proves the Library statement
`Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceStatement` as the theorem
`quasiSplitIntegerApartmentExistence`. The statement concerns a field `k` with a surjective
valuation `v : k → ℤ ∪ {∞}` whose valuation ring is henselian, a quasi-split group `G` over
`k`, and a maximal split torus `i : S → G`. It asserts that there are a normalizer-stable
apartment class `D` of root-datum valuations of `i` for the integer order of `v` and a
centralizer datum `C` with which `D` is compatible (`IntegerValuation.IsOmegaCompatible`).

## Route

The proof follows Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §6.1(b)–(c).
The quasi-split apartment is obtained by Galois descent from the split apartment over a
finite Galois extension `K` splitting the centralizer `T` of `S`. Earlier units of this task
already did the following.

- `QuasiSplitApartmentAssembly` (`quasiSplitIntegerApartmentExistence_of_multipliableOpposite`)
  reduces the statement to `QuasiSplitMultipliableOppositeStatement`. This is axiom V 5 of the
  descended family at relative roots `a` with `2a` also a relative root (type R2). The
  assembly builds the split apartment of `(G_K, T_K)` for the henselian extension of `v`, a
  Galois-fixed point `x`, and the torus-then-field restriction `ψ` of `x`. It proves V 5 at
  all other relative roots (unit `QuasiSplitApartmentOpposite`) and normalizer stability.
- `QuasiSplitMultipliableOpposite` (`torusRestricted_opposite_of_pieceSymmetries`) proves V 5
  of the torus restriction at a multipliable character over `K`. It needs a family of
  value-preserving piece symmetries acting transitively on the roots over each multiple of
  `a`, and two roots over `a` whose sum is a root.

This module supplies those hypotheses from Galois theory and concludes.

## Declarations

- `isPieceSymmetry_galois`: for a Galois automorphism `τ` of `K/k`, the pair formed by
  `rationalConjugate k K G τ` on `G(K)` and the root-index permutation `galoisRootIndexEquiv`
  is a piece symmetry over `a_K` (`IsPieceSymmetry`).
  - Injectivity holds because both maps are bijections.
  - Additivity on roots holds because the Galois action on characters is linear
    (`galoisRootIndexEquiv_root`).
  - Restrictions to `n • a_K` are preserved because the action commutes with restriction to
    `S_K` and fixes base-changed characters (`galoisRepresentation_precompose`,
    `galoisRepresentation_baseChange`).
  - Root groups correspond by the published `rationalConjugate_mem_subgroup_iff`.
- `torusFieldRestrictedRootFunctionFamily_opposite_of_two_mem`: the conclusion of
  `QuasiSplitMultipliableOppositeStatement` under its hypotheses, stated with section notation.
  The proof proceeds as follows.
  1. The restrictions of roots of `T_K` lie on the multipliable line through `a_K`
     (`RestrictsToMultipliableLine`). Let a root restrict to `n • a_K`. Then `n ≠ 0`, because
     no root restricts to zero (`root_restrict_ne_zero_of_torusCentralizer`). So `n • a` is a
     relative root (`mem_roots_comp_iff`, `mem_roots_baseChange_iff`), and
     `HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem`, applied to `a` or `-a`, gives
     `n ∈ {±1, ±2}`.
  2. The published `MultipliableRootNoncommutation.exists_partner` supplies two roots over
     `a_K` whose sum is a root. It uses that `t` is a largest split subtorus of the closed
     centralizer torus and that the root datum is reduced.
  3. The value preservation `x_{τ χ}(τ w) = x_χ(w)` follows from the Galois invariance of `x`
     and `RootFunctionFamily.galoisAction_apply_conjugate`.
  4. Transitivity: the roots of `T_K` over `a_K (n • a)` form one Galois orbit, by the
     published `rootOrbit_eq_restrictionFiber_of_torusCentralizer`.
  5. The scalar extensions of `g, g', g''` lie in the restricted root groups of `±a_K` over
     `K`. `g` stays nontrivial, because scalar extension of rational points is injective.
     `g' g g''` normalizes `j_K` and `groupHom t_K ≫ j_K`: normalizer points of `i` normalize
     `jT` (`mem_normalizerPoints_of_torusCentralizer`), and `normalizerPointsFieldExtend`
     extends them to `K`. Scalar extensions are fixed by every `rationalConjugate`.
  6. `torusRestricted_opposite_of_pieceSymmetries` then gives
     `ψ_{-a_K}(g'_K) + ψ_{a_K}(g_K) = 0`. This is the claim after unfolding the field
     restriction.
- `quasiSplitMultipliableOpposite : QuasiSplitMultipliableOppositeStatement`: introduces the
  hypotheses of the statement and applies the previous theorem.
- `quasiSplitIntegerApartmentExistence : QuasiSplitIntegerApartmentExistenceStatement`: the
  target, `quasiSplitIntegerApartmentExistence_of_multipliableOpposite` applied to
  `quasiSplitMultipliableOpposite`.

The private lemma `rationalExtend_injective'` (injectivity of scalar extension on rational
points of an affine group) repeats the proof of the private lemma of the same purpose in
`QuasiSplitApartmentOpposite`.

## Provenance

Kaletha–Prasad, Proposition 6.1.19 (printed pp. 206–207, PDF pp. 237–238), Construction
6.1.21 (printed pp. 207–208, PDF pp. 238–239), Lemma 6.1.26 (printed p. 209, PDF p. 240) and
Lemma 6.1.28 (printed p. 210, PDF p. 241). The Lean proof uses the internal route described
in the units of task 8ffe0456; at multipliable roots it uses the piece-symmetry argument
instead of the explicit `SU₃` computation of Kaletha–Prasad. The only axioms used are
`propext`, `Classical.choice` and `Quot.sound`.
