# Integral `SL₂`-data for the simple roots (`SimpleRootData`)

Author: Worker 239.

This module defines the structure `SimpleRootData P b` for a root datum `P : RootDatum J X Y`
with base `b`. It is the interface between two steps of the construction:

- the construction of an integral representation with `SL₂`-actions for the simple roots,
  which produces a `SimpleRootData` (module `ChevalleyLieExistence`);
- the construction of root operators for all roots, which consumes one
  (`nonempty_chevalleyLieData_of_simpleRootData` in `ChevalleyLieConstruction`).

The fields are:

- `ℓ : X →+ ℤ`, positive on the simple roots;
- a weight basis `wt : Fin n → X` whose weights generate `X` as an additive group
  (`closure_range_wt`);
- for each simple root `i`, integral divided powers `E i k` and `F i k` (standing for
  `e_i^k / k!` and `f_i^k / k!`). They satisfy `E i 0 = 1`,
  `E i a · E i c = C(a+c, a) • E i (a+c)` and `E i k = 0` for `k > n`, and `E i k` moves
  weight `μ` to `μ + k • α_i`. The same holds for `F i` with `−α_i`. Both `E i 1` and `F i 1`
  are nonzero modulo every prime;
- for each simple root `i` and every commutative ring `R` in the universe `u`, a group
  homomorphism `φ i R : SL₂(R) →* GL_n(R)`, natural in `R`. It sends the upper and lower
  unipotent matrices to the truncated exponentials `divExp (E i)` and `divExp (F i)`, and
  `diag(t, t⁻¹)` to the diagonal matrix with entries `t^⟨wt c, α_i^∨⟩`. The Weyl element
  `φ i R sl2Weyl` moves weight `μ` to `s_i μ` (`weyl_weight`);
- `E_F_same`: `E i 1 · F i 1 − F i 1 · E i 1` is the diagonal matrix of the pairings
  `⟨wt c, α_i^∨⟩`;
- `E_F_comm`: `E i 1` and `F i' 1` commute for distinct simple roots `i ≠ i'`.

The names `sl2Upper`, `sl2Lower`, `sl2Diag`, `sl2Weyl` and `divExp` come from `ChevalleyData`
and `RootExp` (Worker 1398). The module contains only this definition and states no theorem.

## Provenance

The structure is internal packaging. Mathematically, it records an integral representation of
the Chevalley–Serre generators `e_i`, `f_i`, `h_i` of the simple roots,
integrated to `SL₂` for each simple root, with the relations `[e_i, f_i] = h_i` and
`[e_i, f_j] = 0` for `i ≠ j` (Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §18.1; Steinberg, *Lectures on Chevalley groups*, §§1–2). The Serre relations are not
required.
