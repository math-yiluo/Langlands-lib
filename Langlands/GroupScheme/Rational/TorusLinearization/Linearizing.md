# Linearizing coordinates for a point action in prime characteristic

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only.

- `PointAction.exists_linearizing`: let `a : PointAction k K I n` be a point action (module
  `PointAction`) over a field `k` of prime characteristic `p`, with `I` finite. Its points over
  `K`-algebras `C` are surjectively parametrized by tuples `I → Cˣ`. Then there are
  polynomials `Φ_1, …, Φ_n` and `Q_1, …, Q_n` over `k` such that:
  - every `Φ_i` is additive;
  - `Φ(Q_j) = X_j` and `Q(Φ_i) = X_i`, so `Φ` and `Q` are mutually inverse coordinate changes;
  - for every `k`-algebra `B` and every point `t` over `B`, the pullback of each `Φ_i` along
    `t` is a `B`-linear combination `∑_j b_ij Φ_j` of the base changes of the `Φ_j`.

  The conclusion has exactly the shape of the hypothesis `hcore` of
  `torusVectorActionLinearization_of_linearizing` (module `TorusVectorLinearization/Assembly`).

  The proof chooses a `Fintype` structure on `I` and decidable equality classically. It takes
  the subspace `W` from `exists_subspace` (module `Generation`): `W` lies in `addSpan`, is
  stable, has injective linear-part map, and its Frobenius span contains the variables.
  `exists_linearizing_of_subspace` (module `Coordinates`) then turns `W` into the
  coordinates `Φ`, `Q`.
