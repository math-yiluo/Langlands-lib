# Alternating extension of ordered unit cocycles

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.AltCocycle`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`). Everything is proved in the file, with no
hypotheses beyond those in the signatures. Internal construction; no literature statement
is formalized.

For a scheme `X`, a linearly ordered index type `ι` and opens `T : ι → X.Opens`:

- `resU h : (Γ(X, V))ˣ →* (Γ(X, W))ˣ`, restriction of units along `h : W ≤ V`; `resU_val`,
  `resU_resU` (composition).
- `altExt H i j` for a family `H i j` of units on `T i ⊓ T j`: `H i j` if `i < j`, `1` if
  `i = j`, and the restriction to `T i ⊓ T j` of `(H j i)⁻¹` if `j < i`
  (`altExt_of_lt`, `altExt_self`, `altExt_of_gt`).
- `resU_altExt_swap`: on any open `W ≤ T i ⊓ T j`, the restriction of `altExt H j i` is the
  inverse of that of `altExt H i j`.
- `isCocycle_altExt`: if `H` satisfies the cocycle identity
  `H i j · H j k = H i k` (restricted to `T i ⊓ T j ⊓ T k`) for all `i < j < k`, then
  `altExt H` satisfies it for all `i, j, k`, i.e. `CocycleGluing.IsCocycle (altExt H)`
  (Library `CocycleLineBundleProof`). Proof: for fixed `a, b, c`, the restrictions to
  `T a ⊓ T b ⊓ T c` of the values of `altExt H` on the three-element index set
  `{a, b, c}` form an alternating family in the abelian group of units, and the Library
  lemma `CechResolution.add_eq_of_strict` extends the identity from strictly increasing
  triples to all triples.
