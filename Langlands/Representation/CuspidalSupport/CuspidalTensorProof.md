# Proof that external tensors of supercuspidal factors are irreducible and Levi cuspidal

Author: Worker 218.

`Langlands.CuspidalSupport.glCuspidalTensor` proves the published proposition
`Langlands.CuspidalSupport.GLCuspidalTensorStatement` in
`Langlands.Representation.CuspidalSupport.CuspidalTensorStatement`. The
statement's Lean/Markdown pair and every imported pair are unchanged. The
theorem's type is exactly `GLCuspidalTensorStatement.{uV, uF}`, with the
carrier universe `uV` and the field universe `uF` kept independent. The proof
adds no hypotheses and assumes no finite-dimensionality. It uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

The general tensor results come from the new module
`Langlands.Representation.Tensor.FiniteProperties`; see its Markdown for those
proofs. This module adds two small lemmas and the closing argument.

## Auxiliary lemmas

- `conjugateUnipotent_one`: the conjugate unipotent subgroup
  `B.conjugateUnipotent 1`, which is the image of `B.unipotentSubgroup F`
  under conjugation by the identity, equals `B.unipotentSubgroup F`. The proof
  is extensionality and `simp`.
- `exists_parabolic_ne_top`: suppose the refined parabolic
  `refinedParabolic F B S = Subgroup.pi Set.univ (fun i => (S i).parabolic F)`
  is not the whole Levi. Then some block refinement `S i` has
  `(S i).parabolic F ≠ ⊤`. Otherwise every factor is `⊤`, and Mathlib's
  `Subgroup.pi_top` makes the product `⊤`.

## Closing argument

Fix the prime, the p-adic field `F`, its topological data `T` (whose topology
is installed as the local instance), `n > 0`, a block shape `B`, and actual
supercuspidal objects `A i` on the blocks. By definition of
`supercuspidalProperty`, each `(A i).obj` is irreducible, and its
representation satisfies `IsSupercuspidal`, namely admissibility together with
the vanishing of the coinvariants for every conjugate of every proper
standard unipotent radical. The external smooth object
`FiniteTensor.externalSmoothObject (fun i => (A i).obj)` has the actual
external tensor representation `FiniteTensor.external` of the factor
representations. The three required properties are proved as follows.

1. **Irreducibility.** The Library's
   `Langlands.admissibleSchur_scalarEndomorphism` applies to each admissible
   irreducible factor and shows that every self-intertwiner is a scalar.
   `FiniteTensor.isIrreducible_external` then gives irreducibility of the
   external tensor product.
2. **Admissibility**, the first half of `IsLeviCuspidal`, is
   `FiniteTensor.isAdmissible_external` applied to the admissibility of each
   factor.
3. **Quasicuspidality**, the second half of `IsLeviCuspidal`. Let `S` be a
   block refinement with `refinedParabolic F B S ≠ ⊤`. By
   `exists_parabolic_ne_top`, some block `j` has
   `(S j).parabolic F ≠ ⊤`. Apply the supercuspidal vanishing condition of
   `A j` to the shape `S j` and the conjugating element `1`. With
   `conjugateUnipotent_one`, it shows that the coinvariants of factor `j` for
   `(S j).unipotentSubgroup F` vanish. Since
   `refinedUnipotent F B S = Subgroup.pi Set.univ
   (fun i => (S i).unipotentSubgroup F)`,
   `FiniteTensor.coinvariants_external_subsingleton` shows that the
   coinvariants of the external tensor product for `refinedUnipotent F B S`
   vanish.

Only the conjugating element `1` of the supercuspidal condition is used,
since the refined unipotent subgroups are the standard ones.
