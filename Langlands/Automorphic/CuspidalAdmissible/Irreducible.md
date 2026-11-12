# Irreducible admissible subrepresentations by minimal fixed dimension

Provenance: internal. This module gives the representation-theoretic step that turns a
subrepresentation with finite-dimensional fixed vectors into an irreducible admissible one.
The argument is the standard minimal-dimension argument for representations of totally
disconnected groups (compare Bushnell–Henniart, *The local Langlands conjecture for GL(2)*,
§2–§4, and Bernstein–Zelevinsky, *Representations of the group GL(n,F)*, §2). Here it uses an
extra input: every nonzero subrepresentation has a nonzero `U`-fixed vector for one fixed
compact open subgroup `U`. For the finite action of an irreducible operator realization this
input is proved in the second part. The proof uses `U`-averages and the irreducibility of the
full realization (finite, compact and enveloping actions together).

## Abstract part (`CuspidalAdmissible`)

Let `ρ` be a complex representation of a group `G` on `V`.

- `generated ρ M`: the subrepresentation spanned by all translates `ρ g m` with `m ∈ M`, for
  a submodule `M`. `le_generated`: `M` lies in it. `generated_le`: it lies in every
  subrepresentation containing `M`.
- `finite_fixedVectors_toRepresentation`: if `A ≤ Y` and `Y ∩ V^K` is finite-dimensional,
  then the `K`-fixed vectors of the representation on `A` are finite-dimensional. The proof
  injects them into `Y ∩ V^K`.
- `isSmooth_toRepresentation`: a subrepresentation of a smooth representation is smooth.
- `exists_irreducible_admissible_le hρ V₀ hfin U hV₀ hkey`: let `ρ` be smooth and `V₀` a
  subrepresentation such that `V₀ ∩ V^K` is finite-dimensional for every open subgroup `K`.
  Let `U` be an open subgroup with `V₀ ∩ V^U ≠ 0`, and assume every nonzero
  subrepresentation `Z ≤ V₀` satisfies `Z ∩ V^U ≠ 0`. Then there is a subrepresentation
  `A ≤ V₀` that is nonzero, irreducible and admissible.

  Proof: choose `Y ≤ V₀` with `Y ∩ V^U ≠ 0` and with `dim (Y ∩ V^U)` minimal (`Nat.find`).
  Put `M := Y ∩ V^U` and `A := generated ρ M`. Then `A ≤ Y` and `A ≠ 0`. Let `C ≤ A` be a
  nonzero subrepresentation. By the hypothesis, `C ∩ V^U ≠ 0`. Also `C ∩ V^U ⊆ M`, and
  minimality gives `dim M ≤ dim (C ∩ V^U)`. Hence `C ∩ V^U = M`, so `A = generated ρ M ≤ C`.
  Irreducibility follows from `CountableDual.isIrreducible_of_forall`. Admissibility follows
  from `isSmooth_toRepresentation` and `finite_fixedVectors_toRepresentation` with `Y := V₀`.

## Operator realizations (`OperatorRealization`)

Let `S : OperatorRealization F n`, let `U` be an open subgroup of `GL_n(𝔸_f)` and let
`hU` say that `U` is compact. Write `avg` for the `U`-average
`Compact.averageMap S.finiteRepresentation S.finiteRepresentation_isSmooth U hU`.

- `commutingIntertwiner T hT`: an endomorphism `T` that commutes with every finite
  translation, viewed as a self-intertwiner of `S.finiteRepresentation`.
- `averageMap_commute_of_commute`: `avg (T f) = T (avg f)` for such `T`. This is
  `Compact.averageMap_commute`.
- `averageKernel U hU`: the submodule of the vectors `f` with `avg (S.finiteRepresentation d f) = 0`
  for every `d`. `mem_averageKernel` unfolds membership.
- `averageKernel_finite`, `averageKernel_compact` and `averageKernel_enveloping`: this
  submodule is stable under the finite, compact and enveloping actions. Finite translations
  move the index `d`. Compact and enveloping operators commute with finite translations
  (`finiteRepresentation_compactRepresentation`, `finiteRepresentation_envelopingAction`),
  hence with `avg`.
- `le_averageKernel`: let `Z` be a subrepresentation of the finite action with `Z ∩ V^U = 0`.
  Then `Z` lies in the average kernel. For `z ∈ Z`, the vector `avg (S.finiteRepresentation d z)`
  lies in `Z` (`CountableDual.averageMap_mem`) and is `U`-fixed
  (`Compact.averageMap_mem_fixedVectors`), so it is `0`.
- `inf_fixedVectors_ne_bot hS U hU hfix Z hZ`: let `S` be irreducible, let `U` be a compact
  open subgroup with `V^U ≠ 0`, and let `Z ≠ 0` be a subrepresentation of the finite action.
  Then `Z ∩ V^U ≠ 0`.

  Proof: suppose `Z ∩ V^U = 0`. Then the average kernel contains `Z` and is nonzero. It is
  stable under all three actions, so it is everything (`eq_top_of_generatorStable`). For a
  `U`-fixed `f`, taking `d = 1` gives `f = avg f = 0` (`Compact.averageMap_id`). This
  contradicts `V^U ≠ 0`.

The declarations `averageKernel_compact`, `averageKernel_enveloping` and
`inf_fixedVectors_ne_bot` use `set_option maxHeartbeats 1000000`. Their elaboration goes
through the generic `Submodule` instances of `S.Space`, which is costly.
