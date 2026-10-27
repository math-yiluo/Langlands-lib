# Surjectivity of the canonical finite smooth-dual tensor map: proof

Worker 261 wrote the Lean proof and this account of it.

## Result

`Langlands.FiniteTensor.smoothDualTensorSurjectivity` proves the entire
published proposition
`Langlands.FiniteTensor.SmoothDualTensorSurjectivityStatement` from
[SmoothDualSurjectivityStatement](SmoothDualSurjectivityStatement.md). Its
type is `SmoothDualTensorSurjectivityStatement.{uI, uG, uV}`, so the three
universe levels of the index type, the groups and the carriers stay
independent. The proof introduces every binder of the proposition and applies
the module's theorem `smoothDualTensorMap_surjective`.

So for every finite index type `ι` (the empty type included), every family of
topological groups `G i`, and every family of admissible complex
representations `ρ i` on complex vector spaces `V i`, assume that each open
subgroup of each `G i` contains a compact open subgroup. Then every smooth
functional on the external tensor product is the image under the published
`smoothDualTensorMap ρ` of some element of `⨂[ℂ] i, SmoothDual (ρ i)`. The
preimage built in the proof is in general a sum of pure tensors.

The proof adds no hypothesis to the statement. It uses no topology on the
carriers, global finite-dimensionality, local compactness of the whole groups,
countability or separation axiom. Empty `ι` and zero carriers need no separate
case: the argument below is uniform in `ι` and the carriers. The statement
pair and every imported pair are unchanged. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Imports and reused results

The module imports the statement module,
`Langlands.Representation.Tensor.FiniteProperties` and
`Langlands.Representation.Smooth.Contragredient.CompactDualityProof`. It uses
these published results by name:

- `smoothDualTensorMap_val`: the underlying functional of
  `smoothDualTensorMap ρ x` is
  `PiTensorProduct.dualDistrib (PiTensorProduct.map (fun i => smoothDualPairing (ρ i)) x)`.
- `smoothDualTensorMap_action`: the map intertwines the external tensor of the
  factor smooth contragredients with the smooth contragredient of
  `external ρ`.
- `fixedVectors_external_le`: for subgroups `K i`, the vectors of
  `⨂[ℂ] i, V i` fixed by `Subgroup.pi Set.univ K` lie in the range of
  `PiTensorProduct.map (fun i => (fixedVectors (ρ i) (K i)).subtype)`.
- `isSmooth_external`: the external tensor of smooth factors is smooth.
- `smoothDualFixedRestriction_bijective`: for a smooth representation and a
  compact open subgroup `K`, restricting `K`-fixed smooth functionals to the
  `K`-fixed vectors is a bijection onto the full dual of the fixed space.
- Mathlib's `PiTensorProduct.dualDistribEquiv`, the linear equivalence
  `(⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i)` for a finite index and
  finite free modules `M i`. Here it is used only on the finite-dimensional
  factor fixed spaces, never on the ambient carriers.

## Implemented proof

The module has two theorems and the closing theorem. No new definition is
introduced.

1. `exists_isCompact_pi_le` assumes only factorwise compact-open cofinality.
   Then every open subgroup `U` of `∀ i, G i` contains
   `Subgroup.pi Set.univ (fun i => L i)` for some compact open subgroups
   `L i`. For each `i`, the preimage of `U` under the continuous coordinate
   inclusion `MonoidHom.mulSingle G i` is an open subgroup of `G i`.
   Cofinality chooses a compact open `L i` inside it. An element of the
   product of the `L i` has every coordinate inclusion in `U`, so it lies in
   `U` by Mathlib's `Subgroup.pi_mem_of_mulSingle_mem`.

2. `smoothDualTensorMap_surjective` proves surjectivity. A `Fintype`
   structure is chosen from `Finite ι`. Let `ℓ` be a smooth functional on
   `⨂[ℂ] i, V i`.

   - **Compact open product subgroup.** Smoothness of `ℓ` gives an open
     subgroup `U` of `∀ i, G i` fixing it. Step 1 gives compact open `L i`
     whose product lies in `U`. The proof forms that product as an
     `OpenSubgroup` `P` in a local `let`. `P` is open by `isOpen_set_pi`
     because `ι` is finite, and compact by `isCompact_univ_pi`, both for the
     actual product topology. Then `ℓ` is `P`-fixed for the smooth
     contragredient of `external ρ`.
   - **Finite-dimensional factor pieces.** Let `F i` be
     `fixedVectors (ρ i) (L i)`. By the project definition of admissibility,
     which requires finite generation of the fixed vectors of every open
     subgroup, each `F i` is a finite-dimensional complex vector space. Let
     `incl : (⨂[ℂ] i, F i) →ₗ[ℂ] ⨂[ℂ] i, V i` be the tensor of the inclusions.
     Set `y` to be the inverse of `PiTensorProduct.dualDistribEquiv` applied
     to `ℓ ∘ incl`. Then `y : ⨂[ℂ] i, Module.Dual ℂ (F i)` and
     `dualDistrib y = ℓ ∘ incl`.
   - **Lifting factor functionals.** For each `i`,
     `smoothDualFixedRestriction_bijective` (with smoothness from
     admissibility and compactness of `L i`) makes the restriction from
     `L i`-fixed smooth functionals to `Module.Dual ℂ (F i)` a linear
     equivalence `e i`. The linear map `lift i` sends `f` to the element of
     `SmoothDual (ρ i)` underlying `(e i).symm f`. Each `lift i f` is `L i`-fixed and
     agrees with `f` on `F i`.
   - **The preimage.** The candidate is `PiTensorProduct.map lift y`. An
     auxiliary identity `key` holds for all `z` and `w` and is proved by
     induction on both tensors. The dualDistrib of the pairing image of
     `PiTensorProduct.map lift z`, evaluated at `incl w`, equals
     `dualDistrib z w`. On pure tensors both sides are the product of the
     factor evaluations, by `dualDistrib_apply` and the agreement of
     `lift i f` with `f` on `F i`. Both sides are additive in `z` and `w`.
   - **The candidate is `P`-fixed.** For `k ∈ P`,
     `smoothDualTensorMap_action` moves the action inside the map. The action
     of `k` on `PiTensorProduct.map lift y` is the tensor of the factor
     actions composed with `lift`. By `PiTensorProduct.map_comp` it is
     `PiTensorProduct.map` of the composites, and these equal `lift i`
     because each lift is `L i`-fixed.
   - **Equality.** Both `smoothDualTensorMap ρ (PiTensorProduct.map lift y)`
     and `ℓ` are `P`-fixed smooth functionals for `external ρ`. Their
     restrictions to the `P`-fixed vectors agree. By `fixedVectors_external_le`,
     each such vector is `incl w` for some `w`. By `smoothDualTensorMap_val`
     and `key`, the first functional takes the value `dualDistrib y w` there,
     which equals `ℓ (incl w)`. The external representation is smooth by
     `isSmooth_external`, and `P` is compact open. Then
     `smoothDualFixedRestriction_bijective` for `external ρ` at `P` makes
     restriction injective. So the two functionals are equal.

3. `smoothDualTensorSurjectivity` introduces the binders of the statement and
   applies `smoothDualTensorMap_surjective`.

## Provenance

The target is an internal derived proposition, as its statement Markdown
explains, rather than a verbatim theorem from external literature. The
implemented route follows the prospective route sketched in that Markdown:
take a compact open product subgroup, decompose the dual of the
finite-dimensional product fixed space by finite tensor duality, and lift the
factor functionals.
