# Standard modules embedded in isotypic place actions are irreducible

Module `Langlands.Automorphic.ComplexPlaceStandardIrreducible`, namespace
`Langlands.Automorphic.PlaceIsotypic`. It is a step in the
proof of `ComplexPlaceParameterIrreducibleStatement`. Provenance: internal.

Setting. `V` is a complex vector space with:
- a representation `κ` of `U(n) = Matrix.unitaryGroup (Fin n) ℂ`;
- a Lie action `π` of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`.

Two hypotheses are used:
- `hW₀`: `V` has an irreducible stable subspace `W₀` (`PlaceComponent.IsIrreducible κ π W₀`);
- `hcomm`: every subspace stable under `κ`, `π` and every linear map commuting with them is
  `⊥` or `⊤`.

`X(ds)` is the `U(n)`-finite complex standard module of a list `ds` of `n` complex characters,
with `complexStandardRep n ds` and `complexStandardLie n ds`. `A : X(ds) → V` is an injective
linear map with `IsComplexStandardIntertwining n κ π ds A`.

## Results

- `isAtom_range_of_embedding`: under `hW₀` and `hcomm`, the image of `A`, as an
  `opAlg κ π`-submodule (`toOpSubmodule`), is an atom, that is, a simple module.
  - By `isSemisimple_isotypic_of_commutant`, `V` is semisimple and isotypic of the type of
    `W₀`. Hence so is the image `M` of `A` (Mathlib's submodule instance and
    `IsIsotypicOfType.of_injective`).
  - `A` induces a linear isomorphism `e : X(ds) ≃ M`. It carries `complexStandardRep n ds k` to
    the action of `κ k ∈ opAlg κ π` (`IsComplexStandardIntertwining.map_rep`).
  - `exists_isScalarVector` gives a scalar vector `f₀` of `X(ds)`. Every `opAlg κ π`-linear
    endomorphism `E` of `M` gives the `U(n)`-equivariant endomorphism `e⁻¹ ∘ E ∘ e` of
    `X(ds)`, which scales `f₀`. So `E` scales `e f₀ ≠ 0`.
  - `isSimpleModule_of_scalar` concludes.
- `isIrreducibleGKModule_of_embedding`: under the same hypotheses, `IsIrreducibleGKModule
  (complexStandardRep n ds) (complexStandardLie n ds)`.
  - Nontriviality is the Library's `complexStandardNontrivial`.
  - Let `W ⊆ X(ds)` be stable under `complexStandardRep` and `complexStandardLie`. Its image
    `A(W)` is stable under `κ` and `π` (`map_rep`, `map_lie`) and lies in the image of `A`.
  - Since that image is an atom, `A(W)` is `⊥` or the whole image. Injectivity of `A` gives
    `W = ⊥` or `W = ⊤`.

All results use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal. The argument is the multiplicity-one route to the irreducibility of archimedean
standard-module components of cuspidal realizations
(`CuspidalArchimedeanStandardIrreducibleStatement`). The
module is stated for an abstract `V`, so that it does not depend on the operator realizations
of the Library.
