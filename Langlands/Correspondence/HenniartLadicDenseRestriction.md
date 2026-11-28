# Restriction of continuous ℓ-adic representations along a map with dense image

Module `Langlands.Correspondence.HenniartLadicDenseRestriction`, namespace
`Langlands.Henniart.LocalNumerical`. Here `E = PadicAlgCl ℓ` for a prime `ℓ`, `G` is a group
with a topology, `H` is a group and `φ : H →* G` is a homomorphism with dense image. For
representations `A`, `B` in `FiniteRepresentation.{0, uG, uW} E G` that satisfy the Library's
`IsLadicContinuous` (module `Langlands.Correspondence.HenniartLadicClasses`), restriction along
`φ` preserves and reflects intertwiners, isomorphism, irreducibility and
`IsLadicDefinedOverFiniteExtension`. These are derived comparisons by density and are not taken
from a source. Henniart (1988), §4.1, pp. 509–510, takes a local field `K` of characteristic
`p`, fixes a prime `ℓ` distinct from `p` and calls an ℓ-adic representation of the absolute
Galois group `G_K` a continuous homomorphism
`G_K → GL(V)`, with `V` finite-dimensional over `ℚ̄_ℓ` and `GL(V)` carrying the ℓ-adic
topology, that is defined over a finite extension of `ℚ_ℓ` in `ℚ̄_ℓ`. The predicates
`IsLadicContinuous` and `IsLadicDefinedOverFiniteExtension` express the two conditions; the
results here hold for every prime `ℓ`.

## Declarations

- `isClosed_intermediateField_of_finiteDimensional ℓ L`: a finite-dimensional intermediate
  field `L` of `PadicAlgCl ℓ / ℚ_ℓ` is closed in `PadicAlgCl ℓ`. Mathlib's
  `PadicAlgCl.normedAlgebra` makes `PadicAlgCl ℓ` a normed `ℚ_ℓ`-space, and `L`, as a
  `ℚ_ℓ`-subspace, is finite-dimensional over the complete field `ℚ_ℓ`. It is therefore closed
  (`Submodule.closed_of_finiteDimensional`, applied to `Subalgebra.toSubmodule L.toSubalgebra`).
  `PadicAlgCl ℓ` itself is not complete. Closedness comes from the completeness of `ℚ_ℓ`.
- `isLadicDefinedOverFiniteExtension_restrict_iff ℓ φ hφ hA`: for `A` satisfying
  `IsLadicContinuous ℓ A`, `IsLadicDefinedOverFiniteExtension ℓ A` holds if and only if
  `IsLadicDefinedOverFiniteExtension ℓ (restrict φ A)` holds. Restriction keeps the carrier, so
  both conditions are about bases of the same space, indexed by the same `Fin` type. Forward:
  the same field `L` and basis `b` work, since the entries of `(restrict φ A).representation h`
  are those of `A.representation (φ h)`. Backward: the same `L` and `b` work.
  `Langlands.Representation.repr_mem_of_denseRange` (module
  `Langlands.Weil.Representation.DenseRestriction`) extends the condition "the `(i, j)` entry
  lies in `L`" from the image of `φ` to all of `G`, because `L` is closed by the previous
  lemma.
- `ladicRestriction_of_denseRange ℓ φ hφ A B hA hB`: for `A` and `B` satisfying
  `IsLadicContinuous`, the conjunction of four equivalences:
  1. a linear map `f : A →ₗ[E] B` intertwines the actions of `G` if and only if it intertwines
     them at every `φ h` (`Langlands.Representation.intertwines_iff_of_denseRange`);
  2. `IsIsomorphic A B` if and only if `IsIsomorphic (restrict φ A) (restrict φ B)`
     (`Langlands.FiniteRepresentation.isIsomorphic_restrict_iff_of_denseRange`);
  3. `A.representation` is irreducible if and only if `(restrict φ A).representation` is
     (`Langlands.FiniteRepresentation.isIrreducible_restrict_iff_of_denseRange`);
  4. the previous lemma.

  `IsLadicContinuous ℓ A` is continuity of `A.representation` for the module topology on
  `Module.End E A`. The proof gives `Module.End E A` and `Module.End E B` this topology with
  the instance `IsModuleTopology`, then applies the results of
  `Langlands.Weil.Representation.DenseRestriction`. `PadicAlgCl ℓ` is a normed field, hence a
  Hausdorff topological ring, as those results need.

## Use

`Langlands.Correspondence.Laumon.LocalWeilRestrictionProof` applies
`ladicRestriction_of_denseRange` to the projection `localProjection` of the Library's local
Weil group of `LaurentSeries k` to the absolute Galois group, whose image is dense
(`Langlands.Weil.Local.SepClosed.localProjection_denseRange`).

## Source

Henniart, *La conjecture de Langlands locale numérique pour GL(n)*, 1988 (`henniart-1988-numerical`),
§4.1, printed pp. 509–510.
