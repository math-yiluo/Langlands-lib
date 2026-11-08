# A Frobenius map detecting a nonzero Gelfand–Graev vector

Internal module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`.

## The Jacquet-module input

The hypothesis `GelfandGraevJacquetStatement` is defined in `JacquetStatement`. It is the
equivalence of the normalized Jacquet module of the Gelfand–Graev representation along a block
parabolic with the Gelfand–Graev representation of the Levi. Its proof is a separate unit of
this task.

## Cyclic subrepresentations

- `orbitSpan_eq_top_of_generator_mem`: a subrepresentation of a cyclic representation that
  contains the generator is everything.
- `cyclicMap_surjective`: the induced map `Cyclic.map` of cyclic subrepresentations is surjective.

## Main theorem

`exists_frobenius_ne_zero F hJ ψ n` assumes `GelfandGraevJacquetStatement` and takes a nonzero
`h ∈ GelfandGraevFunctions ψ n`. It produces:
- a block shape `B`;
- supercuspidal representations `A i` of `GL_(B.size i)(F)` with carriers in an arbitrary
  universe;
- an intertwiner `Tf` from `gelfandGraev ψ n` to
  `F.canonicalTopologicalData.normalizedProductInduced B (A i)`;

such that `Tf h ≠ 0`.

Proof:
1. The cyclic span of `h` is a nonzero smooth representation. The Library's
   `minimalNonzeroJacquet` gives a block shape `B` for which its normalized Jacquet module `J`
   is nonzero and quasicuspidal.
2. Take `x ≠ 0` in `J`. Its image `x̄` in the Jacquet module of the whole Gelfand–Graev
   representation is nonzero. The Jacquet map of the inclusion is injective, by
   `coinvariants_map_injective_of_smooth` and `Parabolic.unipotentFiniteContainment`. The cyclic
   span of `x̄` is quasicuspidal, as a quotient of the cyclic span of `x` inside `J`
   (`isLeviQuasicuspidal_subrepresentation`, `isLeviQuasicuspidal_of_surjective`).
3. The equivalence `e` from the hypothesis transports `x̄` to the Levi Gelfand–Graev
   representation. `leviGelfandGraev_cuspidalDetection` then gives `Φ` to a tensor product of
   supercuspidals with `Φ(e x̄) ≠ 0`.
4. `Parabolic.FirstAdjointness.frobenius` turns `Φ ∘ e` into `Tf`, and its value
   `Tf(v)(g) = (Φ ∘ e)([g·v])` is recorded by `frobenius_eval`. If `Tf h = 0`, then
   `(Φ ∘ e)([g·h]) = 0` for all `g`. By linearity, `(Φ ∘ e)` then vanishes on the classes of
   the whole cyclic span of `h`, in particular at `x̄`. This contradicts step 3.
