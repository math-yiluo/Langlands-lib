# Geometric reductions for the fibrewise central-isogeny criterion

Worker 625.

This internal proof module supplies the forward implication and the flatness
and local quasi-finiteness steps toward
`ReductiveFibrewiseCentralIsogenyStatement`. It does not prove the whole
statement: centrality and finiteness of the full kernel over an arbitrary base
remain separate obligations.

The provenance is the first geometric step of Conrad, *Reductive group
schemes* (2014), Proposition 3.3.10, p.103, registered as
`conrad-2014-reductive-group-schemes`. The implementation uses the existing
Library results described below; its field argument passes through the
published finite-kernel theorem.

All declarations are in
`Langlands.GroupScheme.FibrewiseCentralIsogenyReduction`, in every universe `u`.

- `finite_central_kernel_fibres_of_isCentralIsogeny` applies arbitrary
  base-change stability of central isogenies. The pulled-back actual kernel is
  finite over the residue field, and its inclusion is central on all test
  schemes. No reductivity or surjectivity hypothesis is needed for this direction.
- `isogeny_of_surjective_of_finite_kernel` concerns a homomorphism over any
  field from a smooth connected affine group to a smooth affine group. The
  actual finite kernel gives finiteness of the homomorphism by
  `isFinite_hom_of_finite_kernel`. Its surjectivity gives dominance, and
  `DominantHomFlat.flat_of_isDominant` gives flatness, since the target is
  reduced and locally noetherian. These are the three conditions in `IsIsogeny`.
- `isFibrewiseIsogeny_of_finite_kernel_fibres` applies that field result to
  each actual residue-field fibre of a surjective homomorphism of reductive
  group schemes. Reductivity supplies connected reductivity of those fibres.
  Surjectivity is preserved by the actual pullback square.
- `fibreIsogeniesOfFiniteKernels` constructs a dependent family of bundled
  isogenies on the actual residue-field fibres. Its value at a point is the
  actual base-changed homomorphism, together with the isogeny proof supplied by
  the preceding theorem. This definition records those maps and proofs for
  consumers that require a bundled family.
- `flat_and_locallyQuasiFinite_of_finite_kernel_fibres` applies the published
  fibrewise-isogeny reductions to obtain flatness and local quasi-finiteness
  over the arbitrary base.
- `isogeny_iff_finite_kernel` applies the published finite-kernel reduction
  for smooth affine groups. With the same finite residue-fibre kernel and
  surjectivity hypotheses, global finiteness of the actual kernel is the
  remaining condition for `IsIsogeny`.

The last three declarations require no centrality hypothesis on the fibre
kernels. They do not conclude global finiteness from finiteness on fibres,
and they do not assert that centrality can be checked on residue-field
fibres over a nonreduced base.
