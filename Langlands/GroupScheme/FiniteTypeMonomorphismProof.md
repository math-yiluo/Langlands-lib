# Finite-type group-scheme monomorphisms are closed immersions

`Langlands.GroupScheme.finiteTypeMonomorphism.{u}` proves the unchanged
published proposition
`Langlands.GroupScheme.FiniteTypeMonomorphismStatement.{u}`.
For every field `k`, separated finite-type group schemes `G` and `H` over
`Spec k`, and group-scheme homomorphism `f : G ⟶ H`, monicity of the
underlying scheme morphism implies that this same morphism is a closed
immersion. Finite type is expressed by locally of finite type and
quasi-compact structure morphisms. Monicity is categorical monicity in
schemes, including tests by nonreduced schemes. The groups may be
nonaffine, nonreduced, nonsmooth and disconnected, and the field is arbitrary.

The source assertion is J. S. Milne, *Algebraic Groups* (2017), Theorem 5.34,
printed p.107 / PDF p.123, registered as
`milne-2017-algebraic-groups` (SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to this
theorem. The implemented proof is a derived argument using the Library's
schematic-dominance and dominant-homomorphism results; it does not follow
Milne's quotient proof or use the adjacent printed Theorem 5.36.

The module proves two auxiliary results in the namespace
`Langlands.GroupScheme.FiniteTypeMonomorphism`. Both assume an algebraically
closed field, a locally finite-type quasi-compact source, and a locally
finite-type separated target.

1. `isClosedImmersion_of_reduced` additionally assumes that the source scheme
   is reduced. Let `Z` be the topological closure of the image of `f`. The
   vanishing ideal of `Z` defines a reduced closed subscheme `O` of `H`,
   with inclusion `j`. Reducedness of the source gives a factorization
   `f = c ≫ j`. The closed embedding `j` identifies its range with `Z`,
   which proves that `c` is dominant. The reduced target makes `c`
   schematically dominant.

   `ImageGeneration.isSchemeTheoreticallyDominant_tensorHom` makes
   `c ⊗ c` schematically dominant. The factorization theorem
   `exists_over_factor_of_schematic_precomp` then restricts multiplication
   to `O`; the same theorem restricts inversion. The unit is obtained by
   composing the source's unit with `c`.
   `GroupObjectDescent.grpObjOfMono` transports the group axioms through
   `j`. Cancellation against the monomorphism `j` shows that `c` is a
   group homomorphism. These constructions impose no affineness assumption.

   `DominantHomFlat.flat_surjective` makes `c` flat and surjective.
   Monicity of `f` implies monicity of `c`, and
   `Flat.isIso_of_surjective_of_mono` makes `c` an isomorphism.
   Thus `f = c ≫ j` is a closed immersion.

2. `isClosedImmersion` removes reducedness of the source. Over the
   algebraically closed field, `reducedSubgroup G` is a reduced group
   scheme whose inclusion into `G` is a surjective closed immersion.
   The preceding result makes the composite of this inclusion with `f`
   a closed immersion. `UniversallyClosed.of_comp_surjective` therefore
   makes `f` universally closed. The map `f` is locally of finite type,
   and monicity makes it separated, so it is proper. Mathlib's
   `IsClosedImmersion.iff_isProper_and_mono` concludes.

For the exact arbitrary-field theorem, the proof base-changes to
`AlgebraicClosure k`. The required finite-type and separated hypotheses,
and monicity of `f`, persist under this base change, so the second auxiliary
result applies. `DominantHomFlat.baseChange_isPullback` identifies the
underlying square of schemes. The target projection is the base change of
the faithfully flat quasi-compact map `Spec (AlgebraicClosure k) ⟶ Spec k`.
Fpqc descent for universal closedness gives universal closedness of the
original `f`. Local finite type and monicity again make it proper, and the
same proper-monomorphism criterion gives the desired closed immersion.
