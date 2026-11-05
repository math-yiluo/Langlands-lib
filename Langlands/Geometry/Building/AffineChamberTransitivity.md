# Simple transitivity of the actual affine Weyl action on chambers

`Langlands.Geometry.Building.affineChamberSimpleTransitivity` proves the exact
published `AffineChamberSimpleTransitivityStatement.{uV, uA}`. Given any two
existing chambers `C` and `D` of `Ψ`, there is exactly one element of the
existing `AffineRootSystem.affineWeylGroup Ψ` whose actual affine direct image
of `C` equals `D`. The theorem adds no premise to the published statement.

The real vector space and its affine torsor have independent universes. The
root-system hypothesis remains `IsAffineRootSystemWithRankZero`, including
corrected AR4, nonreduced systems and rank zero. No origin, topology on the
torsor, reducedness or positive-rank assumption is introduced. The target and
its imported mathematics are unchanged.

## Implemented proof

`IsAffineRootSystemWithRankZero.isLocallyFiniteReflectionArrangement` supplies
the five fields of the published generic arrangement predicate. Spanning of
the derivative roots, nonzero linear parts, finiteness of the derivative
roots and existence of coroots are existing root-system fields. The remaining
field is `IsAffineRootSystemWithRankZero.finite_bounded_at`, the published
consequence of corrected AR4. Integrality and infinite derivative fibres
remain in the root-system hypothesis even though the generic arrangement
result does not need them.

`affineChamberSimpleTransitivity_of_gallery` packages the final deduction.
It first writes the two chamber subsets as `facet Ψ x` and `facet Ψ y`,
where `x` and `y` are their regular defining points. The geometry theorem
identifies `Subgroup.closure (wallReflections Ψ x)` with `affineWeylGroup Ψ`
and gives an element `w` of that subgroup for which `facetRel Ψ (w x) y`.
The equality of generated subgroups makes `w` an element of the existing
affine Weyl group. The published `image_facet` and `facet_eq_facet_iff`
then show that its actual affine image of `facet Ψ x` is `facet Ψ y`.
This is the existence part of the unique-existence conclusion.

For uniqueness, suppose `v` has the same image. The actual map `w⁻¹ * v`
preserves `facet Ψ x`: its image is the inverse image under `w` of the
common target chamber, and the affine equivalence cancels with its inverse.
`chamber_stabilizer_eq_one` from `AffineChamberFreeness` applies to this
same chamber and quotient. It uses the five separation laws already proved
for the actual image action, the wall-generation equality, and the generic
gallery-freeness proposition to conclude `w⁻¹ * v = 1` in the existing
affine Weyl subgroup. Group cancellation gives `v = w`.

The final theorem supplies the two published proofs:
`affineReflectionGalleryGeometry.{uV, uA}` and
`ReflectionGallery.reflectionGalleryFreeness.{max uV uA, uA}`. The larger group
universe is needed because actual affine automorphisms use both the vector
space and torsor carriers; bundled chamber subsets remain in universe `uA`.
Neither generic proposition remains a premise of the final theorem.
The argument also applies when the root set is empty, so rank zero requires
no extra case or nonemptiness assumption on roots. Only transport between
two given chambers is concluded; chamber existence and the other facet
assertions of KP Lemma 1.3.17 are outside this statement.

## Provenance and authorship

This is an internal assembly proof from published Library results. The
mathematical source of the target is Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Lemma 1.3.17, printed p.21/PDF p.52, with the rank-zero
and corrected-AR4 conventions explained in the unchanged
[statement documentation](AffineChamberTransitivityStatement.md).
The generic gallery proof, finite-word deletion proof and actual-action
adapter are imported by their Lean names; no external Lean implementation
is used. The Markdown above describes the implemented deduction rather
than claiming to reproduce the source's proof line by line.

Worker 455 authored the AR4 adapter and final assembly. Worker 1622 authored
the imported actual-action freeness adapter and the original generic
finite-word proof, and checked the assembly invocation. The geometry proof
is the separately published work of Worker 1221; the published generic
freeness contribution was prepared by Worker 1632 with Worker 1622.
