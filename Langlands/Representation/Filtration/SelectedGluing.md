# Objectwise selected parts of supplied gluings

This is internal algebraic infrastructure for the passage to unitary parts in
Renard 2026, VII.2.5 (printed p.230 / PDF p.236). It uses the compact-open
characteristic spaces of VII.1.1 (printed p.220 / PDF p.226) and generalizes the
zero/nonzero real-part selection of VII.2.3 (printed p.229 / PDF p.235).
It does not prove the represented geometric lemma, its tempered analogue, or
any comparison between the selected geometric pieces and induced unitary
Jacquet modules.

`selectedWeightEquiv` restricts an actual representation equivalence to the
sums selected by the same arbitrary character predicate. Both directions
preserve each generalized weight space, so the restricted map is bijective.
The forward map is literally the original equivalence on subtype vectors.
Spanning, smoothness and admissibility are not needed for this restriction;
the coefficient, acting-group, character-group and carrier universes remain
independent.

`IsGluedFrom.exists_objectFiltration` evaluates a supplied natural finite
gluing at one object. It reuses `RepFunctorFiltration.atObject`, retains the
original number of grades and permutation, and evaluates each supplied
natural isomorphism to obtain an equivalence of actual graded representations.
Repeated and zero grades are retained.

`IsGluedFrom.exists_selectedFiltration` assumes that this one ambient value
is admissible over an algebraically closed field. It takes the intersection
filtration furnished by `ObjectRepFiltration.selectedFiltration`. The
supporting algebraic argument in `selectedGradedEquivOfAdmissible` gives an
equivalence from each intersected quotient to the selected part of the
original quotient: admissibility supplies upper-step weight spanning and
ambient smoothness. Composing with `selectedWeightEquiv` for the evaluated
natural isomorphism identifies that quotient with the selected part of the
corresponding supplied piece. No admissibility of the pieces is assumed.
The same permutation and all grades are kept. The acting group has the
nonarchimedean topology and weak local compactness used by the generalized
weight-space construction. Admissibility and the initial gluing are explicit
premises; the full VII.2.5 proof must supply them and the geometric piece
comparisons separately.
