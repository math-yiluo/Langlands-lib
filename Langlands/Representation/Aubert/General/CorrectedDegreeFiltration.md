# Corrected support filtration on homogeneous Jacquet degrees

Worker 691 derived this internal construction from the published
`General.CorrectedFiltration`, the actual Jacquet diagram, the generic
`CutComplex.Diagram.Subdiagram` quotient construction, and
`Langlands.FiniteFiltered`. Its namespace is
`Langlands.Aubert.General.JacquetComplex`.

The setup retains independent index, group and carrier universes, a finite
linearly ordered root type, actual subgroup families `P M U`, their semidirect
decompositions, closed radicals, unimodular modulus data, monotonicity of `P`
and antitonicity of `U`. The input `A` is any smooth complex representation at
the displayed carrier universe. A subgroup `T` has a finite Weyl quotient and
a supplied Coxeter system `cs` on the same root type. The source index `I` is
arbitrary. The root type may be empty.

## Actual support steps and grades

`stepSubdiagram ... i` has coordinate `s` equal to the underlying submodule
of `CorrectedFiltration.step ... I s i`. Thus its ambient object is the actual
normalized Jacquet module of the term indexed by the complement `univ \ s`.
Its map preservation is precisely `CorrectedFiltration.transition_mem_step`.
The actual transition maps and complement convention are preserved.

`degreeFiltration ... k i` requires every coordinate of the homogeneous family
of degree `k` to belong to this step. `degreeFiltration_monotone` follows
coordinatewise from `step_monotone`. `degreeFiltration_zero` uses `step_zero`
in each coordinate. `degreeFiltration_length` uses `step_length` and explicitly
requires `IsBruhatCover T (P ∅) (P I)` for exhaustiveness. This module does not
construct that covering hypothesis.

`degreeDifferential_preserves_degreeFiltration` specializes the generic
subdiagram preservation theorem. In particular it applies to the original
exterior insertion signs.

`gradedDiagram ... i` is the actual adjacent coordinate quotient: its numerator
is support step `i+1`, and its denominator is step `i` pulled back to that
numerator. `gradedEquiv` identifies the actual adjacent quotient of each
homogeneous degree filtration with the homogeneous product of these coordinate
quotients. It is the generic `degreeQuotientEquiv` specialized to these two
support subdiagrams.

`gradedDifferential` abbreviates the actual `FiniteFiltered.gradedMap` of the
signed differential. `gradedEquiv_differential` specializes the generic
commuting square `degreeQuotientEquiv_differential`. Thus the equivalence
identifies the actual descended differential, including every exterior sign.

## Conditional lifting

`gradedDifferential_injective_iff` transfers injectivity across the two degree
equivalences. `gradedDifferential_exact_iff` transfers equality of range and
kernel across three degree equivalences. The latter proof sends cycles through
the middle equivalence, takes a preimage under the asserted exact differential,
and returns it through the preceding equivalence. The other inclusion follows
from the signed differential squaring to zero.

`degreeDifferential_injective_of_graded` applies the published
`FiniteFiltered.injective_of_graded_injective` to the zero-to-full finite
filtration. `degreeDifferential_exact_of_graded` similarly applies
`FiniteFiltered.range_eq_ker_of_graded_exact`, using monotonicity, the zero and
full endpoints, and the existing square-zero law. Both require the Bruhat
covering hypothesis and the corresponding property of every adjacent grade
below the length of the rank-ordered Weyl list.

## Provenance and retained obligations

This is derived infrastructure. The actual support construction and its laws
are imported from Worker 379's `General.CorrectedFiltration`; the quotient
comparison and finite filtration lifting are imported from
`FilteredCutDiagram` and `Filtration.FiniteFilteredExactness`. The organization
parallels the published GL module `CorrectedJacquetCutFiltration`, with the
general support steps and subgroup families in place of its GL constructions.
No GL-specific equivalence or result is used.

This module proves conditional lifting, not exactness of the grades. It
neither constructs an actual Bruhat cover nor derives graded vanishing or
graded transition isomorphisms. It imposes no finite-length, admissibility or
irreducibility hypothesis on `A`. It does not prove
`RationalCorrectedTheorem36Statement`, eliminate its terminal cokernel, or
claim any additional result from the literature.
