# Finite unramified maximality and Galois exhaustion

Worker 60 assembled this proof from the complementary finite arithmetic and
Galois helpers developed with Worker 1199. Worker 118 contributed the target
design and original-source correspondence.

`Langlands.LocalGalois.Separable.separableUnramified` proves the exact published
`Langlands.LocalGalois.Separable.SeparableUnramifiedStatement.{u}`, for an
arbitrary universe `u`. The base field has the statement's supplied field,
valuation relation, topology and nonarchimedean local-field structure.

## Implemented proof

`finiteUnramifiedMaximality F` treats an arbitrary finite-dimensional
`E : IntermediateField F (SeparableClosure F)`. The four local instances are
exactly the published `localNormedField F`, `localNormedField_ultrametric F`,
`localNormedField_complete F` and `localResidue_finite F`.

The proof composes three equivalences:

1. `IntermediateField.le_iff_le` identifies containment in the fixed field of
   `separableInertia F` with containment of inertia in `E.fixingSubgroup`.
   The fixed field and inertia are the actual published objects.
2. `inertia_le_fixingSubgroup_iff_residue_finrank`, applied to `F`,
   `SeparableClosure F` and `E`, identifies this subgroup containment with
   equality of the canonical residue degree and `[E : F]`. The finite residue
   field instance for `E` comes from the arithmetic helper. The Galois
   hypothesis is on the ambient separable closure; `E/F` need not be Galois.
3. `arithmeticUnramified_iff_residue_finrank`, in reverse, identifies that
   equality with the unchanged independent `ArithmeticUnramified F E`.
   This predicate asserts equality of the mapped maximal ideal with the
   extension maximal ideal and separability for the canonical residue algebra.

The final theorem pairs this maximality result with
`finiteUnramifiedGaloisExhaustion_of_maximality F`. That helper maps a finite
set through the actual `fixedFieldToSepClosure F`, adjoins its image inside
the same separable closure, and takes its finite normal closure. Normality of
the inertia fixed field keeps this Galois extension inside it; the maximality
result just proved supplies arithmetic unramifiedness. The construction
includes the empty finite set.

The imported arithmetic helper establishes integral-closure finiteness,
freeness and rank for the spectral integer rings, then uses the canonical
closed-fiber surjection and finite-dimensional linear algebra to obtain its
criterion. The imported Galois helper compares the canonical spectral residue
objects along a finite tower, lifts residue stabilizers, and computes subgroup
indices. This proof adds the composition of those results and discharges the
maximality premise of the exhaustion helper.

## Source correspondence and scope

This is a derived proof of the target's source formulation. Serre, *Local
Fields* (1979), II §2 Proposition 3 and its corollaries, printed pp. 28–29
(PDF pp. 36–37), supply the finite integral-closure setting; III §5 Theorem 1,
printed p. 53 (PDF p. 60), supplies the arithmetic unramified criterion.
Theorems 2–3 and Corollary 1 there, printed pp. 54–55 (PDF pp. 61–62), describe
the residue correspondence and maximal unramified extension. I §7 Propositions
20–22, printed pp. 21–22 (PDF pp. 29–30), and IV §1 Proposition 1 and the
corollary after Proposition 2, printed pp. 62–63 (PDF pp. 69–70), relate inertia
to that extension. The implemented quotient-dimension and subgroup-index
argument is explained above; it need not follow the book's ramification-index
proof.

The registered source is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
These original passages and the registered
`serre-book-corrections-2019`, PDF pp. 2–3, were read during development.
The corrections, SHA-256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
do not change the passages used here.

The result retains the actual separable closure, supplied valuation relation
and topology, canonical spectral integer rings, canonical residue algebras
and actual fixed-field inclusion. It applies in mixed and equal
characteristic, with no characteristic-zero or perfection hypothesis on `F`.
It assumes no completeness or local compactness of the infinite fixed field.
Residue algebraic closure, intrinsic discreteness, DVR and Henselian
arithmetic of that field remain separate conclusions.
