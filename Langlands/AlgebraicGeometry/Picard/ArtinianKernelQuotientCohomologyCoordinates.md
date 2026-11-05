# Finite coordinates on actual quotient cohomology

This internal construction works over an arbitrary commutative ring `k`,
a residue field `K` with `Algebra k K`, and an actual scheme
`f : X ⟶ Spec k`, in arbitrary common universe `u`.
It uses the actual augmented local Artinian tests and their actual relative
scheme spaces. The results in this file require no flatness, properness,
quasi-coherence or finite-cohomology hypothesis.

`residue_testSectionHom` identifies restriction of a source scalar to the
actual residue fibre with its specified augmentation followed by the residue
structure map. It reuses `ArtinianKernelQuotientTensor.baseScalar_naturality`
with the commuting square of the residue immersion. That shared lemma uses
functoriality of section maps and naturality of the canonical global sections
isomorphism for spectra. Its original application treats quotient scalars;
here it is specialized to the residue immersion. `residue_scalarHom_app`
then computes an explicit base-scalar sheaf map into the residue structure
pushforward: on sections it is multiplication by the augmented scalar.

`residueProductCohomologyCoordinates f A ι n` is an `A`-linear equivalence
from actual degree-`n` relative cohomology of the finite product of residue
structure pushforwards to tuples of actual `H^n(X_K, O_X_K)`, with scalars
restricted along `A.augmentation`. It composes the existing finite-product
cohomology isomorphism and the existing residue structure cohomology
isomorphism in every coordinate. The index type `ι` is finite, and may be
empty. `residueProductCohomologyCoordinates_apply` identifies a coordinate
with the actual cohomology map of the corresponding sheaf projection,
followed by the canonical residue comparison.

Let `q : A → B` be an elementary surjection, `W` a subspace of its actual
kernel with the descended `K` action, `AQ` the actual quotient test, and
`r : AQ → B` its reduction. Write `h : X_AQ → X_A` for the actual induced
map. Given finite bases `b` and `c` of the actual kernels of `q` and `r`,
`kernelQuotientMatrix q W b c` is the existing matrix with target rows and
source columns.

`quotientProductMap_projection` expresses the actual quotient sheaf map
followed by a pushed-forward target projection as a finite sum of source
projections multiplied by lifted base scalars, followed by the actual
`residueQuotientIso`. Its inputs include arbitrary elements `a j` of `A`
whose augmentations are the relevant matrix coefficients. The proof is an
equality on all open sections, using the published section coordinate
formula, the scalar calculation above, and the actual residue restriction.
No affine-open restriction is imposed.

`quotientProductCohomologyMap_coordinates` proves that the actual canonical
quotient cohomology map has precisely that same matrix in the residue-fibre
cohomology coordinates. For every degree `n`, element `x` and target index
`l`, its coordinate is

`∑ j, kernelQuotientMatrix q W b c l j • residueProductCohomologyCoordinates f A ι n x j`.

The proof chooses scalar lifts using the specified augmentation's
surjectivity. The bundled linear action on hom spaces from
`DerivedSectionsLinear` carries the finite sum into cohomology, and
`relativeCohomology_map_scalarHom` computes each scalar term. Naturality
and precomposition for the independently defined closed-immersion
cohomology map relate this to the actual quotient map. The existing
`residueStructureCohomologyIso_quotient` identifies both resulting residue
cohomology groups with the same actual residue-fibre group. Finally,
linearity of that comparison turns each lifted source scalar into its
augmentation, which is the specified matrix coefficient.

The provenance is internal: the new comparisons are formal consequences of
the actual section, scalar and cohomology constructions and their proved
naturality identities. Scalar lifts are elements, with no multiplicative
or additive compatibility required; no residue-field section or `K`-algebra
structure on `A` is assumed. Tensor naturality, obstruction naturality and
the exact field Picard-stack atlas theorem remain further obligations.
