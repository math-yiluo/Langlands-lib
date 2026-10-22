# Actual local Weil assembly

Author: Worker 53. This is a definition and construction contribution.

For every prime `p` and `F : PadicField.{u} p`, `localResidueField F` is the actual
residue field of `F.canonicalTopologicalData`. The carrier universe `u` is
unrestricted. `localResidueMap F` bundles the constructed absolute residue action
with its proved continuity. Composing with the finite-field comparison gives
`localResidueDegree F`, a continuous map from the actual absolute Galois group
of `F.Carrier` to the genuine profinite completion of the integers. The
comparison sends the arithmetic Frobenius `x ↦ x^q` to `-1`, so this is the
geometric normalization: geometric Frobenius has degree `+1`.

`localWeilGroup F` is exactly the previously constructed `Weil.Pullback` of that
map. It uses the subgroup topology inherited from the absolute Galois group
times the discrete integers. `localProjection`, `localDegree`, and
`localDegreeInt` expose the projection and geometric degree. No alternate
Weil group or topology is introduced.

`localInertia F` is the kernel of this degree, as a subgroup of the Weil group.
The finite-field comparison is injective, so the kernel of the profinite residue
degree is the actual absolute inertia subgroup (`localResidueDegree_ker`).
`localGaloisInertiaEquiv` records that equality as a continuous group
equivalence; `localInertiaInclusion` composes it with the existing degree-zero
inclusion into the pullback. These kernel and continuity proofs are intrinsic
obligations of the constructed inclusion.

The residue map and finite-field equivalence are both proved surjective in
their respective arithmetic proof modules. Their composite is therefore
surjective (`localResidueDegree_surjective`), and the existing pullback
degree-surjectivity theorem applies (`localDegree_surjective`). Only then does
`localGeometricFrobenius` choose a preimage of degree `+1`. Its degree equation
`localGeometricFrobenius_degree` is proved from the choice witness. Two such
lifts differ by an element of `localInertia F`, so values of characters trivial
on inertia do not depend on the choice. No lift, surjectivity certificate,
reciprocity map, or comparison equivalence is assumed as input.

`localUnramifiedCharacter F z` sends an element of degree `n` to `z^n`.
`localNormCharacter F` is the already constructed residue-normalized character
for the canonical realization, so its formula is `q^(-n)`, where `q` is the
actual residue cardinality; at geometric Frobenius it is `q^(-1)`. Complex
units carry their usual topology. Inertia, topological, projection,
residue-Frobenius and norm compatibility assertions are recorded separately in
the statement target `Langlands.Weil.Local.LocalAssemblyStatement`.

This is derived assembly of the field-theoretic Weil description in Henniart,
*Représentations du groupe de Weil d'un corps local* (1980), sections 2.1 and
2.2 (opening paragraph), printed page 158 (PDF page 5): `W_F` is the subgroup of
`G_F` acting on the residue field by integral powers of Frobenius, inertia is
the open subgroup acting trivially, the topology on inertia is induced from
`G_F`, and an element `Fr` inducing Frobenius generates `W_F / I_F ≅ ℤ`. The
geometric norm convention is that of Tate, *Number theoretic background*
(1979), Part II: (1.4.1), printed page 6 (PDF page 15), describes the same
subgroup with inertia open and `‖Frobenius⁻¹‖ = q⁻¹` for uniformizers;
(1.4.6), printed page 7 (PDF page 16), gives the norm homomorphism with image
the powers of `q`; (4.1.3), printed page 20 (PDF page 29), defines the degree
`v` by `‖w‖ = q^(-v(w))`. Here the group is realized as the pullback of the
degree map rather than as a subgroup of `G_F`; the projection is the
continuous inclusion of the sources, and its injectivity and density are
assertions of the separate statement target, not of this module.
The registered original sources are `henniart-1980-weil-representations`,
PDF SHA-256
`451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`,
and `tate-1979-number-theoretic-background`, Part II PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
These original passages were read directly in the registered files.

The project imports `Langlands.Galois.Local.AbsoluteProof`,
`Langlands.Galois.FiniteField.ComparisonProof`, `Langlands.Weil.AlgebraicProof`,
`Langlands.Weil.TopologyProof` and `Langlands.Weil.Local.ResidueCharacters` are
published at Library commit `68e8013fc4fed0de284fd849695676aca2e0c32d`. The
environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream source authorship is retained: Worker 9 constructs the absolute
residue action and proves its continuity, surjectivity and kernel, Worker 28
constructs the finite-field equivalence, Worker 2 constructs the generic
pullback, and the canonical local-field interface and normalization are reused
from their published modules. This file assembles those constructions without
copying their proofs. Actual finite-extension Weil subgroup maps, degree
scaling, inertia intersection and norm restriction are further implementation
obligations and are not supplied by this file.
