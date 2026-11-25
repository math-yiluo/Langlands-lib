# Whittaker uniqueness and model prerequisites

This module contains this proposition definition; no proof of it is claimed
here. The Library proves it as `Langlands.whittakerPrerequisites` in
`PrerequisitesProof`.

`Langlands.WhittakerPrerequisitesStatement` quantifies over every prime `p`,
every specified finite extension `F : Langlands.PadicField p`, and every
rank `n + 1`. The field and representation carrier have independent universes.
The representation is an actual Mathlib representation of
`Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier` on a complex vector space
`V`; no finite-dimensionality or topology on `V` is assumed.

The topology comes from the already constructed base-extending spectral norm
on `F`, and the general linear group has Mathlib's topology on matrix units.
No normalized absolute value, Haar measure, or Fourier transform is used by
this target. The distinction between the base-extending norm and the
residue-cardinality absolute value therefore introduces no factor convention.

The additive character is an actual `AddChar F.Carrier ℂ`, explicitly
continuous, nontrivial and unitary. The representation is admissible using
the `Langlands.IsAdmissible` predicate, which includes smoothness,
and irreducible using Mathlib's `Representation.IsIrreducible`.

For a matrix unit `g`, the conditions that every entry below the diagonal is
zero and every diagonal entry is one describe the actual standard upper
unipotent subgroup. The finite product
`∏ i : Fin n, ψ (g.val i.castSucc i.succ)` is its usual Whittaker character.
At rank one the product is empty and the subgroup is trivial.

The local `equivariant` predicate is the explicit equation
`ℓ(ρ(g)v) = θψ(g) ℓ(v)` for every such matrix and every vector. It is
fully defined within the target, not an arbitrary predicate supplied by a
caller. The published [GeneralLinear](GeneralLinear.md) module already
provides `Langlands.Whittaker.glFunctionals`, `glInverseFunctionals` and the
actual coefficient-image model. Its `glModelEquiv` requires irreducibility
and a specified nonzero functional; `glModel_isSmooth` transfers a supplied
smoothness hypothesis. The published [CharacterChange](CharacterChange.md)
module provides `characterChangeFunctionalEquiv` and
`characterChangeInverseFunctionalEquiv` for a unit `a` over a topological
field, without irreducibility, between the spaces for `ψ` and `ψ.scale a`.
The published [PrerequisiteInterfaces](PrerequisiteInterfaces.md) module
connects these constructions to this target. Its
`UnitaryAdditiveCharacter.ofComplex` packages the raw continuous, nontrivial
unitary `AddChar`; `standardCharacter_eq_product` identifies the bundled
sum formula with the adjacent-entry product, and
`mem_glFunctionals_iff_entrywise` identifies functional membership with the
explicit matrix covariance equation. Its `raw_exists_inverse_iff` proves
the second clause for the same representation, using scaling by `-1`;
`raw_coefficient_injective` proves the third clause under irreducibility and
a specified nonzero equivariant functional, without requiring admissibility.
This target does not create a second subgroup, character, functional-space
or model construction.

The target has three clauses:

1. Given two equivariant linear functionals with the first nonzero, the second
   is a unique complex multiple of the first. This expresses dimension at
   most one without assuming finite-dimensionality of the functional space.
2. A nonzero Whittaker functional exists for `ψ` exactly when one exists for
   `ψ⁻¹`, for the same representation. This does not assert existence for
   every irreducible representation.
3. For any nonzero Whittaker functional, the map taking `v` to the function
   `g ↦ ℓ(ρ(g)v)` is injective.

## Original source and correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367-464. Literature ID `jpss-1983-rankin-selberg`, retained-file SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Original file:
`C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.

The fingerprint was verified, and the retained scan's printed pages 375-378
and 381-386 were read visually. Printed page `a` is PDF page `a - 365`.
Only the following passages are the basis of this target:

- Section 0.3, pages 375-377 defines the actual matrix group, standard upper
  unipotent subgroup and product character. Page 378 fixes complex
  representations and the central-character convention.
- Section 2.1, page 385, equation (1), defines the equivariant linear forms.
  The paragraph after equation (2) recalls dimension zero or one for
  irreducible representations and explicitly distinguishes genericity.
  The following diagonal-conjugation argument permits replacement of
  `ψ` by its complex conjugate. For the explicitly unitary character
  here this is its inverse.
- Section 2.1, page 386, equation (3), defines the orbit functions
  `W(g) = ℓ(ρ(g)v)` and states that their model is equivalent to the
  representation when it is irreducible.

The source's integral theory also treats admissible finite-type representations
with one-dimensional Whittaker functionals, which need not be irreducible.
This prerequisite target concerns irreducible admissible representations only.
It must not be substituted for the broader Whittaker-type hypotheses of
Theorem 2.7. Irreducibility supplies finite type because a nonzero vector
generates the whole representation; the target does not assume the later
integral theorem. The rank-one instance uses that an irreducible admissible
representation of `GL₁(F)` is a character, consistently with the source's
central-character convention and its discussion of rank one.

The scalar formulation of dimension at most one and the injectivity formulation
of the irreducible Whittaker model are derived reformulations. The bundled
model equivalence and change-of-character equivalences described above are
already constructed, and the published raw-to-bundled adapters supply proofs
of the second and third clauses. The multiplicity-one argument is a separate
proof obligation; no proof of the full three-clause proposition is supplied
here. `PrerequisitesProof` proves it from `Whittaker.multiplicityOne` and
these adapters.

## Dependencies and boundary

Project imports are `Langlands.LocalField.Definitions` and
`Langlands.Representation.Smooth.Definitions`. When this statement was
checked, the two imported pairs had these hashes:

| Dependency | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| LocalField definitions | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` | `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf` |
| Smooth definitions | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` | `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569` |

Mathlib supplies additive characters, irreducible representations,
matrix units and their topology. The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

The representation-factor definitions and the group/classification
definitions are not part of this module.
This statement does not implement JPSS integrals or factors, assume their
existence, construct normalized induction, or assert that every irreducible
representation is generic.

A development check compiled the two
dependencies and the entry module with zero errors and warnings. Inspection
found a definition returning `Prop`, with independent universe parameters
`uF` and `uV`, no declared or disallowed axioms, and target fingerprint
`78e81f8a9179603f4f3738154c99928b6352e443d571438841e0c33ee2a0cd21`.
A separate native print of the elaborated definition retained all explicit
quantifiers, the actual matrix group, the three character hypotheses,
admissibility, irreducibility, and all three conclusion clauses. Its axiom
closure contains only `propext`, `Classical.choice`, and `Quot.sound`,
inherited from the mathematical definitions. These checks establish successful
elaboration, not truth of this proposition.
