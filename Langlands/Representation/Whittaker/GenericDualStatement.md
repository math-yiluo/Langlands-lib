# Generic contragredients and inverse transpose

`Langlands.GenericContragredientStatement` is a proposition about
actual complex representations of `GL_(n+1)(F)`, for every positive rank,
every prime `p`, and every finite extension `F : Langlands.PadicField p`.
The field and representation-space universes are independent. The topology
is that of `F.canonicalNormedField`. No topology is put on the vector space,
and that space is not assumed finite-dimensional.

This module defines the proposition and proves nothing. Its proof,
`Langlands.genericContragredient`, whose type is exactly
`GenericContragredientStatement.{uF,uV}`, is in the companion module
`Langlands.Representation.Whittaker.GenericDualProof`. That proof takes the
first conclusion from the published Gelfand–Kazhdan theorem
`Langlands.gelfandKazhdanContragredient`, of
`Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`, which
needs only admissibility and irreducibility. It takes the second conclusion
from the published `Langlands.Whittaker.explicitSmoothDualFunctional` and its
lemmas `explicitSmoothDualFunctional_ne_zero` and
`explicitSmoothDualFunctional_covariance`, of
`Langlands.Representation.Whittaker.GenericDualTransport`, applied to the
given nonzero functional.

The hypotheses are irreducibility and admissibility of the representation,
and genericity for a specified continuous nontrivial unitary additive
character `psi`. Genericity is expressed by existence of a nonzero linear
functional with the actual upper-unitriangular adjacent-entry covariance.
This is a hypothesis on the representation, not a claim that every
irreducible representation is generic.

The first conclusion asserts existence of a complex linear equivalence
`E : V ≃ₗ[ℂ] SmoothDual rho` satisfying

`E(rho(transpose(g inverse))v) =
 smoothContragredient rho g (E(v))`.

Thus it is the inverse-transpose action that is equivalent to the smooth
contragredient. The carrier `SmoothDual rho` is the actual submodule of
smooth vectors in the full algebraic dual; its action is
`(g ell)(v)=ell(rho(g inverse)v)`. The proposition does not replace it by
the whole algebraic dual. The equivalence is existential, with no claim
of a canonical normalization.

The local `invTranspose` expression is the actual transpose of the inverse
matrix, bundled into the general linear group using its nonzero determinant.
The only proof term in the proposition definition supplies this intrinsic
well-formedness certificate: transposition preserves determinant and the
inverse of an invertible matrix has nonzero determinant. It does not prove
either conclusion of the proposition. No arbitrary automorphism or
assumed representation is supplied in place of the actual matrix formula.
The Library's reusable bundled inverse-transpose automorphism is the separate
`Langlands.GeneralLinear.inverseTranspose` of `Langlands.Group.GL.Maps`. This
module does not import it. The companion proof identifies `invTranspose g`
with `GeneralLinear.inverseTranspose (n + 1) F.Carrier g` by `Units.ext` and
`rfl`.

The second conclusion asserts that the smooth contragredient has a nonzero
Whittaker functional for `psi inverse`, using the same explicit upper
unitriangular subgroup conditions. For a unitary additive character this
inverse equals its complex conjugate, matching the source convention.
It is not a claim about the original representation with unchanged action.
Rank one is included: inverse transpose is inversion, the upper-unipotent
group is trivial and the source's inverse-character representation is the
contragredient.

## Original source and precise scope

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*,
American Journal of Mathematics 105 (1983), 367--464:

- Section 0.3, pages 375--378, fixes the general linear group, inverse
  transpose, smooth contragredient, right-translation and character
  conventions; page 377 defines `pi^iota(g)=pi(g^iota)`.
- Section 2.1, page 385, defines Whittaker functionals and Whittaker type,
  recalls multiplicity at most one for irreducibles, and the character
  transport convention.
- Section 2.1, page 386, equation (4) gives
  `W_tilde(g)=W(w_r g^iota)` in the model for `pi^iota` and conjugate
  `psi`. The following irreducible paragraph records equivalence of
  `pi^iota` with the contragredient. The preceding rank-one formulas
  identify the resulting inverse character explicitly.

The source attributes the contragredient equivalence to Gelfand--Kazhdan.
This target records the specialization used by JPSS in its integral theory;
this module supplies no formalization of that proof. The companion proof
obtains the equivalence from the published
`Langlands.gelfandKazhdanContragredient`, described above. The target retains
the generic irreducible admissible scope. Existence of a nonzero functional together
with irreducible multiplicity one gives the source's Whittaker-type
hypothesis; that multiplicity-one fact is a separate result, not an axiom
imported by this target. Inverse-character genericity of the
dual is the reformulation obtained from the transformed model and the
existential equivalence. The pointwise Weyl-transformed model identity and
the functional equations themselves remain separate targets.

Registered source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Original retained file:
`C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
The cited original pages, including displayed formulas, were read.

## Definitions, dependencies and status

Direct project definition dependencies:

- `Langlands.LocalField.Definitions`.
- `Langlands.Representation.Smooth.Contragredient.Definitions`.
  The effective Lean SHA256 is
  `878b6130d7c563ead853cbdd50a6c70aac01f9104062049e696f9e68cbb30de3`;
  the effective Markdown SHA256 is
  `531fc58fb846d22f48363964f7fb5af0ab9459747c7ca08a683df6ada7c8aae0`.
  Publication commit: `933f2719b54fcf01bebb367c9cae56b8d5f17edc`.

The contragredient construction imports the algebraic-dual
definitions `Langlands.Representation.Dual.Definitions` and smooth-part
definitions `Langlands.Representation.Smooth.SmoothPart.Definitions`;
foundational smoothness and admissibility are from
`Langlands.Representation.Smooth.Definitions`.
The availability of all dependencies was checked at Library commit
`9007729971e6e6ecea63b5567b6d1621769ccfb0`.
No Whittaker construction or theorem proof is imported.

The environment is Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Mathlib supplies the actual general linear matrices, their determinant,
transpose and inverse, complex linear equivalences, representations,
irreducibility and additive characters.

A development check compiled the entry module and reused
its five unchanged project dependencies, with zero errors and warnings.
Exact inspection reports a proposition definition with the two universe
parameters `uF` and `uV` and target fingerprint
`2d57e7217d2a08e3de8e5fd0f50bdd501c608f0742638b6e461647470b8af33e`.
Its only reported assumptions are the standard Lean principles
`propext`, `Classical.choice` and `Quot.sound`.

A separate successful native `#print` inspection checked the elaborated
quantifiers, the positive-rank indexing, the explicit genericity hypothesis,
the actual inverse-transpose formula, and both conclusions. No additional
representation-space topology, finite-dimensionality, equivalence or dual
genericity hypothesis was introduced by elaboration.

Neither assertion is proved by defining or compiling this proposition. Both
are proved by the separate theorem `genericContragredient`.
