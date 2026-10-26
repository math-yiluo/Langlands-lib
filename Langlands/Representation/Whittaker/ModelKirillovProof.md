# Conditional Kirillov lifting into actual coefficient models

Author: Worker 654.

`Langlands.Whittaker.modelKirillovTransfer` proves exactly
`Langlands.Whittaker.ModelKirillovTransferStatement.{uF,uV}`. Its explicit
premise is `Langlands.WhittakerTypeKirillovStatement.{uF,uV}`. The proof
transports that premise to each supplied `PadicField.TopologicalData` and the
actual coefficient image of each specified nonzero functional.

The supplied topology and the canonical topology are equal because each equals
the canonical module topology, by `topology_eq_canonicalModule`. Rewriting this
equality transports the entire remaining proposition, including character
continuity, admissibility, open subgroups and compactness. This is the topology
transport pattern of `RankinSelberg.ModelAsymptoticProof`; the present proof
uses the Kirillov premise directly.

For the canonical topology, the linear equivalence from the functional space
to `ℂ` in `IsOfWhittakerType` sends the specified nonzero functional `ℓ` to a
nonzero scalar. For any other functional `L`, injectivity of this equivalence
proves `L = (e L / e ℓ) • ℓ`. Thus the uniqueness hypothesis in the canonical
Kirillov premise holds for this very `ℓ`, without selecting or normalizing a
different functional.

The published `mem_glFunctionals_iff_entrywise` identifies functional
membership with the canonical premise's entrywise covariance equation.
The published `standardCharacter_eq_product` converts the covariance of the
input `WhittakerFunctions` element to the product character in that premise.
The smoothness clause of `IsMirabolicTestFunction` is already the required
open-subgroup clause. Its compact-support clause supplies the same compact
set after forgetting the upper-unipotent subtype of each witness.

Applying canonical Kirillov with the admissibility and finite generation
already in `IsOfWhittakerType` gives a vector `v`. The witness in the requested
coefficient image is `modelMap π ℓ v`. Its underlying value at `q` is
definitionally `ℓ.val (π q v)`, so the lifting equality follows directly.
The result compares values only at matrices with the stated mirabolic last
row. The field and representation universes remain independent. Every
`n : ℕ`, including `n = 0`, is covered by the same proof. The proof uses
neither irreducibility nor a topology on the representation module.

This is an internal conditional adapter. Its source content is the existing
canonical proposition, rather than a new source theorem or a proof of
canonical Kirillov. The corresponding original passage is H. Jacquet,
I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg Convolutions*,
American Journal of Mathematics 105 (1983), 367–464, registered as
`jpss-1983-rankin-selberg`. Section 2.1, printed page 385, specifies
admissibility, finite type and a one-dimensional functional space. Equation
(3), printed page 386, gives the actual coefficient functions. Section 2.2,
on page 386, defines the smooth, covariant, compact-modulo-unipotent
mirabolic functions and states their inclusion in the restricted model,
attributing the assertion to [G-K]. This adapter relies on that JPSS passage
through the explicit canonical premise and asserts no independent proof of
[G-K].

Both original pages were read visually in the retained PDF
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
They are one-based PDF pages 20–21. No JPSS errata entry was present in the
checked project or Library notes. The existing statement pair and imported
modules are unchanged.
