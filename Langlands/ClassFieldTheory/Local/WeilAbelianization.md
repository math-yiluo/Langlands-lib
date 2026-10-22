# Abelianization and inertia quotients of the existing Weil pullback

Author: Worker 21. This construction uses published Galois and generic Weil
pullback modules. Its own independent review and publication remain required.

The namespace `LocalClassField.WeilQuotients` uses the existing
`Langlands.Weil.Pullback φ`. It does not introduce another Weil group.
`Abelianization φ` is Mathlib's quotient by the closure of the commutator,
with the quotient topology of that pullback. In particular, the source
topology comes from the subgroup of `Γ × ℤ_discrete`, not the topology
induced by its projection into `Γ`.

`projection` is the continuous quotient map. `degree` is the continuous
descent of integer degree. `toGroupAbelianization` is the induced comparison
to the topological abelianization of `Γ`. When `Γ` is an absolute Galois
group this is a map to the compact profinite quotient; this file does not
assert that it is an isomorphism or even that its image is dense.

`inertia` is the kernel of descended degree. The intrinsic quotient
calculation `inertia_eq_image` proves that it equals the image of the
original degree-zero subgroup. `UnramifiedQuotient` divides by that actual
subgroup, and `unramifiedProjection` is its continuous quotient map.
`unramifiedDegreeEquivRange` applies the first isomorphism theorem and the
quotient-topology criterion to identify this quotient with the image of
degree, a subgroup of the discrete integers. Continuity of the inverse
follows from that discrete topology. `unramifiedDegreeEquiv` identifies
it with all the integers only under the explicitly supplied surjectivity
of the original degree map. It does not assume surjectivity for an
arbitrary `φ`.

`characterDescent` is the actual equivalence between continuous complex
quasicharacters of the pullback and its topological abelianization.
Its construction uses the closed kernel in the Hausdorff complex unit
group. `map` descends a specified continuous homomorphism between the
actual pullbacks. It does not construct the field-extension pullback map.

`localPullbackAbelianization F φ` and `localPullbackToGalois F φ` specialize
these objects to the actual `Field.absoluteGaloisGroup F.Carrier`. The
continuous map `φ` is explicitly supplied. Its identification with the
geometric residue-degree map, and the local Weil assembly itself, remain
the existing parameter/residue tasks' work. This specialization is not a
claim to have constructed that missing map.

## Original sources and convention

Deligne, *Les constantes des équations fonctionnelles des fonctions L*
(1973), section 2.3, internal pages Del-23–24 / printed pages 523–524 /
PDF pages 23–24, describes the topological Weil abelianization and its
reciprocity identification. Worker 21 read both original pages and
visually checked the normalization and norm/transfer diagrams.
Deligne's integer quotient uses arithmetic Frobenius and therefore has
a minus sign in its valuation comparison. The project instead assigns
degree `+1` to geometric Frobenius. Once the actual residue-degree map is
available, the normalized comparison with additive valuation therefore
has a plus sign. This generic quotient module makes no choice of `φ`.

Registered source `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`,
file `C:/Central-Library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
Henniart (2000), section 1.1, printed page 439 / PDF page 1, states the same
geometric-Frobenius/uniformizer normalization; the original page was read.
Registered source `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

The definitions and their quotient certificates are a derived implementation
using Mathlib, not a formalization of the reciprocity theorem in these
passages. No reciprocity equivalence, its existence, or canonical inverse
into an unabelianized Weil group is assumed or constructed.

## Dependencies and validation boundary

The project imports are `Langlands.Weil.Pullback` and
`Langlands.ClassFieldTheory.Local.Galois`. Their Lean/Markdown pairs were checked
against the current Library and are unchanged.
The prepared environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development check `cd937d6c-2958-4282-9e30-2d26a308d351` compiled the
whole module without errors or warnings and inspected
`localPullbackToGalois` in universe `u` with only standard allowed
assumptions. The combined construction build
`b73aa15f-0efc-4b49-aa5d-450c72998b9c` also passed without diagnostics.
Independent semantic review and current publication remain required.

## Topic-hierarchy migration

Worker 63 relocated this pair from `Langlands.LocalClassField.WeilAbelianization` to
`Langlands.ClassFieldTheory.Local.WeilAbelianization` at Library base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 21 remains the
author of every mathematical declaration and construction certificate above.
Only imports were rewritten in the Lean source; all declaration text, including
universes, hypotheses, definitions, proofs and instance declarations, was retained.
The old path is a declaration-free re-export with its own paired documentation.

The full [module table and declaration-preservation ledger](Completion.md#topic-hierarchy-migration-ledger)
records this mechanical migration and its validation. Original source citations
and mathematical explanations are retained; their historical submission-status
remarks describe the original contribution, not this relocation's review status.
