# Canonical adelic point bijections for Weil restrictions of algebraic spaces

Author: Worker 113.

This is a derived construction supporting the proof of
`Langlands.Global.AdelicSpaceWeilRestrictionStatement`, the formalization of
Conrad's Proposition 5.14. It packages the set bijection using the published
Weil point identification and the published adelic tensor equivalences. It
does not prove that a Weil restriction is an algebraic space or make any
assertion about continuity.

For a commutative base ring `C`, an algebraic space `X` over `Spec C` and an
equivalence `e : A ≃ₐ[C] B`, `RingPoints.changeRingEquiv X e` identifies
`X(A)` with `X(B)`. Its forward map is change of coefficients along `e`, and
its inverse changes coefficients along `e.symm`. The two inverse identities
use functoriality of pullback along spectra and the inverse identities of
`e`. These constructions use actual algebraic-space points.

For rings `R`, `R'`, `A` and `B`, with `R'` and `A` algebras over `R` and
`B` an algebra over `R'`, suppose the Weil restriction of `X'` over `Spec R'`
is an algebraic space, witnessed by `h`. A specified algebra equivalence
`e : R' ⊗[R] A ≃ₐ[R'] B` defines
`ringWeilRestrictionPointsEquivOfAlgEquiv`: first apply the published
`ringWeilRestrictionPointsEquiv R R' A X' h`, then change coefficients
along `e`. The intrinsic naturality lemma says that this identification
commutes with every morphism `X' ⟶ Y'` when both Weil restrictions are
algebraic spaces. Its proof combines the published naturality of the Weil
point identification with naturality of change of coefficients.

The two arithmetic specializations are:

- `curvePlaceSpaceWeilRestrictionPointsEquiv k F F' Y' h` for a
  finite-dimensional extension `F'/F` of function fields over a finite
  constant field `k`, using `curvePlaceAdeleTensorEquiv`. No separability
  of `F'/F` is assumed.
- `numberFieldSpaceWeilRestrictionPointsEquiv K K' Y' h` for an extension
  of number fields, using `numberFieldAdeleTensorEquiv`. These are the full
  adeles, including all infinite places.

The `_apply` lemmas verify, by definitional equality, that the forward maps
are precisely
`RingPoints.changeRing (adele tensor map) (ringWeilRestrictionPointsEquiv … x)`,
the maps appearing in the unchanged published proposition. Bijectivity is
therefore supplied without choosing models, and without separatedness or
finite type once the representability witness `h` is given.

Provenance is derived from the Library modules `SpaceWeilRestriction`,
`ProductPointsGluing`, `CurvePlaceAdeleTensorComparison` and
`NumberFieldAdeleTensorComparison`. The packaging and names are internal.
The original source for the intended arithmetic bijection is Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 5.14, printed p.20; registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This module proves only the constructions and identities described above;
the homeomorphism and existence parts remain separate proof obligations.

The generic `RingPoints.changeRingEquiv` and its two computation lemmas now
live in `AlgebraicSpace.RingPointsEquivalence`, imported here. Their public
names, explicit space argument and definitions are unchanged.
