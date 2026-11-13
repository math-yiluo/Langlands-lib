# Coefficient extension of actual formal coordinate atlases

This module constructs coefficient extension of a supplied principal-open
atlas of formal `O`-modules from a commutative ring `R` to an `R`-algebra `S`.
It extends actual formal chart laws and transports their actual formal
transition isomorphisms.

The source convention is Drinfeld, *Coverings of p-adic symmetric regions*
(1976), printed p.109 (PDF page 3), paragraph immediately before section 2:
formal groups may be glued from formal groups over localizations of the
base. Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The coefficient construction below is derived from the Library's actual
formal laws, coefficient extension and atlas transitions; it is not a
separate numbered theorem of that article.

The hypotheses are arbitrary commutative rings `O : Type u` and
`R : Type v`, an `O`-algebra structure on `R`, a fixed finite coordinate
type `σ : Type`, and `S : CommAlgCat.{v} R`. Coefficient tests for the new
atlas are `A : CommAlgCat.{v} S`. The original chart set can be infinite;
its covering hypothesis is `Ideal.span X.opens = ⊤`. No flatness or
injectivity of `R → S` is required. This unit constructs an atlas and
individual chart comparisons. Independence from the chosen generators,
compatibility with iterated base change, a comparison of complete
compatible-family point functors, refinement descent, and preservation of
order actions, specialness or heights remain separate obligations.

`restrictTest` views an `S`-algebra as an `R`-algebra through its structural
map, and `restrictTestHom` restricts the coefficient homomorphism. The
local `coefficientAlgebra` and `coefficientScalarTower` instances specify
the composite `O`-action through the relevant base ring.

`baseOpens` is the image of `X.opens` under `algebraMap R S`.
`baseSource` chooses an original generator above each image generator.
Different original generators may have the same image; the construction
uses one chosen preimage for that chart. `baseSource_image` records the
actual image equation. Mapping the ideal spanned by the original generators
proves `baseOpens_covers`. If an image generator is invertible on a test
algebra, `baseSource_unit` proves that the chosen original generator is
invertible there too.

`baseChartCoefficient_unit` proves that the chosen original generator is
invertible in the localization of `S` at the image generator.
`baseChartCoefficient` uses the localization universal property to construct
the `O`-algebra map
`R[1/baseSource(b)] → S[1/b]`. Its algebra-map equation is
`baseChartCoefficient_algebraMap`. `baseCoefficient_comp` states that
extending along this map and then to a test algebra agrees with directly
extending the original localization to the restricted test. Its proof uses
uniqueness of homomorphisms out of the original localization and checks the
equation on `R`.

`baseChart` extends the actual original chart law along
`baseChartCoefficient`. `baseChartIso` compares its extension to a test
with the original chart's extension to the restricted test. The coefficient
triangle makes their addition series and all `O`-action series equal.
`Iso.ofIdenticalCoordinates` therefore supplies actual forward and inverse
formal homomorphisms, both with identity coordinate series.

`baseTransition` follows the source chart comparison, the original transition
on the restricted test, and the inverse target chart comparison.
`baseTransition_coordinates` proves that its coordinate series are exactly
those of that original transition, by removing the identity coordinate maps.
`baseChange` packages these charts and transitions into `BasicAtlas O S σ`.
Identity and cocycle laws follow by extensionality of actual formal
homomorphisms and the original laws. Coefficient naturality is the original
formal coordinate equation applied to `restrictTestHom`. These are equations
of formal maps, before their evaluation on points.

`baseChangeChartEquiv` evaluates `baseChartIso` to give an `O`-linear
equivalence between one new chart's nilpotent points and its chosen original
chart's points on the restricted test. The `apply` and `symm_apply` lemmas
prove that both directions preserve the actual nilpotent coordinate tuple:
each evaluates the identity coordinate map. The equivalence is constructed
from the formal inverse maps, rather than supplied as point data.
