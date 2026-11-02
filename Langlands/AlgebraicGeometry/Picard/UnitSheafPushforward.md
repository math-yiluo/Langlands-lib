# Actual unit sheaves and cohomology under topological pushforward

The namespace `Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward`
constructs comparisons for the actual unit sheaves defined in the published
`NilpotentUnitReduction` module. The constructions work at every universe `u`.
For the cohomology comparisons, the underlying spaces, section rings, abelian
coefficient groups and Ext groups have universe `u`.

`unitsPushforwardIso` applies to a continuous map `f : X ⟶ Y`, a presheaf
`F` of commutative rings on `X`, and a proof that `F` is a sheaf. It identifies
the unit sheaf of the actual pushed-forward ring sheaf with the actual
pushforward of the unit sheaf. Both have the same sections and restriction
maps, so the isomorphism is the identity. Its component on every open is
recorded by `unitsPushforwardIso_hom_app`.

For a topological isomorphism `e : X ≅ Y`,
`sheafPushforwardEquivalence` makes actual pushforward along `e.hom` an
equivalence of sheaf categories, with inverse pushforward along `e.inv`.
It works for coefficients in any category. The unit and counit are the
isomorphisms of Mathlib's presheaf equivalence, lifted to actual sheaves.
Their naturality is proved by forgetting to presheaves.

For abelian-group coefficients, `constantInversePushforwardIso` identifies
the inverse pushforward of a constant sheaf on `Y` with the corresponding
constant sheaf on `X`, naturally in the coefficient group. The constant-sheaf
functor is left adjoint to global sections. Composing that adjunction on `Y`
with the inverse-pushforward adjunction gives the same right adjoint as
global sections on `X`. Uniqueness of left adjoints supplies the isomorphism.

`cohomologyPushforwardEquiv` is the additive equivalence

\[
H^n(Y,e_*F)\;\simeq\;H^n(X,F)\qquad(n\in\mathbb N)
\]

for every actual abelian-group sheaf `F` on `X`. These are Mathlib's
`CategoryTheory.Sheaf.H` groups, defined by Ext from the constant sheaf
with coefficient `ULift ℤ`. The sheaf categories are Grothendieck abelian,
so Mathlib supplies the needed `HasExt` instances. The pushforward
equivalence preserves finite limits and colimits and is additive, as follows
from its preservation of binary products. Its inverse adjunction therefore
gives an additive Ext equivalence. The constant-sheaf isomorphism changes
the first argument to the constant sheaf on `X`. No exactness of pushforward
along an arbitrary continuous map is assumed. Specializing to actual unit
sheaves gives `unitsCohomologyPushforwardEquiv`.

For arbitrary schemes `X Y : Scheme.{u}` and a closed immersion
`i : Y ⟶ X`, `nilpotentClosedImmersion_surjective` proves that a nilpotent
ideal-sheaf kernel `i.ker` makes the underlying map surjective. If
`i.ker ^ n = 0`, its power `n+1` is also zero. A positive power has the same
support as `i.ker`, and the zero ideal has full support. Mathlib identifies
the kernel support with the closure of the image. The image of a closed
immersion is closed, so it is the whole space.
`nilpotentClosedImmersionTopIso` combines this surjectivity with the closed
embedding to construct an actual topological isomorphism. Its forward map
is exactly `i.base`, as proved by `nilpotentClosedImmersionTopIso_hom`.

Finally, `nilpotentUnitsCohomologyPushforwardEquiv` specializes the comparison
to the structure sheaf of `Y`. It identifies, in every degree, the cohomology
on `X` of the unit sheaf of the actual pushed-forward structure sheaf with
the cohomology on `Y` of its actual structure-unit sheaf. Its hypotheses are
only a closed immersion and nilpotence of `i.ker`; no properness, base field,
reducedness or affine assumption is used.

These are internal derived adapters. Their provenance is the published
actual-unit construction and Mathlib's topological presheaf equivalence,
constant-sheaf adjunction, exact-adjunction Ext comparison, and ideal-sheaf
support lemmas. In particular, the module uses
`TopCat.Presheaf.presheafEquivOfIso`, `constantSheafAdj`,
`CategoryTheory.Adjunction.extEquiv`,
`AlgebraicGeometry.Scheme.IdealSheafData.support_pow_succ` and
`AlgebraicGeometry.Scheme.Hom.support_ker`.
It does not assert an external literature theorem beyond these imported
results. It does not identify Picard classes with H1, classify deformations,
or prove Picard representability. It imports no pending exact-sequence
candidate.
