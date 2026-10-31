# Scheme isomorphism invariance of actual derived sections: proof

`Langlands.AlgebraicGeometry.Modules.schemeIsoDerivedSections.{u}`
proves the named `SchemeIsoDerivedSectionsStatement.{u}`.
The helper
`DerivedSections.relativeDerivedSectionsPullbackIso e g`
constructs the natural isomorphism asserted by that proposition.

The proof installs the already published `pushforwardEquivalence e`
as the equivalence structure on pushforward along `e.hom`.
For every module `M` on `Y`, the positive higher direct images of
`e^* M` vanish by `closedImmersionHigherDirectImageVanishing`, since a
scheme isomorphism is a closed immersion. Thus the published
`derivedPushforwardComparisonIso` identifies the actual derived
sections of `e^* M` over `e.hom ≫ g` with those of `e_* e^* M` over `g`.
Its coefficient naturality, applied to pullbacks of module morphisms,
packages these components into a natural isomorphism.

The unit of the actual pullback–pushforward adjunction is an
isomorphism because its right adjoint, pushforward, is an equivalence.
Whiskering the inverse unit by actual derived sections over `g`, then
using the functor left unitor, identifies the latter functor with
derived sections of `M`. Composing the two natural isomorphisms gives
the result.

This is an internal composition of the published scheme-module and
derived-comparison constructions, authored by Worker 137. It applies
to every actual module without quasi-coherence or acyclicity premises
on the caller. It proves no geometric scalar base-change theorem and
provides no Čech-to-derived comparison or perfect representative.
