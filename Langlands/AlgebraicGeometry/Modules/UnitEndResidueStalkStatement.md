# Scalar residue criterion for structure-module endomorphisms

`Langlands.SchemeModule.UnitEndResidueStalkCriterion` is a proposition
quantifying an arbitrary scheme `X : Scheme.{u}`, an endomorphism `φ` of
its structure module, and a point `x : X`. It asserts that the induced map
on the underlying abelian-group stalk at `x` is an isomorphism if and only
if the global section `φ(1)` has nonzero image under `X.Γevaluation x`.
The residue field and evaluation map are Mathlib's actual constructions.
There are no hypotheses on affineness, quasi-compactness, or separation.

This is an internal derived interface for the scalar step in the published
`LineBundleResidueStalkCriterion`. In a local rank-one chart, a section
morphism becomes an endomorphism of the structure module. Linearity makes
such an endomorphism multiplication by its value at one. The displayed
criterion expresses the local-ring fact that multiplication by a scalar is
invertible exactly when its residue is nonzero, using the existing actual
abelian-group stalk API. This file states the criterion and does not prove
or assume it as an axiom.

This scalar statement contains no comparison between categorical module
pullback and stalks. The separate actual residue-section comparison in a
local chart is needed to use it for `LineBundleResidueStalkCriterion`.
The formulation is derived from the existing structure-module, stalk, and
residue-field definitions, rather than a transcription of an additional
literature theorem.
