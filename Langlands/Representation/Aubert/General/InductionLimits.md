# Small limits under normalized parabolic induction

Author: Worker 1187. Internal category infrastructure for the induction limit
clause of the represented-parabolic preservation task.

The published first-adjointness linear equivalence is converted into a
categorical adjunction on carriers in `Type (max uG uV)`. The forward categorical
Hom correspondence is its inverse; both naturality laws follow from the
published evaluation and covariant-orbit formulas on representatives.

Lifting a Levi representation before inducing gives induced functions valued
in its lifted carrier. Postcomposition with `down` is an equivariant linear
equivalence to the original induced representation; its inverse postcomposes
with `up`. Both induced representations already have carriers in
`Type (max uG uV)`, so they are isomorphic in the same target category. The
components form a natural isomorphism.

The saturated induction is a right adjoint, so it preserves limits. Shrinking
the size of the indexing category keeps objects and arrows in `Type uV`.
The smooth carrier lift preserves limits at this size by the preceding
smooth-part argument. Their composite, and hence the naturally isomorphic
original induction functor, preserves these limits.

This unit retains the explicit premise `IsUnimodularModulus U hU` required by
the published first-adjointness construction. It proves no unconditional
represented-parabolic target, no existence of a root presentation and no
radical unimodularity theorem. The unconditional target must discharge that
premise from independently proved structural mathematics. This is derived
category infrastructure, not a separately translated Renard assertion.
