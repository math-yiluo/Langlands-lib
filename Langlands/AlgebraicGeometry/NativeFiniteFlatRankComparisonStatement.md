# Native finite flat rank and affine fraction-field degree

`NativeFiniteFlatRankComparisonStatement` records two local comparisons used
to relate the native rank in the polarized finite flat problem to field degree.
All maps and ranks retain their existing Mathlib meanings.

First, let `f : X ⟶ Y` be finite and flat, with `Y` affine and integral.
Via the algebra on global sections induced by `f.appTop`, the native
`f.finrank y` at every point of `Y` equals
`Module.finrank Γ(Y, ⊤) Γ(X, ⊤)`. Finiteness makes `X` affine.

Second, let `S` be a finite flat algebra over a domain `R`, with `S` a domain
and the algebra map injective, expressed by `FaithfulSMul R S`. The native
rank of the actual map `Spec S ⟶ Spec R` at every prime is
`Module.finrank (FractionRing R) (FractionRing S)`. The scalar action uses
`FractionRing.liftAlgebra R (FractionRing S)`, the canonical extension of
the given algebra map to fraction fields.

This is internal derived content. It combines Mathlib's affine naturality
of `Scheme.isoSpec`, invariance of native rank under pullback,
`Scheme.Hom.finrank_SpecMap_eq_finrank`, `Module.rankAtStalk_eq`,
`Ideal.finrank_fiber_eq_finrank`, and `IsFractionRing.finrank_eq`.
It does not construct intersection numbers or prove a polarized degree formula.
