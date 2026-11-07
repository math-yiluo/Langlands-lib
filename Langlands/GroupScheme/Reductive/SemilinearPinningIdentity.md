# Identity normalization for actual semilinear pinned lifts

This internal coherence unit works with actual group schemes over an arbitrary
scheme, then specializes to a supplied complete split pinning of an affine
group scheme over an arbitrary field in universe `u`. It makes no additional
field hypothesis.

`Descent.baseChangeEqIdentityIso b hb G` transports the actual pullback of `G`
along a base map `b`, given `hb : b = 𝟙 S`, to the identity pullback and then uses
the canonical `baseChangeIdIso G`. Its underlying scheme map is the pullback
first projection. `baseChangeEqIdentity_map_injective` proves that pullback
along `b` is faithful on group-scheme morphisms: substitute `hb`, apply
naturality of the canonical identity-pullback isomorphism, and cancel its
source isomorphism.

`Descent.baseChangeEqIdentity_tower` identifies the pullback of this comparison
with the actual iterated-to-direct `pullbackComparison b b b hbb G`, for
`hbb : b ≫ b = b`. The proof compares the two maps by their pullback
projections; the first projection is the preceding formula, and the second
is the structure-map equation in the over category.

`SplitPinning.semilinearPinnedIso_one_groupIso` identifies the ambient
isomorphism of the identity semilinear pinned lift, with trivial based
root-datum automorphism, with `baseChangeEqIdentityIso` for the base map induced
by `RingEquiv.refl`. Specialize the actual semilinear composition law to the
two identity ring equivalences and two trivial based automorphisms. Cancel
the common final ambient isomorphism. The tower formula then identifies the
two pulled-back maps, and identity-pullback faithfulness identifies the
original maps.

The provenance is an internal derivation from the imported actual scalar
coherence and semilinear composition constructions and the canonical
categorical pullback identities. This unit proves an equality of actual
ambient group-scheme isomorphisms. It does not construct an assembled Galois
descent datum, descend a pinning, or prove unconditional quasi-split
inner-form existence.
