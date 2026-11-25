# A complete simultaneous standard basis on the canonical Levi

This derived internal module assembles the full simultaneous standard-basis
property on the actual standard Levi scheme. It combines the compact-open
normal basis and inherited-basis transports with the compatible
component, Iwahori and weak-chamber transports. It states no new
original-literature assertion.

Let `G` be a connected reductive affine group scheme locally of finite type over
an arbitrary nonarchimedean local field. Fix a maximal split torus `i`, a generic
cocharacter `ν`, a subset `J` of its simple relative roots and an original
subgroup `K0` with `SimultaneousStandardBasisAt i ν K0`. Write `L` for
`Standard.leviScheme i ν J`, `iL` for its canonical torus map and `j` for its
closed immersion into `G`.

`standardLeviInheritedBasis` first selects one witness family `B` of the original
simultaneous basis property, then takes the literal preimages `j⁻¹(K)` for all
`K ∈ B`. The selection is made before every intrinsic face and member. The
relative compact subgroup is exactly `leviSchemeCompact K0 i ν J`.

`standardLeviInheritedBasis_spec` proves all required clauses for this same
family. `leviSchemeBasis_basisClauses` supplies its compact-open normal basis
property and all its inherited intersection-basis properties. The intrinsic
simple-root set is exactly `J`, so an intrinsic face `R` is a subset of `J`
and hence an original ambient face. The proof takes the original component
`A,q` selected for that face, transports its compatibility with
`IsCompatibleStandardSplitComponent.leviScheme`, and obtains every intrinsic
member clause from `StandardParabolicBasisMember.leviScheme`. Openness and
compactness are taken from the same original basis member.

The member transport includes the enlarged intrinsic weak chamber. Its earlier
proof uses an outer-central integral cocharacter adjustment which preserves
conjugation on `L`, and then the published contraction and cofinality theorem.
Thus the assembly retains every contraction, power-neighborhood and uniform
cofinality clause; it does not merely assemble Iwahori factorizations.

`SimultaneousStandardBasisAt.leviScheme` packages the resulting family and its
specification as the complete intrinsic simultaneous-basis property. The
original basis is an assumption. No existence of such an ambient basis, source
Iwasawa factorization at an arbitrary original compact subgroup, analytic
coefficient estimate or wave-packet Schwartz target is asserted here.
