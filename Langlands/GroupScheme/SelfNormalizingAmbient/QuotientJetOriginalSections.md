# Retained jet coordinates of the original actual subgroup

Let `G` be an affine group over `Spec R`, let `i:H→G` be an actual closed
subgroup, and let `D : ProperQuotientJetData i Q` retain the ambient coordinate
algebra `B`, subgroup ideal `I`, and quotient data. For any base change
`b:S→Spec R`, order `n`, and affine open `U⊂S`, the construction
`D.originalBaseChangeJetEquiv b hi n U` identifies
`Γ(S,U) ⊗_R B/(I+aug^(n+1))` with sections over `U` of the actual original
subgroup's base-changed identity jet.

It composes the actual cut subgroup's jet comparison with `IdentityJet.isoSections`
applied to the base change of `D.cutRepresentativeIso hi`. The latter is an
isomorphism of actual group schemes that preserves the ambient inclusion.
Affineness of the original source follows from the closed immersion into `G`;
relative affineness survives every base change.

`originalCutProjection_eq_ambientProjection` states that inclusion compatibility
after base change is exactly the original subgroup's ambient-coordinate
projection. The proof uses the pullback projection law and the original cut
representative inclusion equation. The theorem
`originalBaseChangeJetEquiv_tmul_mk` then sends `a ⊗ class(c)` to `a` times the
actual jet restriction of that ambient coordinate. Function pullback under the
actual group isomorphism and literal substitution under the quotient spectrum
map establish this formula.

This is an internal consequence of the imported all-test cut representative,
actual cut identity-jet sections, and actual group-homomorphism jet section APIs.
No smoothness or flatness premise is added. It supplies the original subgroup
model; comparison with its conjugate family's orbit map and descent to the
classified Grassmannian kernel remain separate obligations.
