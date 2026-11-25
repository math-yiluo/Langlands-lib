# Adjoint geometric fibres and arbitrary base change

This internal helper supplies the adjointness comparisons used in the affine
adjoint Weil-restriction problem. All schemes and coefficient fields lie in an
arbitrary universe `u`. No smoothness, affineness, characteristic, algebraicity,
separability or reducedness hypothesis is added to the predicates being compared.

`center_eq_bot_baseChange_iff` states that triviality of the full
scheme-theoretic centre is preserved and reflected by an fpqc morphism of bases
(flat, surjective and quasi-compact). Preservation uses the published equality
between the pulled-back centre and the centre of the pulled-back group.
Reflection uses the published fpqc reflection of trivial subgroup functors.
Thus the result concerns central points on every relative test scheme.

`IsAdjoint.baseChange_fieldExtension`, `IsAdjoint.of_fieldExtension` and
`isAdjoint_fieldExtension_iff` compare adjointness under an arbitrary extension
of fields. They combine the centre comparison with the published preservation
and reflection of semisimplicity. Field-extension spectrum maps are fpqc.

`IsFibrewiseAdjoint G` means that every chosen geometric fibre of `G` is
adjoint, using the Library's algebraic closure of its residue field.
`fieldAdjoint_iff_residueFiber`, `geometricAdjoint_iff_residueFiber` and
`fieldAdjoint_iff_geometricFiber` identify this test with adjointness of the
actual residue-field fibre and of any specified field-valued pullback at that
point. The implemented proof factors the field-valued point through its
residue-field embedding and uses `fieldPointFiberIso` followed by the
field-extension equivalence.

`IsFibrewiseAdjoint.baseChange` proves preservation along every morphism of
base schemes. `IsFibrewiseAdjoint.of_baseChange` and
`isFibrewiseAdjoint_baseChange_iff` prove reflection and equivalence when that
morphism is surjective. These proofs use composition of actual base changes
and the field-valued comparison; surjectivity supplies a point above each
point for reflection. Flatness is unnecessary for these fibrewise assertions.

The motivation is Brian Conrad, *Reductive group schemes* (2014), Remark
6.4.5 and the proof of Proposition 6.4.4, pp.232–233, registered as
`conrad-2014-reductive-group-schemes`: the argument passes to étale charts
and compares geometric fibres. These lemmas are internal compositions of
published Library results, rather than separately quoted assertions from
that source. They do not construct the finite étale algebra, simple factors,
or a Weil-restriction isomorphism.
