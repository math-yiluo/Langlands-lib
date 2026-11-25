# Reductive coefficient extensions from actual reductivity descent

This internal derived module specializes the published
`isReductive_baseChange_iff_eventually` theorem to the directed system of
finitely generated coefficient subalgebras. It uses the actual reductivity
descent proof, so no `DirectLimitReductiveStatement` premise remains.

`SimultaneousHomModel.exists_reductive_extension_of_isReductive` starts with a
simultaneous model whose recovered source is reductive. All finitely generated
subalgebras form a directed system covering the supplied algebra: adjoining a
singleton includes any given element. The published coefficient-colimit
construction identifies its ring colimit with that algebra. The model's
source recovery isomorphism transfers reductivity to its colimit base change.
The published whole-group reductivity equivalence then gives a finite stage
above the original coefficients where the source is reductive. Its actual
inclusion base change is exactly `SimultaneousHomModel.enlargeTo`.

`SimultaneousHomModel.reductiveExtension` chooses an actual simultaneous model
with reductive source over a finite coefficient enlargement. A private existence
lemma constructs such a model by `enlargeTo` and records preservation of monicity
as an implication, so the construction does not require the starting map to be
monic. The public `reductiveExtension_spec` proves coefficient containment,
source reductivity and this monicity implication for the chosen model. Its
`sourceIso`, `targetIso` and `comm` fields recover the same specified original
homomorphism. No canonical choice or uniqueness is asserted.

`SimultaneousHomModel.exists_reductive_mono_extension_of_isReductive` also
retains scheme monicity by taking this chosen model and applying its
specifications. The underlying construction uses preservation under base change. All other
model fields, including target separatedness and finite presentation and the
exact recovery square, remain those supplied by `enlargeTo`.

`exists_reductiveMonoModel_of_monomorphism_descent` uses the published
`homGeneral` proof to obtain a simultaneous model containing any prescribed
finite set. Its one explicit premise is scheme monicity descent: that premise
gives a finite enlargement where the supplied homomorphism is monic. The
preceding unconditional reductivity extension gives a further model with
reductive source and monic homomorphism. Both enlargements retain the prescribed
coefficients. The target is separated and finitely presented.

This is a specialization and composition of the published coefficient-model,
homomorphism-descent and direct-limit reductivity constructions; it asserts no
new literature result. It proves neither scheme monicity descent nor a
closed-immersion conclusion. Semisimple-locus openness is not used.
