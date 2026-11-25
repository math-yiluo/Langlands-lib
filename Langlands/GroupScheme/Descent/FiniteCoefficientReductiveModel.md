# Reductive monomorphisms over finite coefficient rings

This is an internal conditional construction using the Library's
simultaneous `SimultaneousHomModel`, its direct and iterated pullback comparisons, and the
explicit proposition `DirectLimitReductiveStatement`.

`SimultaneousHomModel.enlargeTo` pulls both groups and the homomorphism along an inclusion
of the coefficient subalgebra into a larger finitely generated subalgebra.
The original recovery square is preserved by naturality of pullback comparison.
`SimultaneousHomModel.enlargeTo_mono` uses preservation of monomorphisms by scheme base change.

The coefficient diagram consists of all finitely generated subalgebras, ordered
by inclusion. It is directed under sums of subalgebras, and singleton adjunction
shows that it covers the supplied algebra. The published subalgebra colimit
construction makes the supplied algebra its colimit.

`SimultaneousHomModel.exists_reductive_extension` starts that diagram at the original
model's coefficient algebra. The recovery isomorphism makes the source after
base change reductive. Clause 2 of the explicit direct-limit premise gives an
eventually reductive stage. Evaluating at that stage yields a reductive model
retaining all the original coefficients.

`SimultaneousHomModel.exists_reductive_mono_extension` also retains monicity by base change.

`exists_reductiveMonoModel` combines this construction with simultaneous
homomorphism descent and scheme monicity descent. All three propositions are
explicit premises. It first finds a model containing a prescribed finite set,
enlarges until its homomorphism is monic, then enlarges again until its source
is reductive. Both enlargements retain the finite set. The target is separated
and finitely presented and is not required to be affine.

These results leave the descent and direct-limit premises explicit and prove
no closed-immersion conclusion.
