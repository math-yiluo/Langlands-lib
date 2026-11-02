# The Serre criterion for Noetherian affine étale equivalence relations

Authors: Worker 101, Worker 1203, Worker 424, Worker 122 and Worker 239.

The theorem has exactly the published proposition `EtaleEquivalenceRelationSerreCriterionStatement.{u}` as its type, for an arbitrary universe u. It adds no hypotheses and uses the published scheme relation, coaction, acyclicity and affine quotient predicates unchanged.

The proof applies `serreCriterion_of_ringForm_of_nonzeroInvariant` to two unconditional inputs: `etaleEquivalenceRelationRingForm`, the ring form of an affine closed étale equivalence relation, and `groupoidCoactionNonzeroInvariant`, which proves that acyclicity of all coactions implies a nonzero invariant in every nontrivial coaction over a Noetherian ring. Both rings and all modules tested by acyclicity remain in the same arbitrary universe `u`.

The nonzero invariant theorem reduces an arbitrary module to a finite subcoaction containing a chosen nonzero element. Its closed support contains a finite invariant closed orbit; the corresponding vanishing ideal gives a nontrivial quotient module over an Artinian quotient ring. The actual quotient relation and quotient coaction satisfy the original identities. Étaleness over the Artinian object ring gives finite projectivity through both projections, so the finite locally free invariant-ring presentation and flat tensor descent produce a nonzero quotient invariant. Acyclicity lifts that invariant back to the original module. Thus this input adds no finite generation or finite length hypothesis.

The reduction first forms the actual equalizer invariant ring. Acyclicity gives exactness of the invariant functor, and the nonzero invariant theorem makes that functor detect zero modules. The invariant unit and counit constructions then provide the requisite equivalences. Applied to the relation coaction, they identify the tensor square over the invariant ring with the relation ring and establish faithful flatness of the original ring over the invariant ring. The resulting certificate yields the spectrum of the invariant ring as an affine quotient, with the required flat, locally finitely presented and surjective map and the source/target pullback square.

The final assembly uses the invariant ring proof route. It assumes no affine descent conclusion and changes no pair in the published target's import closure. Its mathematical provenance is the published statement and the internally derived constructions named in its imports.
