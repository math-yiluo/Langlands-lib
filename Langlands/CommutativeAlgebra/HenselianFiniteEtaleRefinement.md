# Conditional construction of a finite étale local refinement

`HenselianFiniteEtaleRefinement.exists_local_finite_etale_refinement` is an internal derived lemma. It assumes `FiniteLocalHenselianStatement` in the common carrier universe and constructs a finite étale local target algebra for an étale algebra with a prime above the base's maximal ideal. It does not yet prove the unconditional refinement statement.

For the chosen prime `q`, its residue field `K` is finite over the residue field of the base because the original map is étale. Thus `K` is finite over the base ring, and it is formally unramified by localization and quotient. The published `CompleteLocal.exists_etaleCover` supplies a local finite étale algebra `L` surjecting onto `K`. The supplied inheritance result makes `L` Henselian. After tensor base change to `L`, the `K` point lifts to an `L` section by `HenselianSections.exists_lift_of_etale`. Restriction to the original algebra is the required algebra map.

All mathematical inputs in this construction are named imported Library or Mathlib theorems, apart from the explicit Henselian inheritance premise. The construction is a derived proof route to the scheme statement from Stacks Project Tags 04GG and 04GH; it does not use the finite-part decomposition described in that statement's source commentary.

`RefinementData R A` packages a carrier ring in the same arbitrary universe, its local-ring and `R`-algebra structures, proofs of étaleness and module finiteness, and the actual `R`-algebra map from `A`. `refinementOfPrime` chooses these data from the implemented existence proof. This is a data-construction definition with an explicit inheritance argument, not an unconditional proof of `HenselianFiniteEtaleRefinementStatement`.
