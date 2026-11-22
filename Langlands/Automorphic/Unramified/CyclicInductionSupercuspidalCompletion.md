# Unique-place supercuspidality from the generic sigma-lift fibre

`CyclicInductionSupercuspidalCompletionStatement` derives the local supercuspidality criterion at the actual finite completions from `CuspidalSigmaLiftExistenceStatement` and `SigmaLiftGenericFibreStatement`. The downstairs and upstairs actions are related by the local cyclic induction characterization in Henniart (2012), Theorem 6, printed p. 7. The upstairs action is supercuspidal and has trivial Galois stabilizer. The conclusion is supercuspidality of the downstairs action in the sense of the admissibility and Jacquet-vanishing predicate.

`isSupercuspidal_of_generic_orbitProductLift_at_completion` applies `exists_commonSigmaLift_of_orbitProductLift_at_completion` to the normalized orbit lift of a generic downstairs action. Cuspidal sigma-lift existence gives a supercuspidal, essentially square-integrable witness at the original matrix rank with the same irreducible sigma-lift as the downstairs action. The generic fibre theorem uses the downstairs action's Whittaker genericity to identify it with a norm-trivial determinant twist of the witness. Such a twist has open kernel and preserves supercuspidality.

`cyclicLocalInductionSupercuspidalAtCompletion_of_genericFibre` obtains the upper action's irreducibility, the lower action's Whittaker datum and the orbit lift from the cyclic local induction conditions, then applies this implication.

`cyclicWeakInductionSupercuspidal_of_completionFibre` plugs the local implication into `cyclicWeakInductionSupercuspidal_of_matching_at_completion`. The global theorem also assumes strong matching at the unique place and cuspidal Euler constituent recovery. The totally complex theorem specializes this implication. Both global implications carry the four independent universes of their target propositions.

The construction is a derived route to the local step of Henniart–Herb (1995), Proposition 5.5, printed pp. 152–153. The cuspidal existence and generic fibre premises come from Henniart–Lemaire (2011), II.4.12 Remarque, printed p. 97, and II.4.8 Lemme (2), printed pp. 90–91.
