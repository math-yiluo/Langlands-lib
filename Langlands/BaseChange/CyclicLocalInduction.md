# Local cyclic induction via base change and determinant twist

`IsCyclicLocalInductionOf σ d π τ` records the characterization in Guy Henniart, *Induction automorphe globale pour les corps de nombres*, Theorem 6, printed p. 7. The cyclic extension and its generator are supplied by consumers. The relation is on actual complex representations over the two local fields. Both actions are smooth and unitarizable and have Whittaker functionals as in `Whittaker.IsGeneric`, which includes irreducibility and admissibility.

Condition (ii) uses a continuous multiplicative character of the downstairs field with kernel equal to the norm image. The determinant pullback stabilizes the downstairs representation up to equivalence. The character can be any generator of the characters trivial on norms, since invariance under a generator is equivalent to invariance under the whole cyclic group.

`HasSigmaOrbitProductLift` expresses condition (i). The normalized parabolic induction `sigmaOrbitProduct` uses the tensor of all \(d\) conjugates of the upstairs representation, including their multiplicities. The ranks of the supplied representations are \(r+1\) and \(m+1\). A proof of \(r+1=d(m+1)\) supplies the matrix reindexing on the downstairs action. The relation then requires the Library's sigma-lift identity for that action and the orbit product, with an actual intertwiner and a nonzero scalar.

The relation is an interface for the field case of Theorem 6. The theorem's existence, uniqueness and identification with the Henniart–Herb lift are separate proof obligations.
