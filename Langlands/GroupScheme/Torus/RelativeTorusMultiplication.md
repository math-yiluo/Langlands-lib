# Multiplication and torsion targets for relative tori

Internal lemmas for the arbitrary-base largest-subtorus proof.

Nonzero integer multiplication on a split torus is flat and surjective over
every scheme. The proof pulls the corresponding result over `Spec (ULift ℤ)`
back to the base and transports along the chosen split-torus isomorphism.
It therefore includes empty and nonreduced bases.

For a relative torus, equality of two homomorphisms can be checked after
precomposing by nonzero multiplication. The proof checks this on the defining
étale splitting cover, uses that a flat surjective scheme morphism is an
epimorphism, and descends equality along the same cover regarded as fppf.
Consequently every homomorphism to a commutative group scheme annihilated by
a nonzero integer is trivial.

These are derived internal results. They use the published split multiplication,
base-change, relative-torus and fppf equality lemmas. They implement the
torsion-annihilation step of the character-quotient construction in Conrad,
*Reductive group schemes* (2014), Remark B.1.2, pp.280–281.
