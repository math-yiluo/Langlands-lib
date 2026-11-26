# Cofinite pair Euler comparison for two weak inductions

`WeakInductionOrbitPairEulerValuesStatement` uses the weak base-change identity to the full Galois orbit. It applies to two supplied cuspidal weak inductions and genuine presentations. At almost every finite base place the pair factor of the two inductions is the product, over every actual place above it and every element of the upper orbit, of the pair factors of the first source and the conjugates of the second source. The factors use the residue cardinality at their own place.

`galoisGeneratorEquiv` enumerates the automorphisms by powers of the given generator. `galoisOrbit_eq_of_conjugates` equates the multiset obtained from the supplied realizations with the full orbit multiset by this enumeration. Equal members occur as many times as the indexing family prescribes. The theorem then applies `weakInductionPairEulerValues`, using the weak base-change identity for the second induction. The field and presentation universes are independent.

This is the cofinite comparison in Henniart–Herb (1995), Lemma 8.13, printed p. 179, and §8.16, printed p. 180, from the numerical projection formula and the orbit identity. The registered source is `henniart-herb-1995-induction`, SHA-256 `5e753525048b08007d9605baa9019c8e792512887305ec2e39ae9c3bee6a963e`.
