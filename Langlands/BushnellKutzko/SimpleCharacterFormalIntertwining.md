# Formal intertwining of the dual H lattice coset

`simpleCharacterIntertwiningSubgroup` joins the mixed adjoint congruence group and cutoff J. The product description and fractional shift identify its carrier with the factor in `SimpleCharacterIntertwiningStatement`. The dual H layer is stable under the cutoff J lattice by the two-sided ideal property and cyclicity of trace, and contains its adjoint image by the dual formula.

The positive cutoff J group preserves the large coset. A finite sequence of conjugations raises the depth of each error until it lies in the filtration step of the ordinary stratum coset. Applied to both representatives, this gives the sandwich in `simpleCharacter_formalIntertwining_eq_sandwich`. The ordinary intertwining theorem and the outer subgroup product then give the double coset in `simpleCharacter_formalIntertwining_eq_doubleCoset`.

For a unit satisfying the covariance identity on the character overlap, `simpleCharacter_intertwining_iff_formal_of_ratio` equates character self-intertwining with formal intertwining of the parameter coset modulo the dual H lattice. The covariance identity expresses character self-intertwining as triviality of the trace ratio on the overlap. The dual-of-intersection formula identifies that triviality condition with formal intertwining.

This implements BK93 (3.3.5)–(3.3.13), printed pp. 107–110, using (1.5.8), printed p. 44, and the dual formula (3.1.19), printed pp. 96–97.
