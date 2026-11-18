# The sufficient implication in Nagata’s theorem

This proof establishes `NagataLinearlyReductiveSufficiencyStatement` in every universe. Its hypotheses and conclusion are exactly those in the paired reduction statement: an affine group scheme locally of finite type over a field of nonzero characteristic, a supplied open multiplicative-type identity component, and geometric component cardinal not divisible by the characteristic. Smoothness and reducedness are unnecessary.

First compare the supplied identity-component inclusion with the canonical locally finite-type identity component. Both are open immersions with the same range. Lifting each inclusion through the other gives mutually inverse group-scheme homomorphisms. Transport multiplicative type along this actual isomorphism.

Over an algebraically closed field, every representation of the canonical multiplicative-type identity component is semisimple. Thus each ambient stable subspace admits an actual identity-component-equivariant projection. The rational component quotient is finite, and its cardinal is invertible by the prime-to-characteristic assumption. Component averaging upgrades the supplied projection to an actual ambient-equivariant projection. Its stable kernel is a complement, so the stable-complement characterization proves the exact sum-of-simple-stable-subspaces semisimplicity condition.

For the arbitrary original field, extend to its algebraic closure. Formation of the canonical identity component commutes with this extension, and multiplicative type is preserved. The geometric component cardinal is exactly the rational component quotient cardinal after this extension. The preceding argument gives semisimplicity of the extended representation. Descent of semisimplicity along a field extension gives semisimplicity of the original representation. The descent theorem applies a normalized original-field linear functional to an extended projection matrix, so it neither assumes linear-reductivity ascent nor uses the necessary implication of Nagata’s theorem.

This is an internal derived proof of the sufficient implication, following the extension of Maschke’s theorem in Milne (2022 corrected reprint), Exercise 4-3, printed p.97 / PDF p.108, together with the exact invariant-complement criterion of Proposition 4.17, printed p.90 / PDF p.101. The full official errata snapshot has no correction to these passages. All stability and equivariance are tested on arbitrary affine algebras; finite non-smooth multiplicative-type groups are retained.


The identity-component and component-order necessity implications, and hence the full Nagata theorem, remain separate proof obligations.
