# An ordinary normalized test detecting the conjugate equal-rank residues

`HasNormalizedConjugateResidueTest` asks for a nonzero cuspidal vector and its actual conjugate, spherical outside the retained set, and an adelic Schwartz–Bruhat test standard there with both the test and its Fourier transform nonzero at zero. It also asks for an entire normalization of the ordinary partial integral of that pair and test with respect to the prescribed factors.

`exists_normalizedConjugateResidueTest_of_local` gives this data for two presentations of the actual conjugate pair with irreducible admissible finite components, the finite Euler factor choice and the specified real and complex parameters. The original cuspidal realization is trivial on the split centre. The nontrivial unitary adelic additive character is trivial on the diagonal number field. The supplied slice comparisons give the specified model ranges for the two opposite characters. The theorem assumes ordinary local continuation in those models. The finite set can be chosen to contain any starting finite set. Choose a nonzero cuspidal vector and enlarge the finite set so the vector and its conjugate both belong to the spans of pure vectors of their supplied presentations. Use the product Schwartz test with nonzero origin values, converting its finite tests to the canonical local topology. The pure-pair formula and span extension then give the indicated normalization of the actual conjugate vector pair. The residue positivity input is available separately in `SelfPairResidue`.

This internal derivation supplies the test data for the pole argument in J. W. Cogdell, *Analytic Theory of L-Functions for GL(n)*, chapter 9 of Bernstein and Gelbart, eds., *An Introduction to the Langlands Program*, Birkhäuser, 2004, Theorem 4.1, printed pp. 218–221.

`exists_normalizedConjugateResidueTest_of_local_at` requires ordinary equal-rank
continuation for the given rank. The all-rank version applies this result to
the given rank's continuation clauses. Both versions use the same normalized
pure-span argument.

`exists_normalizedConjugateResidueTest_placewise` uses the real continuation for an actual real place and therefore also applies on totally complex fields with complex continuation alone.
