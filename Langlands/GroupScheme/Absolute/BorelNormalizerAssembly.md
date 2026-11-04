# Assembly of the Borel normalizer induction

This internal construction combines the existing normalizer branches. It does
not prove the unconditional `BorelNormalizerStatement`: the torus endomorphism
dichotomy, centralizer intersection, parabolic quotient properness, rational
unipotent-times-torus factorization, and solvable maximal-torus conjugacy
statements are explicit arguments.

`borelNormalizer_of_structuralInputs` returns the exact original normalizer
statement from those five inputs, at arbitrary universe `u`. It uses strong
induction on the Lie dimension of smooth connected affine group schemes. For
each Borel, it chooses a maximal torus of the Borel itself using the existing
height construction. Solvable maximal-torus conjugacy corrects a normalizing
point by left multiplication by a Borel point, so the corrected point also
normalizes this torus.

The torus commutator endomorphism has the actual commutator formula. In its
scheme-surjective branch, rational factorization supplies the unipotent and
torus factors required by the published smooth surjective branch. That branch
constructs the quotients, uses the explicit properness input, and proves that
the Borel inclusion is an isomorphism.

Otherwise the dichotomy supplies a closed copy of `Gm` killed by the commutator.
Its composite into the ambient group is again closed and factors through the
Borel. If this composite is central, the smooth central quotient branch applies
the induction hypothesis to its smaller quotient. If it is noncentral, the
canonical smooth connected proper centralizer branch applies the same induction
hypothesis, using the exact centralizer-intersection input. This proves
membership of the corrected point; the existing torus correction lemma then
recovers membership of the original point.

`borelPointOfStructuralInputs` uses the resulting normalizer equality to choose
an actual rational Borel point with its prescribed ambient image. Its subtype
retains the image equality.

The provenance is the composition of the imported constructions, with no new
literature claim. All geometric inputs remain explicit, so this module supplies
an assembly and a point-selection interface while the unconditional host
theorem remains open.
