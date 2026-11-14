# Integral simple-gradient generation after deleting an affine node

The internal predicate `IsIntegralSimpleDerivativeDeletion Ψ C δ` states
that the gradients of all simple affine roots of `C` except `δ` are
linearly independent over the reals and have the same integer span as
the full derivative root set. All full derivative roots, including
multipliable roots, occur in this span equality.

For a rank-zero-compatible affine root system and a regular chamber,
the main result assumes affine-root irreducibility, vertex transitivity
of the actual chamber Cartan matrix, and integral generation of the full
derivative set by the simple affine gradients. It proves the predicate
for every choice of deleted simple affine root. A corollary replaces
integral generation by the imported indivisible-lift premise.

The proof first proves positive definiteness of the full coroot form.
Vanishing of its sum of squares makes a functional vanish on every
coroot, and the full derivative root pairing's coroot spanning theorem
then makes the functional zero. A left-kernel vector of the chamber
matrix therefore gives a zero combination of gradients: the
reflection identity makes that combination orthogonal to each simple
gradient, hence to itself. Matrix vertex transitivity and the positive
integral marks give zero column sums, using the imported matrix
theorem. Thus the sum of all simple gradients is zero.

This last relation expresses the deleted gradient as the negative sum
of the remaining gradients, so deletion preserves their integer
lattice. Irreducibility gives linear independence of the simple
affine functionals. The imported linear-algebra deletion theorem,
applied to the relation with all coefficients one, then gives real
linear independence of the remaining gradients. The assumed full
integral generation gives the other containment in the lattice
equality.

This is derived infrastructure from the imported form, Cartan, marks,
irreducibility, linear-independence and integral-generation results;
it is not a transcription of a literature assertion. It uses independent
universes for the translation space and affine torsor and imposes no
field or characteristic hypotheses. It does not yet prove that these
remaining gradients are a root base, compare an absolute Cartan
matrix, or supply the actual-group irreducibility, matrix transitivity
or indivisible-lift hypotheses.
