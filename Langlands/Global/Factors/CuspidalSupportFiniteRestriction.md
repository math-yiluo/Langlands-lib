# Finite-place restriction in cuspidal support

`Langlands.Global.finiteLocalNormalizedInduced hm P v` is the actual normalized
block induction at `v` appearing in `IsFiniteInducedConstituent`. Its coefficients
are the tensor of the local block components of the supplied spectral presentations.
The Library proves admissibility and finite length for this induction from the
irreducibility and admissibility of each block.

Suppose a smooth finite adelic representation has the given finite action of `Q`
as a subquotient. Assume that at each place its restriction has separating
intertwiners to `finiteLocalNormalizedInduced`. Restrict the actual numerator and
quotient map to the local group. The inclusion of the numerator lets the same
intertwiners separate its vectors. The finite-length extraction lemma gives a simple
subrepresentation of the local restriction of `Q` that is a subquotient of the local
induction. Admissibility passes to this carrier by the subrepresentation and
quotient results for smooth representations. The equality of the completion and
canonical p-adic matrix topologies gives the required correspondence object.

Choose one nonzero vector of `Q` and an open subgroup of the finite adelic group
fixing it. Under the restricted product description, the preimage of this subgroup
in the product of all the local integral subgroups is a neighborhood of the identity.
A basic product neighborhood restricts finitely many coordinates. It therefore
contains each embedded local integral subgroup outside that finite set. At those
places the chosen vector is fixed by the local spherical subgroup. Averaging over
that subgroup and joint irreducibility for the local action and its commuting
operators imply that every nonzero local subrepresentation of `Q` also has a
nonzero spherical fixed vector. This applies to the extracted constituent.

This is a finite-place argument derived from Langlands's constituent and
almost-everywhere spherical conclusions in Lemma 1 of *On the notion of an
automorphic representation*, Corvallis Part I (1979), printed p. 203 (PDF p. 198),
source `langlands-1979-notion-automorphic-representation`. It uses that lemma's
finite-length input at each place and proves fixed vectors directly from the finite
adelic topology and the concrete action on `Q`.
