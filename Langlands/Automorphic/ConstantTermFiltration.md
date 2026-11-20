# Cyclic quotients and a finite filtration by kernels

`laterTermKernel c n` is the intersection of the kernels of the maps in the
finite ordered family `c` at indices at least `n`.

`exists_cyclic_term_quotient` isolates the cyclic quotient argument in
Langlands (1979), printed p. 204, final paragraph (Corvallis Part I, PDF
p. 199). The registered source is `langlands-1979-notion-automorphic-representation`,
SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The derived version uses a family of linear maps with trivial joint kernel.
For all standard block constant terms, separation of vectors is supplied by
including the term for the whole group.

The proof takes the least cutoff whose common kernel has a vector mapping
nontrivially to the given simple quotient. The cutoff is positive by separation.
At the immediately preceding index, a vector in the kernel of that map within
the selected cyclic module belongs to the earlier common kernel. Minimality
makes its image in the simple quotient zero. The quotient map therefore
descends to the cyclic image of the term and is surjective by simplicity. The
selected cyclic source is killed by every later term. In the constant-term
application, an ordering with strict refinements later and transitivity of
constant terms give the vanishing conditions on Levi slices.
