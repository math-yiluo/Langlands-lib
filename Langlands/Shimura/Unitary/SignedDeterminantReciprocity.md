# Parity of the finite signed determinant defects

Let \(A\) be a central simple algebra of even degree \(n>1\) with unitary involution over a totally complex quadratic extension \(K/E\) of a totally real number field. Suppose its upper completed Brauer invariants vanish over all finite places outside a specified finite support \(s\). The field universes are independent. `evenSignedDeterminantDefectSet` uses the compatible profile residues and real positive dimensions together with a supplied global cohomological Brauer class over \(E\). The class is assumed to have the following local invariants.

- At a place of \(s\) the invariant is \((n/2)a_p/n\) modulo the integers.
- At every split place outside \(s\) the invariant vanishes.
- At a nonsplit place outside \(s\) the invariant is zero if the signed Gram determinant is a norm from the actual upper completion, and is \(1/2\) otherwise.
- At a real place with associated embedding \(\tau\), the invariant is the half-class of \(n/2+n-r_\tau\).

Brauer reciprocity gives finite support and a total invariant sum of zero. Removing \(s\) from the finite support gives exactly the nonsplit places outside \(s\) with nonnorm signed determinants. The map from \(\mathbb Z/2\mathbb Z\) to \(\mathbb Q/\mathbb Z\) sending \(1\) to \(1/2\) identifies the sum over \(s\) with the sum of the residues reduced modulo two. Using the real-place indexing by embeddings, compatibility cancels that sum with the real contributions. The residual sum is half the cardinality of the defect set in \(\mathbb Q/\mathbb Z\), so the set has even cardinality.
