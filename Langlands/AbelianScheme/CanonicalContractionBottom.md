# Bottom-degree creation and multiplication-slant contraction

Let \(A\) be an abelian variety over an arbitrary field \(K\). This internal
extension of `CanonicalCreationContraction` defines `unitClass A` in actual
\(H^0(A,\mathcal O_A)\), represented by the constant unit cocycle on the fixed
finite affine cover. `creation_unitClass` proves
\(c_x(1)=x\) for every actual \(x\in H^1(A,\mathcal O_A)\).

The two bottom slant formulas evaluate a first-projection pullback as
\(\ell(x)\,1\), and kill a second-projection pullback. They specialize
`AllSeq.slantByH1Dual_bottom_pull_left` and
`AllSeq.slantByH1Dual_bottom_pull_right` on the simple product cover.
The published \(H^1\) primitivity identity
`pullStructure_mul` then gives `contraction_zero`:
\[
d_\ell(x)=\ell(x)\,1.
\]
Linearity and creation on the unit give `creation_contraction_bottom`:
\[
c_x(d_\ell(y))=\ell(y)x.
\]
These identities hold in every characteristic and for the actual cohomology
maps previously defined, using their fixed cocycle retraction and covers.

The provenance is internal specialization of the generic bottom-degree
representative calculation and the existing canonical multiplication
pullback. This unit does not prove the general creation-contraction relation,
exterior generation, or the host exterior/coproduct comparison.
