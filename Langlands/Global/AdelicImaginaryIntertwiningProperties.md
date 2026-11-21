# Inner products and composition for imaginary intertwining operators

The theorems in `Langlands.Global.AdelicImaginaryIntertwiningProperties` concern supplied bounded maps satisfying `IsImaginaryIntertwiningOperator`. They work with independently presented parabolics and the actual restriction spaces `inducedHilbertSpace` in `AdelicSpectralTransformSpaces`. They do not construct the meromorphic continuation or discharge any of the named premises below.

## Evaluation and inner products

`Langlands.Global.map_eq_sum_smul_toLp_of_isImaginaryIntertwiningOperator` turns the almost-everywhere evaluation property into an equality of `Lp` classes. For a qualifying finite expansion \(M(w,\lambda)v=\sum_q a_q(\lambda)\psi_q\) on the sufficiently regular region, with coefficient domains containing the imaginary slice and with square-integrable restriction classes for the \(\psi_q\), it gives
\[
  \mathrm{Mop}(x)[v]=\sum_q a_q(i e(x))[\psi_q]
\]
viewed in the target restriction `Lp`. This uses the existing sum-of-classes lemma and `Lp.ext`; it does not evaluate the defining integral at an imaginary parameter.

`Langlands.Global.inner_map_map_of_isImaginaryIntertwiningOperator` proves preservation of inner products on the full source Hilbert space, not surjectivity. It takes `IntertwiningImaginaryUnitarityStatement`, `InducedRestrictionMemLpStatement`, and `IntertwiningSquareIntegrableExpansionStatement` as premises, with the geometric, measure, and coordinate data of the pair. For each pair of inducing forms, `inner_eq_of_expansions` concatenates their expanding families and pads the coefficients with zeros so that the Gram statement applies to both at once. It uses a common coefficient domain containing the imaginary axis. The target coordinates and weighting function are transported to the ones required by that statement without changing the target inner product, using the assumed measure preservation. The agreement clause of the Gram statement transfers the resulting identity to the original expansions at \(i e(x)\), and the induced-inner-product comparison identifies it with the `Lp` inner products of the restriction classes. The classes of the inducing forms have dense span by the definition of `inducedHilbertSpace`; continuity extends the identity to arbitrary pairs.

## Composition on classes of inducing forms

`Langlands.Global.map_comp_of_isImaginaryIntertwiningOperator` considers Weyl conjugations \(s:P\to P'\), \(r:P'\to P''\), and \(u:P\to P''\) whose parameter map equals the composite \(rs\). It proves
\[
  \mathrm{Mop}_u(x)[v]=\mathrm{Mop}_r\big(e'^{-1}(s(e(x)))\big)\big(\mathrm{Mop}_s(x)[v]\big)
\]
for the class of any square-integrable inducing form \(v\). Here \(s\) in the expression for the coordinate means its real parameter map. The Lean conclusion is the equality on these classes, not an operator equality for every vector.

The proof expands \(M(s,\lambda)v\) and then expands \(M(r,\mu)\psi_q\) for each term. `exists_uniform_expansions` pads the latter expansions to a common length with a common domain; `exists_flat_expansions` places their target vectors in one family indexed by `Fin (ms * m)` using zero coefficients off the corresponding block. It obtains a third expansion for \(M(u,\lambda)v\) and uses `IntertwiningRepresentativeIndependenceStatement` to make that expansion one for the product of the chosen rational representatives on the regular region. Now `IntertwiningCocycleStatement.{0}` applies to the continued expressions at \(\lambda=i e(x)\): `weylParameter_imaginaryParameter` identifies the intermediate parameter as \(i e'(e'^{-1}(s(e(x))))\). `InducedRestrictionMemLpStatement` gives the needed restriction classes, and the evaluation lemma and linearity give the claimed equality.

## Provenance

These are derived interfaces for the finite-family density argument. Arthur, *An introduction to the trace formula* (2005), §7, Theorem 7.2(a), (7.4), p. 35 (PDF p. 47 of the registered proceedings), uses the unitary extensions of the intertwining operators and their compatibility in the spectral families. Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), Theorem 2.3(5), p. 191 (PDF p. 5 of the journal article), supplies the source of the product identity formalized as the separate cocycle premise. The Lean theorems pass from the named Gram and cocycle statements to properties of the supplied bounded maps; they are neither unconditional statements of source unitarity nor proofs of the original product formula.
