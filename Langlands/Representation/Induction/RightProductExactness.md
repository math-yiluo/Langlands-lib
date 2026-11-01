# Actual right-product exactness

This internal unit constructs maps between actual normalized two-factor
products and proves that a short exact sequence in the first factor remains
short exact after taking the product with a fixed right factor. The positive
ranks may differ. The field, supplied topological data, and carrier universe
remain independent.

For actual smooth objects \(S,P,Q\) of \(\mathrm{GL}_a(F)\), an injection
\(i:S\to P\), and a surjection \(q:P\to Q\) with
\(\operatorname{range} i=\ker q\), the theorem
`rightProductMap_shortExact` proves injectivity, equality of range and
kernel, and surjectivity for the corresponding actual maps
\[
 S\times C\longrightarrow P\times C\longrightarrow Q\times C
\]
on the literal two-block shape \((a,b)\), where \(C\) is any supplied smooth
object of \(\mathrm{GL}_b(F)\). It imposes no irreducibility or admissibility
hypothesis.

`rightTensorMap` is the external tensor map of the first-factor intertwiner
and the identity of \(C\). `rightTensorSplit` identifies the indexed tensor
carrier with the ordinary binary tensor. The proof of
`rightTensorMap_split` checks the equality of linear maps on pure tensors,
so the external map is literally the usual right tensor map after splitting.
Flatness over \(\mathbb C\) preserves injectivity. Tensor right exactness
supplies surjectivity and equality of range and kernel, transported through
the splitting equivalences.

`rightProductMap` applies the supplied normalized parabolic induction map
to that external tensor map. The final theorem applies the existing actual
`normalizedInductionExactness` to the three smooth tensor objects and the
three tensor exactness conclusions. Thus its maps use the same parabolic,
half-modulus normalization, and topology as the supplied \(T\).

This is derived infrastructure for the local repeated-factor triple task.
Its provenance is elementary tensor exactness and the existing actual
normalized-induction exactness proof. It does not prove product
irreducibility, construct a proper subrepresentation of a linked product,
or assert either local triple transfer.
