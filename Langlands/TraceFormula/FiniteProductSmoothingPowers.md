# Convolution powers on finite products

`FiniteProductSmoothingPowersStatement` concerns a finite family of locally
compact, second-countable Hausdorff groups, with Haar measure \(\mu_i\) on
each factor. A topological group isomorphism from \(A\) to their product
sends the supplied Haar measure \(m\) to \(\prod_i \mu_i\). For continuous
compactly supported tests \(f_i\), the \(k+1\)-fold convolution power of
the tensor pulled back to \(A\) is the pullback of the tensor of the
\(k+1\)-fold powers of the \(f_i\), with each power taken using its own
measure \(\mu_i\). The Lean index \(k=0\) denotes the original function.

`finiteProductSmoothingPowers` obtains continuity from the coordinate
projections and compact support from the finite product of the supports.
At the induction step, `convolutionIntegral_comp_continuousMulEquiv`
moves the convolution integral to the product. The finite product formula
for integrals then factors it into the coordinate convolutions. Applying
`positiveConvolutionPower_succ` at each coordinate gives the result.

This extends the product computation in `SplitSmoothingPowers` to a
family of possibly different groups and to any topological group
isomorphism with the stated measure normalization. Arthur–Clozel (1989),
Chapter 1, §4, pp. 43–44, use tensors of local tests at the infinite places
in the comparison leading to (4.6) and (4.7).
