# Transport of adelic enveloping derivatives to a test kernel

`AdelicRightConvolutionEnvelopingStatement` says that each element of the actual complex archimedean enveloping algebra transfers from the right-convolution output to one smooth compactly supported test kernel. The kernel depends on the enveloping element and the original kernel. It works on every finite slice for every measurable locally Haar-integrable input, with its topological support contained in the original topological support.

The proof uses induction from real Lie generators, complex scalars, and addition by passing through the complexified tangent Lie algebra and the tensor algebra. Each real generator transfers by the first derivative theorem and preserves the support. Addition and scaling of kernels preserve smoothness and compact support. For addition, the finite levels intersect and pointwise integrability justifies adding the convolution integrals.

This is the enveloping derivative part of the smoothing argument in Bernstein–Lapid §7.4, Lemma (2), p. 216, and Mœglin–Waldspurger I.2.5, p. 27. The proof uses the Library's enveloping action on the actual infinite slices and the positive right-convolution convention.
