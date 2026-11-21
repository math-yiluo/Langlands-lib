# Smooth test integration along a product fiber

Let \(U\) and \(V\) be open subsets of real normed spaces. Integrating a smooth test on \(U\times V\) in its second variable against a locally finite Borel measure gives a smooth compactly supported test on \(U\). Its support is contained in the projection of the original support. All iterated derivatives in the first variable pass under the integral.

The integral is Mathlib's Bochner integral. It gives ordinary integration for a Banach target space and returns zero for every test taking values in an incomplete target space.

The projection of the original compact support to the integration variable gives a common compact integration domain. The joint smooth test defines a smooth family of continuous functions on that compact set. Integration and point evaluation there are continuous linear maps, which gives the derivative identity.

A normalized smooth bump gives a nonnegative test of integral one in any neighborhood of a point of a finite-dimensional real space for a locally finite measure positive on nonempty open sets. These constructions are used in local orbit integration and distribution descent.
