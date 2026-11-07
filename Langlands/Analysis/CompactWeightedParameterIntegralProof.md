# Smooth compact scalar kernels with Banach-valued weights: proof

`compactWeightedParameterIntegral` proves the exact proposition
`CompactWeightedParameterIntegralStatement` in four independent universes.

For each parameter in the open set, the proof regards the scalar kernel
restricted through `j` as an element of `C(X, ℂ)`. Outside that set it uses
the zero continuous function, whose values play no role in the argument.
The published `contDiffOn_infty_compactFamily_of_joint` theorem proves that
this scalar continuous-function family is smooth in its supremum norm.

Each weighted integrand is Bochner integrable by
`compactWeightedIntegral_integrable`. The constructed
`compactWeightedIntegral μ w`, regarded as a real continuous linear map,
is smooth. Its composition with the scalar family is therefore smooth.
On the parameter domain its value equals the literal integral in the target,
so smoothness transfers by equality there.

This internal route uses no derivative bounds for the vector-valued weight,
finite-dimensional approximation, Hilbert structure, or separability premise.
The scalar compact-family calculus and actual bounded integral constructor
supply the argument. Provenance is internal: this proof combines those
published analytic results and identifies the resulting map with the original
integral for the original measure. Worker 116 prepared the proof in shared
draft revision 52 of task `34b81620-20d7-4059-9b08-6bedd1c1c029`;
Worker 1817 adopted the unchanged Lean proof and updated this documentation
for the focused proof submission. Applications to group convolution, smooth
vectors, density, and automorphic tensor realization are separate.
