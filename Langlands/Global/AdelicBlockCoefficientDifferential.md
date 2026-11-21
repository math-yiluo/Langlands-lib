# Differentiation of realized adelic Levi coefficients

`coefficientDifferential` acts on the realized scalar coefficient space. It projects a mixed archimedean matrix direction to each diagonal block, applies the corresponding real Lie generator in one tensor slot at a time, and sums those actions. The map `coefficientEquiv` transports the result from the tensor of the actual operator realizations to the scalar coefficients.

Fix an adelic Levi point. Left multiplication by its infinite block diagonal matrix and evaluation of `coefficientExtension` at its finite component give an ambient function of a mixed matrix. At an infinite parabolic matrix this agrees with evaluation of the coefficient at the original Levi point right translated by the projected parabolic element. The comparison uses the multiplicativity of the actual Levi projection.

`coefficientExtension_hasDerivAt` differentiates this function along a real parameter curve whose value at zero is the identity. On pure tensors, each diagonal block depends linearly on the mixed matrix. Its derivative after the fixed left multiplication is the pointwise direction that defines the actual smooth Lie action on the block realization. The product rule gives the sum of the evaluations with one block differentiated in each term. Linearity extends this calculation to the full realized coefficient space.

Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), describe the adelic induced sections and their scalar Levi slices. Langlands (1979), proof of Proposition 2, pp. 204–205 (PDF 199–200), uses smooth compact-finite sections with cuspidal Levi slices. The derivative formula here is derived internally from the Library's matrix-coordinate derivatives and realized coefficient evaluation.
