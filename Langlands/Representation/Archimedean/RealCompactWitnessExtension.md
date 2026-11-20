# Extending a compact coefficient model into a real standard module

For a finite-dimensional complex representation of `O(n)`,
`IsStandardFunctional` requires the left sign character and the block Fourier
cutoff dictated by the real blocks. Fix a qualifying form `ℓ` with continuous
coefficients. The translates of `k ↦ ℓ(ρ(k)x)` lie in the image of
`coefficientMap`, so their span is finite-dimensional. The published
`PrincipalSeriesExtension` constructs a smooth, compact-finite extension, and
`RealKTypeTransport.mem_realStandardModule_of_unitaryCompact` puts it in the
standard module. The Fourier condition at any compact element `k` follows
by applying the condition at the identity to `ρ(k)x`.

The extensions define a linear intertwiner `A`, as one verifies on the compact
subgroup, where restriction is injective. For any compact-equivariant
endomorphism `E` of the standard module, evaluation at the identity after
`E ∘ A` again satisfies the sign and Fourier conditions. If every qualifying
form is a scalar multiple of `ℓ`, the equality at the identity extends by
equivariance to the compact subgroup and then to the full functions. A vector
where `ℓ` is nonzero therefore yields a nonzero standard module vector scaled
by every such endomorphism.

`compactIntertwiner_ext` also gives this extension of equality for arbitrary
compact intertwiners from the same source representation.

This is an internal compact-model argument for the multiplicity step in the
archimedean cuspidal irreducibility proof. It follows directly from the
Library's definitions of the principal series and real standard module in
`StandardModule` and the published extension and restriction results above.
