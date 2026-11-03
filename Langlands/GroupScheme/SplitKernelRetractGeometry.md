# Geometry of the kernel of a split homomorphism

This internal, derived module supports the actual triangular diagonal-kernel geometry theorem.
It constructs an underlying scheme retraction from a split diagonal-image factorization, without
assuming the splitting theorem. It also proves the affine geometry facts used by that retraction.
No smoothness or connectedness assertion for arbitrary unsplit kernels is made.

For affine schemes over a noetherian commutative ring, an affine retract of a smooth affine
scheme is smooth. Relative spectrum converts the retraction into algebra homomorphisms whose
composite is the identity. Formal smoothness descends using the published
`DynamicSmooth.formallySmooth_of_algSpec_retract`. The coordinate restriction is surjective, so
finite type descends; over a noetherian base it gives finite presentation. This yields algebraic
smoothness and hence scheme smoothness. Affine coordinate isomorphisms transport the conclusion
back to the given schemes. A scheme retraction is surjective on underlying topological spaces,
so connectedness follows by continuity.

Given group-scheme homomorphisms `f : H ⟶ L`, `q : H ⟶ D`, `d : D ⟶ L`, `s : D ⟶ H`
with `q ≫ d = f` and `s ≫ q = id`, `SplitKernelRetract.adjustment` sends a point `h` to
`h s(q(h))⁻¹`. It is killed by `q`, and hence by `f`. The universal property of the actual
scheme-theoretic `kernel f` gives `SplitKernelRetract.retraction`. If the underlying morphism
of `d` is a monomorphism, the kernel inclusion is also killed by `q`, so the retraction restricts
to the identity on `kernel f`. The retraction is an underlying morphism over the base; it need
not be a homomorphism of group schemes.

All arguments are formal consequences of the existing Library kernel, affine-spectrum and
formal-smoothness interfaces, together with Mathlib's finite-type and topology results. They
are internal derived content, with no additional external theorem assumed.

The combined theorem `SplitKernelRetract.smooth_connected_kernel` uses the actual closed
kernel inclusion to prove affineness of the kernel. Its hypotheses are: a noetherian
commutative base ring; a smooth, connected, affine source; a separated target; a factorization
through a monomorphism; and a homomorphic section of the first factor. It then applies the
scheme retraction geometry to this same kernel. The section is explicit input here and must be
proved separately before the theorem can yield unconditional triangular-kernel geometry.
