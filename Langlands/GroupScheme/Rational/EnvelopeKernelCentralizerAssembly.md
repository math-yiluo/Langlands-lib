# Actual kernel and centralizer geometry of a torus envelope

This internal construction combines the actual restricted-kernel geometry and
centralizer-intersection comparison with the finite-field normality interface.
It retains the supplied sectioned torus quotient, and makes no assumption of
product surjectivity or normality.

For a smooth connected actual representative `D` of the unchanged closed torus
envelope over a perfect field, `D.kernelCentralizerGeometry` constructs the
complete `EnvelopeKernelCentralizerGeometry D n q s` record. The ambient group
is smooth connected affine; the supplied closed unipotent subgroup `n` is
exactly the full kernel of the supplied fppf torus quotient `q`, with
homomorphic section `s`. The construction does not require smoothness or
connectedness of this supplied kernel as extra inputs.

The section factors canonically through `D`, and the kernel of the resulting
restricted quotient is the record's actual group `V`. Its closed inclusion,
map to the original kernel, compatibility equation, smoothness, connectedness,
unipotence, splitness and fppf quotient property are supplied by
`SectionedSubgroupKernel`.

The construction applies `torusKernelCentralizerData` both to the ambient
group and to `D.group`, using this same section and restricted kernel.
The first application supplies the actual centralizer `C` inside the original
kernel. The second, together with the published intersection comparison,
supplies smoothness and connectedness of the actual scheme-theoretic
intersection of `V → N` with `C → N`. Perfect-field splitness gives represented
split unipotent series for these same groups. All subgroup identities hold on
arbitrary relative test schemes, including nonreduced tests.

`D.sectionedQuotientKernelCentralizerGeometry a` specializes this construction
to `SplitGeometricRadicalSectionedTorusQuotient G`. It uses exactly the
radical inclusion, quotient projection and section stored in `a`.

This is a supporting construction. The absolute solvable torus quotient,
stable-vector and finite-field product statements remain separate proof inputs
to the surrounding normality argument.
