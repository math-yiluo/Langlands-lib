# Relative derived groups as kernels of smooth torus quotients

This internal supporting module reformulates the geometric existence input
`RelativeDerivedGroupExistenceStatement` using the full scheme-theoretic kernel
of a supplied quotient homomorphism. It does not construct that quotient and
does not prove either existence statement.

For a homomorphism `q : G ⟶ Q` over any scheme `S`,
`RelativeDerived.IsSemisimpleTorusQuotient q` means that `Q` is a relative torus,
`q` is smooth and surjective, and the full kernel of the actual geometric-fibre
homomorphism is semisimple at every point of `S`. The geometric kernels retain
the whole scheme structure. There is no restriction on the base or on
characteristic.

`RelativeDerived.isAdmissible_kernelι` proves that, for a reductive source,
the full kernel inclusion of such a quotient satisfies the unchanged
`RelativeDerived.IsAdmissible` predicate. The kernel square is a pullback of
the quotient homomorphism along the target's identity section, so the kernel
is smooth. A relative torus is affine and separated, making the kernel
inclusion closed. Its composite with the affine source structure map is
affine. The published kernel/base-change isomorphism transports the supplied
semisimplicity to the geometric fibres of this kernel. Those fibres are
therefore pseudo-reductive, proving reductivity of the kernel. Its range is
normal because homomorphisms kill conjugates of kernel points. Finally,
smoothness gives flatness and local finite presentation; together with
surjectivity and the identical kernel range, this is precisely the existing
`RelativeRoot.IsFppfQuotient` predicate.

The converse helpers concern any specified quotient by an admissible subgroup.
`RelativeDerived.IsAdmissible.smooth_quotient` applies the published smoothness
theorem for an fppf quotient by a smooth represented kernel. The required
quasi-compactness follows from affineness of the source over `S` and
separatedness of the torus target, so it is not an added assumption.
`RelativeDerived.IsAdmissible.isSemisimple_geometricKernel` identifies the
specified subgroup with the full kernel, then base-changes this isomorphism
and uses the kernel/base-change comparison. The subgroup's semisimple
geometric fibres give semisimplicity of the full geometric kernels.
`RelativeDerived.IsAdmissible.isSemisimpleTorusQuotient` combines these facts.

`RelativeDerivedTorusQuotientExistenceStatement` asks for a quotient with this
property for every reductive group over every base scheme.
`relativeDerivedGroupExistence_iff_torusQuotient` proves its equivalence with
the unchanged published existence input. The forward implication uses the
quotient in admissibility and the converse helpers. The reverse implication
chooses the actual kernel and applies `isAdmissible_kernelι`.

The provenance is an internal categorical reformulation of the published
`RelativeDerivedInputs` interface. That interface records the geometric
existence part of Conrad's *Reductive group schemes* (2014), Theorem 5.3.1;
the present module only proves the kernel packaging and converse from
published pullback, torus geometry, represented-kernel and quotient-smoothness
results. No geometric existence, relative derived-group uniqueness, or
semisimple fppf-perfectness assertion is assumed by these helpers.
