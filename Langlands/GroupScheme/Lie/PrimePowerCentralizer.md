# Centralizers of actual Lie prime powers in positive characteristic

This internal construction derives centralizer and spanning consequences from
the actual prime-power Lie elements and their simultaneous representation
formulas. It combines those formulas with the previously proved intrinsic
adjoint centralizer coordinates and the nonnilpotent adjoint spanning theorem.
No external structural theorem about algebraic groups is invoked.

Let `G` be an actual affine group scheme locally of finite type over a field
`k`, and let `p` be a natural prime with `CharP k p`. The function
`semisimplePrimePowerExponent G X p` chooses an exponent from
`exists_isSemisimpleElement_primePowerKernel`, independently of any
representation. The actual identity-kernel point
`semisimplePrimePowerReplacement G X p` is the corresponding
`primePowerKernel`. The first theorem states its representation-tested
geometric semisimplicity.

Fix actual finite coordinates `c : FiniteCoordinates G d`.
`adjointDifferentialFamily_primePowerKernel` proves that the actual adjoint
differential of `primePowerKernel G X p r` is the `p^r`-th power of the
actual adjoint differential of `X`. It applies the already proved
prime-power tangent-matrix formula to the actual adjoint representation and
uses compatibility of matrix-to-endomorphism conversion with powers.
This formula needs affineness but does not need local finite type.

`elementCentralizerLie_le_primePowerKernel` proves that taking a prime
power enlarges the actual tangent centralizer. The intrinsic adjoint
centralizer identity identifies these submodules with kernels of their
own adjoint differentials. If the original differential kills a vector,
so does its `p^r`-th power, because `p^r` is positive. Self-centralization
then places `X` in the actual tangent centralizer of every one of its
prime powers.

If the actual adjoint differential of `X` is nonnilpotent, the tangent
centralizer of any prime power is proper. Otherwise its adjoint
differential would vanish, and the power formula would give a vanishing
power of the original differential. The combined theorem
`semisimplePrimePowerReplacement_properties` therefore says that the
chosen replacement is semisimple, has proper tangent centralizer, and
has tangent centralizer containing the original one.
`exists_noncentral_semisimple_centralizing_of_not_isNilpotent` adds
self-centralization to give a noncentral semisimple element whose actual
tangent centralizer contains the original `X`. Here “noncentral” means
precisely that its actual tangent centralizer is not the whole Lie module.

Finally, let `k` be infinite, and let `K` be any field extension in the
same arbitrary universe. Assume that the actual scheme pullback `G_K`
has a representation-semisimple Lie element with proper tangent
centralizer. The theorem
`semisimpleCentralizer_spanning_of_geometric_semisimple_primeChar`
proves both existence of such an element over `k` and
`noncentralSemisimpleCentralizerSpan G = top`. The imported nonnilpotent
adjoint locus theorem gives a ground-field nonnilpotent element and says
that the entire such locus spans the Lie module. The preceding replacement
theorem puts every element of that locus in one of the noncentral
semisimple tangent centralizers. Each of those submodules is contained in
the defining supremum, so the nonnilpotent spanning equality proves that
the supremum is the whole module.

All fields and actual schemes retain arbitrary universe `u`. Finite coordinate
sizes include zero, and no smoothness, connectedness, reducedness, splitness,
or perfection hypothesis is added. The extension `K` need not be algebraic
or algebraically closed. The final spanning theorem retains its explicit
geometric semisimple premise and positive-characteristic hypotheses. This
module does not prove the corresponding characteristic-zero assertion,
the existence of Cartan subgroups, or Cartan generation.
