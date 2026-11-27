# The local factor of a cuspidal summand of `GL_n`, read over a given p-adic field

Let \(K\) be a number field whose adele quotient is compact. Let \(S\) be the full
almost-everywhere cuspidal subspace of \(L^2\) of the positive rational quotient of
\(GL_{r+1}(\mathbb A_K)\), with the central torus data of
`fullAEL2CuspidalSubmodule`. Fix a finite place \(v\), a p-adic field \(F\) and a
ring isomorphism \(e_F : K_v \to F\) that is continuous with continuous inverse.
`localPlaceFieldEquiv K r v F eF` is the topological group isomorphism from the
points of the group scheme \(GL_{r+1}\) over \(K_v\) to \(GL_{r+1}(F)\). It composes
`localGLHomeomorph` with the entrywise map of \(e_F\).

`GeneralLinearSummandLocalFactorStatement` assumes the two Library statements
`GeneralLinearCuspidalSummandRealizationStatement` and
`GeneralLinearCuspidalLocalComponentTraceStatement`. Let \(P\) be a nonzero complete
subspace of \(S\) that is invariant under right translation and has no closed
invariant subspaces other than \(0\) and \(P\). The conclusion supplies an irreducible
admissible representation \(A\) of \(GL_{r+1}(F)\), generic for a nontrivial
unitary additive character of \(F\), and a functional \(C\) of the exterior test. Let
\(f_v\) be a Schwartz–Bruhat function on \(GL_{r+1}(F)\). Let \(f^v\) be a function
on the adelic group that is invariant under right translation by the points over
\(K_v\). Suppose that \(g \mapsto f_v(\kappa(g_v))\,f^v(g)\) is integrable and that
the compression of its integrated action to \(P\) is trace class. Then
\[
  \operatorname{tr}\bigl(P\,R(f)\,P\bigr)
    = \operatorname{tr} A(f_v)\cdot C(f^v),
\]
where \(\operatorname{tr} A(f_v)\) is the distribution character for `sphericalHaar F r`.
The functional \(C\) does not depend on \(f_v\) or \(f^v\).

## Proof

The realization statement gives a cuspidal operator realization \(R\) and a linear map
from its forms to \(S\) whose image is dense in \(P\). The completeness of \(P\) gives
its closedness. The Library theorems
`cuspidalIrreducibleAdmissibleFiniteSliceExistence` and
`CuspidalOperatorRealization.exists_presentation_of_finiteSlice` give a spectral
presentation \(D\) of \(R\) whose local components are irreducible and admissible at
every finite place.

The Haar measure on the local group is the pushforward of `sphericalHaar F r` under
the inverse of \(\kappa\). The local component trace statement then factors the trace
through the character of `localRealizationPlaceRepresentation (D.localComponent v)`
at the test \(f_v \circ \kappa\).

`presentationFieldObject` is the component at \(v\) in the canonical category over
`CompletionPadic.padicField v`, pulled back to \(F\) by `fieldPullbackObject` along
\(e_F^{-1}\). The canonical topology of the completion equals its completion topology
by `CompletionPadic.completion_topology_eq`. This identifies the two continuity
conditions. Composing the place representation with \(\kappa^{-1}\) gives the same
operators as the pullback, since `localGLHomeomorph` cancels against its inverse.
The change-of-variables theorem `distribution_comp_equiv` and equality of the two
representations then identify the two distribution characters.

The global Whittaker coefficient of the presentation gives a nonzero functional on
the local component. It is equivariant for the local component of the standard
character of \(\mathbb A_K/K\) (`CuspidalWhittaker.exists_localWhittakerFunctional`).
That local character is nontrivial and trivial on the integers. Hence
`LocalRealization.isGeneric_of_integerTrivial_character` gives genericity for a
nontrivial character of the completion, which exists by
`padicUnitaryAdditiveCharacterExists`. `fieldPullbackObject_isGeneric` transfers
genericity to \(F\).

This reads the local factors of Henniart–Lemaire, *Changement de base et induction
automorphe pour GLₙ en caractéristique non nulle* (2011), II.6.5 and I.6.9, printed
pp. 121–122 and 50–51, over the local field of the fundamental lemma. Genericity of
these factors is used in I.5.5, printed pp. 35–39. The argument is an internal
combination of the cited Library statements and theorems.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
