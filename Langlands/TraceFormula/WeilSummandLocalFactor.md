# The twisted local factor of a cuspidal summand of `Res_{L/K} GL_n`, read over a field

Let \(L/K\) be a finite extension of number fields such that the adele quotient of \(L\)
is compact. Let \(\sigma_K \in \operatorname{Aut}(L/K)\) and let
\(W = \operatorname{Res}_{L/K} GL_{r+1}\), the Library's `weilGroup K L GLᵣ`. Take the
central torus data of `fullAEL2CuspidalSubmodule` and a Haar measure \(\nu\) on
\(W(\mathbb A_K)\). Let \(S\) be the full almost-everywhere cuspidal subspace of \(L^2\) of
the positive rational quotient of \(W(\mathbb A_K)\).

Fix a finite place \(v\) of \(K\) and p-adic fields \(F\) and \(E\) with \(E\) an
\(F\)-algebra. Let \(\sigma \in \operatorname{Aut}_F(E)\). Let \(e_E\) be a ring
isomorphism from the local algebra \(E_v = K_v \otimes_K L\)
(`LocalBaseChangeAlgebra K L (.inr v)`) onto \(E\) that is continuous with continuous
inverse. Assume that it intertwines \(\sigma_v = \mathrm{id} \otimes \sigma_K\)
(`localGalois`) with \(\sigma\). Let \(\kappa\) be the induced topological group
isomorphism \(GL_{r+1}(E_v) \to GL_{r+1}(E)\). Let \(g_v\) be the \(v\)-component of
\(g \in W(\mathbb A_K)\), read in \(GL_{r+1}(E_v)\) through `localPointsEquiv`.

## Statement

`WeilSummandLocalFactorStatement` assumes the two Library statements
`WeilGeneralLinearCuspidalSummandRealizationStatement` and
`WeilGeneralLinearCuspidalLocalTwistedTraceStatement`.

Let \(P\) be a nonzero complete subspace of \(S\). Assume that it is invariant under the
right action and has no closed invariant subspaces other than \(0\) and \(P\). Let
\(\Theta\) be the automorphism of \(W(\mathbb A_K)\) induced by \(\sigma_K\). Assume that
\(\Theta\) preserves the positive rational subgroup and the quotient measure, and that the
twisting operator \(I_\Theta\) maps \(P\) into \(P\).

The conclusion supplies three things:

- an irreducible admissible representation \(A\) of \(GL_{r+1}(E)\), generic for a
  nontrivial unitary additive character of \(E\);
- an isomorphism \(B\) of \(A\) onto \(A^\sigma\) (`SigmaIntertwiner σ (r + 1)`);
- a functional \(C\) of the exterior test.

Let \(f_v\) be a Schwartz–Bruhat function on \(GL_{r+1}(E)\). Let \(f^v\) be a function on
\(W(\mathbb A_K)\) that is invariant under right translation by \(W(K_v)\). Suppose that
\(f(g) = f_v(\kappa(g_v))\,f^v(g)\) is \(\nu\)-integrable. Let \(B_P\) be the compression
to \(P\) of the compression to \(S\) of \(R(f) \circ I_\Theta\), and suppose that it is
trace class. Then
\[
  \operatorname{tr} B_P = \operatorname{tr}\bigl(A(f_v) \circ B\bigr) \cdot C(f^v),
\]
where the twisted trace is `twistedDistribution` for `sphericalHaar E r`. The data
\(A\), \(B\) and \(C\) do not depend on \(f_v\) or \(f^v\).

## Local algebra

`localTensorEquiv K L v` is the completed tensor comparison
\(E_v \cong \prod_{w \mid v} L_w\) (`finiteTensorMap`, bijective by
`completedTensorComparison`) as a \(K_v\)-algebra isomorphism.
`exists_unique_placeAbove_of_isDomain` shows that exactly one place \(w\) of \(L\) lies
above \(v\) when \(E_v\) is a domain. Two distinct places would give two nonzero
idempotents with product zero. `localPlaceAboveEquiv` is then the \(K_v\)-algebra
isomorphism \(E_v \cong L_w\), evaluation at \(w\) after `finiteTensorMap`. It is
continuous in both directions for the module topologies over \(K_v\). Under the
hypotheses of the statement \(E_v \cong E\) is a field, so the place \(w\) exists.

`fieldPlaceAboveEquiv` is the composite \(E \cong E_v \cong L_w\).
`weilPresentationFieldObject` is the local component at \(w\) of a spectral presentation
over \(L\), in the canonical category over `CompletionPadic.padicField w`, pulled back to
\(E\) along that composite by `fieldPullbackObject`. The canonical topology of the
completion equals its completion topology by `CompletionPadic.completion_topology_eq`.
This identifies the continuity conditions. `weilPresentationFieldObject_isGeneric`
proves genericity as in `GeneralLinearSummandLocalFactor`. The global Whittaker
coefficient gives a nonzero functional equivariant for a character that is nontrivial and
trivial on the integers (`CuspidalWhittaker.exists_localWhittakerFunctional`).
`LocalRealization.isGeneric_of_integerTrivial_character` and
`fieldPullbackObject_isGeneric` then give genericity over \(E\).

## Proof

The realization statement gives a cuspidal operator realization \(R\) over \(L\) and a
linear map from its forms to \(S\) whose image is dense in \(P\). The completeness of
\(P\) gives its closedness. The theorems
`cuspidalIrreducibleAdmissibleFiniteSliceExistence` and
`CuspidalOperatorRealization.exists_presentation_of_finiteSlice` give a spectral
presentation \(D\) of \(R\). Its local components are irreducible and admissible at
every finite place, in particular at \(w\).

The Haar measure on \(GL_{r+1}(K_v \otimes_K L)\) is the pushforward of
`sphericalHaar E r` under \(\kappa^{-1}\). Part 2 of the twisted local trace statement
gives an isomorphism \(A_v\) of the local component \(\Pi_v\) onto \(\Pi_v^{\sigma_v}\)
and a functional \(C\). The trace of \(B_P\) is then the twisted trace of
\(\Pi_v(f_v \circ \kappa) \circ A_v\) times \(C(f^v)\).

`SigmaIntertwiner.ringPullback` carries \(A_v\) along \(e_E^{-1}\) with the same linear
map. This uses the compatibility of \(e_E\) with \(\sigma_v\) and \(\sigma\). The result
is the intertwiner \(B\) for the representation over \(E\). The change-of-variables
theorem `twistedDistribution_comp_equiv` moves the twisted trace to \(GL_{r+1}(E)\). There
\(\Pi_v \circ \kappa^{-1}\) and `weilPresentationFieldObject` are the same
representation on the same space.

In the Lean proof, `AdelicGroupAutomorphism.weilGroup`, `AffineWeil.groupScheme`,
`AffineWeil.unitBaseChange` and `Corepresented.groupScheme` are made locally
irreducible. Unification then compares their arguments instead of unfolding the Weil
restriction. The kernel checks the resulting proof as usual.

## Sources

This reads the twisted local factors of Henniart–Lemaire, *Changement de base et
induction automorphe pour GLₙ en caractéristique non nulle* (2011), Proposition of II.6.5,
printed pp. 121–122, over the local field of the fundamental lemma, at a place with one
place above it. Their genericity is used in I.5.5, printed pp. 35–39, and the spherical
comparison in I.6.9, printed pp. 50–51. The argument is an internal combination of the
cited Library statements and theorems.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
