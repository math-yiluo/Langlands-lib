# Central characters of presented local components

Let a cuspidal operator realization have central character \(\chi\). On its presented local component at a finite place \(v\), a scalar matrix \(aI\) acts by \(\chi_v(a)\), where \(\chi_v\) is the restriction of \(\chi\) along the finite idèle inclusion at \(v\).

`CuspidalSpectralPresentation.localComponent_hasCentralCharacter` transfers the global character condition to the finite slice with `FiniteRealization.hasCentralCharacter`, then uses `FiniteTensorPresentation.localComponent_hasCentralCharacter` and the nonzero finite slice of the presentation.

`LocalRealization.representation_scalar_of_hasCentralCharacter` checks the scalar action at each adelic point. `LocalRealization.evaluate_representation` computes the action by right translation. `AdelicGL.scalar_finiteIdeleInclusion` and `AdelicGL.scalar_commute` identify it with left translation by the central idèle. The central-character condition then computes the value, and injectivity of evaluation on the realization gives the vector identity.

This is the local restriction of the central action used in Henniart (2000), §2.2, printed p. 444. It supplies the local action in the determinant clause of `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.
