# Transport to an irreducible real standard module

These internal lemmas implement the standard-module step of the real exponent-bound argument. They use the Library's `HasRealStandardParameter` and the definition of infinitesimal unitarity in Knapp–Vogan, *Cohomological Induction and Unitary Representations* (1995), display (0.5), p. 6 (PDF p. 28, `knapp-vogan-1995-cohomological-induction`).

`IsRealStandardIntertwiner.toCompactIntertwiningMap` bundles the compact equivariance of the given linear map as a Mathlib representation intertwiner. `IsRealStandardIntertwiner.isUnitarizable_of_injective` uses this map to pull the form back by `InvariantPositiveForm.comap`. The Lie intertwining identity reduces the skew condition for each real matrix to the skew condition on the given module.

`realStandardParameter_model` uses `realStandardNontrivial` at the rank recorded in the parameter. The parameter injection is therefore nonzero, and `IsRealStandardIntertwiner.surjective` makes it surjective onto the irreducible module. The image of each stable submodule of the standard module is stable. Injectivity reflects its equality with the zero or full submodule from the target. The Whittaker functional pulls back along the map and is nonzero by surjectivity. The positive form transfers by the preceding lemma.

`realUnitaryGenericExponentBound_of_standard` applies a bound on the canonical models to the transported hypotheses. Its premise is the remaining exponent estimate on those models. Its conclusion retains the published target's unrestricted carrier universe.
