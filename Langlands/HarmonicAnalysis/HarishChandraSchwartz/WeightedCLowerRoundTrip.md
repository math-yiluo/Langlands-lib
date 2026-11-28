# The lower round trip through the negative auxiliary parabolic

`exists_weightedC_lowerRoundTrip` starts from the lower density package for
`M' ∩ s·P` inside `M'`. It assumes `hPM : PM.canonicalScalar ≠ 0` and
`CommonCompactNormalization`. The field `lower` identifies `PM.K` with the
preimage of `K` in `M'(F)`, supplying the compact inclusion used by
`auxiliaryInner_compare` for induction in stages. The package scalar is a
quotient of regular functions on the lower parameter scheme
(`package_compact_spec`), and `hPM` gives a nonzero numerator.
`auxiliaryInner_compare` identifies the lower round trip with the round trip
of the system `p` between the negative auxiliary vertex `y` and the
opposite `ox` of the positive one, up to a positive factor `t₁`. This is
the product of the two positive scalars comparing the pushed-forward
ambient quotient measure with the lower quotient measure, in the
directions `y` to `ox` and `ox` to `y`. For each direction, the ambient Haar
measures on the target radical and its intersection with the source
radical give their intersections with `K` mass one. The lower Haar
measures on the corresponding groups give their intersections with
`PM.K` mass one, using the normalization in I.1, printed pp. 240–241.
The fractions are pulled back to the
translated parameter scheme along `auxiliaryInnerParameterIso`, using
`rationalUnramifiedRegularFunctionsMap_iso_ne_zero` for nonvanishing.

The lemma provides nonzero regular functions `Mnum`, `Mden` and `c₁`. If
both ambient continuations between `y` and `ox` are regular at `w` and
`c₁(w) ≠ 0`, every scalar value of the round trip `J(ox, y) J(y, ox)` at `w`
equals `t₁ · Mnum(w)/Mden(w)`. For a point of the weighted domain with
lifted parameter `w` and `Mnum(w) ≠ 0`, the lower density value is the
lower density constant times `Mden(w)/Mnum(w)`
(`weightedC_restrict_lowerDensity`).

This is the lower factor in the product formula IV.3(4) of Waldspurger,
printed pp. 286–287. The comparison of intertwiners across the Levi inclusion
is IV.1(14), printed p. 284, and the lower density is `µ^{M'}` of V.2, printed
p. 292 (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
