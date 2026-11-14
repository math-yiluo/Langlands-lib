# Unramified zero points in a compatible torus

This internal supporting construction works at arbitrary universe `u` over
`K = UnramifiedClosure F`, for a nonarchimedean local field `F`. The field `K`
itself is not assumed to be a local field. Let `E : UnramifiedZeroDatum F G`;
its specified torus is `E.T`, its inclusion is `E.i`, and its finite Galois
splitting field is `E.L`.

`UnramifiedZeroDatum.torusZeroDatum` constructs zero data for `E.T.toGrp`
itself. It retains exactly `E.T` and `E.L` and takes the torus inclusion to be
the identity. The identity is a maximal torus inclusion, by transport from
`E.i`; a maximal split torus in `E.T` makes it maximally split. The derived
group and its simply connected cover are both the actual trivial group
scheme, with its identity cover and unit inclusion into `E.T`. The published
`commutativeDerivedCoverData` construction supplies the required cover
property, using connected reductivity of a torus.

The theorem `torusZeroDatum_zeroPoints` identifies these zero points with
the original `E.torusIwahori`. Every rational point of the trivial cover is
the identity, so its image subgroup is trivial. The other factor in the
definition of zero points is the original Iwahori subgroup mapped along the
identity.

For a split subtorus inclusion `a : A.toGrp ⟶ G`, assume explicitly that
`E.i` represents the entire subgroup functor `torusCentralizer a`. Then
`zeroPoints_comap_inf_characterValuationKernel_eq_torusIwahori` proves

```text
E.zeroPoints.comap (rationalPoints.map E.i)
  ⊓ characterValuationKernel (fixedFieldValuation F) E.T.toGrp
    = E.torusIwahori.
```

Here the Iwahori subgroup is the norm image from the character-unit subgroup
over the original `E.L`. The character-valuation kernel uses the specified
fixed-field valuation.

The proof first applies the published
`coverImage_inf_characterValuationKernel_le_zeroPoints` to the original
ambient derived cover, the split subtorus `a`, the representative `E.i`, and
the constructed `E.torusZeroDatum`. Its four structural hypotheses are
discharged by the published theorems `cocenterQuotientExistence`,
`splitTorusCentralizerCocenterInduced`, `inducedTorusIwahori`, and
`splitTorusCentralizerCoverPreimage`. Replacing the torus datum's zero points
by `E.torusIwahori` gives
`coverImage_comap_inf_characterValuationKernel_le_zeroPoints`.

Norm images of character-unit points lie in the fixed-field
character-valuation kernel, by `torusNormIwahori_le_characterValuationKernel`
and invariance of the splitting-field valuation under Galois conjugation.
If `t` belongs to the intersection in the displayed equality, the published
zero-point product theorem writes `E.i(t) = c * E.i(s)` with `c` in the
simply connected image and `s` in `E.torusIwahori`. Consequently `t * s⁻¹`
maps into the simply connected image and remains in the torus's
character-valuation kernel. The preceding containment puts it in the Iwahori
subgroup, and multiplication by `s` puts `t` there too. Conversely, the
Iwahori image lies in ambient zero points by definition, and its points lie
in the character-valuation kernel by the norm argument.

The provenance is internal: this pair specializes and combines existing
Library constructions and theorems; it introduces no new translation of an
external statement. It supplies a comparison needed by
`UnramifiedParahoricModelStatement`. It does not identify a whole-apartment
fixer with a centralizer, construct an integral model, or prove the complete
host statement.
