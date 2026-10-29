# Proof of descent of compatible global units

The entry theorem `Langlands.Scheme.compatibleUnitsDescent` proves the unchanged
`CompatibleUnitsDescentStatement`.

The helper `compatibleUnitsDescent_of_effectiveEpi` first replaces the given unit
`s` by its representing morphism `e : X ⟶ Spec Gm.laurentRing` under
`Gm.unitsHomEquiv`. Naturality (`Gm.unitsHomEquiv_comp`) and injectivity of the
representing equivalence turn the hypothesis on all equal-composite pairs into
the coequalizing condition required by `EffectiveEpi.desc p e`.

The descended morphism `d` represents the required unit on `Y`.
`EffectiveEpi.fac` and naturality show that its pullback is exactly `s`.
If another unit has that pullback, the corresponding representing morphisms
become equal after precomposition by `p`. Effective epimorphisms are
epimorphisms, so cancellation proves equality of the morphisms. Applying
`Gm.unitsHomEquiv` gives equality of the units.

The entry theorem supplies the effective-epimorphism instance from Mathlib's
`AlgebraicGeometry/Sites/Fpqc.lean` using precisely the stated quasi-compactness,
flatness and surjectivity assumptions. This proof is an internal deduction from
the existing representing equivalence and effective-epimorphism API. It does
not supply module-sheaf gluing or line-bundle effectivity.
