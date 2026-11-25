# Natural maps on units are determined on roots of unity

This internal development applies the relative schematic density helpers to
natural families of maps on global units into a scheme separated over the base.
It is intended for the diagonal-preimage commutativity step in Conrad,
*Reductive group schemes* (2014), Proposition 4.3.1.

`laurentUnit A` is the unit represented by `X` in `A[X, X⁻¹]`. `specUnit`
transports ring units to units of the global sections of the spectrum.
The two compatibility lemmas express this transport under ring maps and under
the morphism associated to a ring map into the global sections of a scheme.

`laurentEvaluation s` evaluates `X` at the unit `s`, fixes coefficients, and
takes the universal Laurent unit to `s`. For affine `V`, `laurentProjection V`
maps `Spec(Γ(V)[X, X⁻¹])` to `V`; `laurentSpecialization V s` is a section of
that projection and pulls the universal unit back to `s`.
`laurentUnit_quotient_pow` checks that the image of the universal unit is an
`(n+1)`st root of unity after taking the quotient by `rootsOfUnityIdeal A n`.

`units_natural_ext_affine` takes two families

```text
F, F' : for each V → T, global units of V → morphisms V → Y over S,
```

where `Y → S` is separated. The families are assumed natural under every
morphism of test schemes over `S`, and equal whenever the input unit has any
positive finite order. The conclusion is equality for every unit on an affine
test scheme. The proof first evaluates both families on the universal Laurent
unit. On each quotient by `rootsOfUnityIdeal A n`, naturality and the
finite-order hypothesis give equality. The zero-intersection result and
`eq_of_eq_on_quotients` from `Density` give equality on the universal test
scheme itself. Pullback along `laurentSpecialization` then gives equality at
the original unit.

`units_natural_ext` has the same naturality and finite-order hypotheses and
concludes equality on arbitrary test schemes. Restriction to an affine cover
reduces it to the affine result; the cover's joint epimorphism property gives
equality of the morphisms. There is no affineness, finiteness or reducedness
assumption on the base, the fixed parameter test scheme `T`, or the final
test scheme `V`.

All declarations are derived supporting constructions and lemmas. They do not
prove commutativity of any central-extension preimage or existence of an
extension section. The module imports the `Density` helpers and adds no
assumptions to its mathematics.
