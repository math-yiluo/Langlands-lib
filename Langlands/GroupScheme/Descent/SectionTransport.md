# Group-valued sections and actual Čech transport

This internal derived adapter uses the actual group-scheme and Čech datum
interfaces in `Descent.Data` and `Descent.DatumRelation`, and Mathlib's
slice pullback adjunction and groups of morphisms into group objects.
It introduces no assertion attributed to external literature.

All schemes and test schemes are in arbitrary universe `u`. No affineness,
field, flatness, surjectivity, quasi-compactness, finite-type or
commutativity assumption is used.

For `f : T ⟶ S`, `r : Z ⟶ T`, and a group scheme `H` over `S`,
`sectionPullbackEquiv` is the multiplicative equivalence

```text
(Over.mk (r ≫ f) ⟶ H.X) ≃* (Over.mk r ⟶ ((baseChange f).obj H).X).
```

The two groups are groups of sections on the actual slice categories.
Its underlying equivalence is the hom-set equivalence of
`Over.mapPullbackAdj f`. The forward map is pullback on morphisms
followed by precomposition with the diagonal section
`Z ⟶ Z ×_S T`. Both operations preserve multiplication, which proves
the multiplicative-equivalence law.

`sectionPullbackEquivOfEq` gives the same equivalence for a specified map
`z : Z ⟶ S` and equality `r ≫ f = z`. Its projection formulas identify
the forward map with `pullback.lift a.left r`, and the inverse map with
composition with `pullback.fst H.X.hom f`.

For an actual datum `D : Datum p G`, maps `z₁ z₂ : Z ⟶ S`, and an
equality `z₁ ≫ p = z₂ ≫ p`, `D.sectionTransport` is a multiplicative
equivalence from sections of `G` above `z₁` to sections above `z₂`.
The construction first pulls back a section to the overlap point
`pullback.lift z₁ z₂ h`, then postcomposes with the datum's actual group
isomorphism, and finally applies the inverse section-pullback equivalence.
Each step is a multiplicative equivalence; consequently transport also
preserves the unit and inverse.

`D.sectionTransport_left` identifies its underlying scheme morphism with
the previously constructed all-test transport `D.move a.left z₂`.
The proof expands the three equivalences and uses the pullback projection
formulas and the section's equation over `S`.

The module supplies transport of sections only. Construction of a
descended group scheme and of a simply connected cover remain separate
obligations.
