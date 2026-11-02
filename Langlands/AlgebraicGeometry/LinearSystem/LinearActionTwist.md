# The degree-one twist under polynomial linear actions

This internal derived construction identifies the actual pullback of the degree-one
projective twist under the polynomial projective action of an invertible coordinate
map with the original twist. It applies to every commutative ring `R : Type u` and
every natural number `n`. Write `a_e` for `ProjectiveSpace.linearAction R n e`,
`L` for the actual module sheaf `twistOne R n`, and `x_i` for its homogeneous
coordinate sections.

`linearActionTwistIso R n e` constructs an isomorphism `a_e^* L ≅ L`.
The comparison sends the actual pulled-back section `a_e^* x_i` to
`changedProjectiveCoordinates R n e i`, the linear combination specified by the
`i`th row of `e`, with coefficients pulled from the base spectrum.
The changed coordinates generate because the coordinate transformation is invertible.
Their linear-system map is the actual polynomial action: the published coordinate
change law and recovery of the identity from the original coordinates prove this
equality. The construction transports pullback along that equality and then uses
the section-preserving linear-system twist comparison.

The comparisons have the following compatibility properties. For the identity
coordinate map the isomorphism equals equality transport from `a_id` to the
identity scheme map, followed by the canonical identity-pullback comparison.
They commute with every further linear combination of coordinates, including
noninvertible combinations: the action is over `Spec R`, so it fixes the pulled-back
base coefficients. If `e.trans f` means first `e` and then `f`, their composition
law, as an equality of module-sheaf morphisms, is

```
a_e^*(linearActionTwistIso f).hom ≫ (linearActionTwistIso e).hom
  = pullbackComp(a_e, a_f).hom
      ≫ pullbackCongr(a_e ≫ a_f = a_(e.trans f)).hom
      ≫ (linearActionTwistIso (e.trans f)).hom.
```

The auxiliary `hom_ext_of_generating_sections` shows that sections whose frame opens
cover determine a module-sheaf map. Its proof restricts to intersections with those
opens, expresses every local section as a scalar multiple of the frame, and applies
the sheaf equality criterion. `frameCover_pullback` obtains a pulled-back frame
cover from the actual equality of frame opens with inverse images. Generic
section-evaluation lemmas give a composition criterion for pullback comparisons.
Applying this criterion to the coordinate sections reduces the displayed law to
their explicit comparison formulas and composition of linear combinations.
The identity law similarly follows by equality on the pulled-back coordinates.

All content is derived from the imported constructions and their proved laws;
no new external source assertion is used. This module concerns polynomial
projective space over an arbitrary commutative ring. Comparison with the twist
on the integral relative model, a tautological bundle on a glued projective bundle,
and ordinary moduli representability remain further obligations.
