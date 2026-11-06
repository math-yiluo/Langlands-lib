# Full centralizers, perfect factors and derived subgroup comparison

Over an arbitrary base scheme, the full centralizer of an actual homomorphism
commutes with arbitrary base change. The equality retains every test scheme
and every refinement. Consequently every supplied representative of the full
centralizer remains a representative after base change.

`conjugation_fixedSubgroup_baseChange` proves this equality directly from the
all-refinement commutation criterion. For a test over the old base mapping to
a test over the new base, give its underlying scheme the induced map to the
new base. The existing pullback point equivalence transports the acting
point and the commutation equation. The reverse implication transports each
refinement in the other direction. The represented statement follows by the
existing base change theorem for represented subgroup functors.

`CentralizerProduct.isDerivedSubgroup` assumes a monic inclusion `j : H → G`,
a supplied full centralizer `c : C → G`, a supplied full centre `z : Z → H`,
and a closed factor `d : K → C`. If ambient multiplication `H × K → G`
is flat, surjective and quasi-compact and `derivedSubgroup K = ⊤`, then `d`
represents the full derived subgroup of `C`. The actual isomorphism
`CentralizerProduct.derivedIso` compares `K` with any supplied full derived
representative of `C`, and its homomorphism followed by that inclusion is `d`.

The proof first uses the centre-product pullback to transfer the three
geometric properties to `Z × K → C`. The centre map is central in `C`.
The fpqc central-product theorem then proves that the perfect closed factor
is the full derived subgroup. The existing comparison of representatives
supplies the actual isomorphism and its inclusion equation.

For a field extension `L/k`, assume also that `C` is affine and that an
original full derived representative `e : D → C` is supplied.
`CentralizerProduct.derivedIsoOfFieldExtension` identifies a supplied perfect
closed factor `K` of the base-changed centralizer with the base change of
`D`, if the corresponding geometric ambient multiplication is fpqc.
The isomorphism followed by the base-changed `e` is exactly `d`.
This uses the proved exact base-change equality for the full derived subgroup
of an affine group over a field. If `K` is semisimple, then
`CentralizerProduct.semisimple_of_fieldExtension` proves that `D` is semisimple,
by transporting semisimplicity across the isomorphism and applying the
published arbitrary-field-extension reflection theorem.

The provenance is internal composition of the full centralizer definitions,
point base change, the centre-product pullback, fpqc central-product derived
comparison, exact field base change and semisimplicity reflection. All
representatives, fpqc multiplication and perfectness remain explicit inputs.
This module neither constructs a geometric complement nor proves semisimple
perfectness or the unconditional normal-isogeny-complement theorem. No
smoothness is required of the full centralizer or its centre.

Authorship: Worker 1616.
