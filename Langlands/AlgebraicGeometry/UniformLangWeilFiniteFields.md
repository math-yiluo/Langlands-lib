# Uniform lifting over sufficiently large finite fields

Author: Worker 208.

This is a derived construction for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Theorem 4.5, printed p.13,
last paragraph, using the full uniform estimate of Lemma 4.6, printed
pp.12–13, as an explicit premise. The affine-line enlargement below is an
internal proof route for the passage to all sufficiently large fields of
values; it is not claimed to be Conrad's written proof.

`uniformLangWeilLargeFiniteFieldPointLifts` constructs a positive real
constant `C`, followed by an actual lift of every morphism
`p : Spec K ⟶ B` from every finite field `K` with `C² < #K`. The output is
an actual morphism `q : Spec K ⟶ Y` together with the equality `q ≫ f = p`.
The constant is chosen before the field and its point and hence is uniform
in both. All schemes and fields lie in an arbitrary common universe.

The hypotheses are exactly those passed to `UniformLangWeilStatement`:
`B` is locally of finite type over the universe-lifted integers and has
compact underlying space; `f : Y ⟶ B` is smooth, separated, surjective,
locally of finite type, quasi-compact and geometrically connected, and all
its fibres have pure dimension `d`. The construction does not require
`B` or `Y` to be affine or separated over the integers. The full uniform
estimate remains an explicit parameter, rather than a result proved here.

`exists_surjective_integer_polynomial_map` proves that every finite field
is a quotient of `(ULift ℤ)[X]`. Choose a generator of the cyclic group of
units and evaluate `X` at it. Zero is the image of zero, and every nonzero
field element is the image of a natural power of `X`.

`surjective_descResidueField_of_affine_coordinate` concerns any field-valued
point `p` of any scheme, without finiteness or closedness hypotheses. If
`p` has a surjective affine coordinate map `A → K`, then the induced map
from the image residue field to `K` is surjective. The coordinate map
factors through that residue field: express the composite from
`Spec κ(b)` to `Spec A` as the spectrum of a ring homomorphism and use the
actual residue-field factorization of `p`. Surjectivity of the composite
forces surjectivity of its second factor. That factor is also injective,
because its domain is a field, so its source and target have equal
cardinality.

For the main construction, form the fixed scheme
`B' = B ×_(Spec (ULift ℤ)) Spec ((ULift ℤ)[X])`, let `g : B' ⟶ B` be the
projection, and base-change `f` to `f' : Y ×_B B' ⟶ B'`. The polynomial
structure map is of finite type and quasi-compact, so `B'` retains the
required finite-type and compactness hypotheses. The geometric hypotheses
on `f` survive base change. Pure fibre dimension survives by
`SchemeFiberGeometry.hasPureDimension_locallyFiniteType_fiberBaseChange_iff`,
which applies to arbitrary locally finite-type schemes.

Apply `uniformLangWeilLargeResidueFieldPointLifts` to this fixed family to
choose `C`. Given `K` and `p`, choose the generating polynomial coordinate
and use the actual pullback universal property to construct
`p' : Spec K ⟶ B'` projecting to `p`. The preceding helper identifies
`κ(p')` with `K` for cardinality purposes. Thus `C² < #K` supplies the
residue-field threshold required by the existing construction. Project
its lift from `Y ×_B B'` to `Y`; the pullback equations prove the exact
equality with the supplied morphism `p`.

This strengthens the threshold on the image residue field in
`UniformLangWeilFieldPoints` to a threshold on the field of values.
Largeness of `K` alone need not make the original image residue field
large; the extra coordinate is what permits the argument. This file
neither proves the uniform Lang–Weil estimate nor supplies the spreading,
finite exceptional-place, or adelic openness arguments needed to complete
Theorem 4.5.
