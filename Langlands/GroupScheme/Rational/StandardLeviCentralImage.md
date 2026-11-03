# Central split-torus images in a standard Levi

This internal construction combines the actual selected-root weight-space
comparison with central-root restriction. It retains `DynamicLieStatement` as
an explicit premise.

Let the affine ambient group scheme be locally of finite type over any field.
Let `j : L → G` be a closed all-test representative of `standardLevi i ν J`,
where `J` is a subset of the actual simple relative roots. Given a central
split torus `a : A → L` and an actual commutative-group-scheme map `f : A → T`
whose composite into `G` is `a ≫ j`, every selected character restricts to
zero along `f`.

The proof obtains affineness and local finite type of `L` from closedness of
`j`. Cancellation of the representing monomorphism shows that `f` followed by
the actual torus factor into `L` equals `a`. The selected roots are actual
roots of that torus in `L`, by the dynamic Lie premise and actual tangent
lifting. The central-root restriction theorem then makes their restrictions
to the split torus `A` zero.

Associativity of composition gives vanishing of the actual integral pairing
on every cocharacter in the image of `f`. Tensor induction extends this to
containment of the entire real cocharacter image in `rootAnnihilator T J`.
`standardLeviCentralDirectionsMap` restricts the codomain of the actual
`cocharacterMapReal f` to this annihilator; its coercion formula preserves
the original real map.

The scope includes arbitrary universes and fields, nonreduced relative roots,
empty selections and rank zero. It assumes no reductivity of `L`, genericity
of `ν`, finiteness of `J`, or existence of a standard cocharacter. The actual
map `f` and its composite equality are supplied, so this construction proves
neither their existence, injectivity, nor equality of the real image with
the annihilator. Those remain separate obligations of the full standard-Levi
central-directions target.

Provenance: this is a derivation from the published point, weight, pairing
and real torus constructions, using the explicit dynamic Lie premise and
the supporting selected-root and central-root restriction results.
