# Ordinary dynamic cells for a fixed lifted reflection

This internal construction converts the fixed translated cell from
`DynamicReflectionNormalizerLift` into ordinary opposite-unipotent/parabolic
coordinates. All schemes and fields have arbitrary universe `u`. The field-level
construction retains the perfect field, affine source, actual fppf quotient
with a represented smooth connected closed unipotent kernel, connected reductive
quotient and maximal split quotient torus hypotheses of that input. The actual
quotient conjugation action descends through the given original character,
which pairs positively with the cocharacter. The positive dynamic subgroup is
assumed nontrivial. The original character need not be an actual root.

`IsNormalizingPoint.comp_hom` first transports a supplied normalizing equation
through any group-scheme homomorphism over the same base. The source point's
image normalizes the image torus map through the same torus automorphism. This
follows from the naturality of actual inner automorphisms; it makes no
injectivity or quotient assumption.

`dynamic_conj_opposite_mem_unipotent_of_cyclic_support` works over any field
with a smooth affine ambient group and a monic split-torus map having a
relative root system. Every actual root is assumed to be an integral multiple
of the original character. The selected indivisible positive root identifies
the dynamic groups on every test scheme. Since a supplied normalizer negates
the original character, additivity makes it negate the selected root.
Normalizer conjugation of actual root subgroup functors therefore sends
`U(-ν)` into `U(ν)`, on every test scheme.

`dynamicReflectionCellNormalizerLift` retains the exact source point and torus
automorphism chosen by `dynamicReflectionNormalizerLift`, including their
normalizing equation and negation of the original character. The same choice
works for every later nonidentity quotient point `x` in `U(ν)`:

`x * q(m)⁻¹ = y * v`, with `y` in `U(-ν)` and `v` in `P(ν)`.

The implementation derives cyclic root support from the descended action and
applies the preceding conjugation lemma to the image of this same normalizer.
For the translated coordinates `x = y * z * q(m) * w`, it takes
`v = z * (q(m) * w * q(m)⁻¹)`. Both factors of `v` belong to `P(ν)`,
by the dynamic centralizer and unipotent inclusions.

These are internal consequences of the named Library constructions, without
an additional literature assertion. This unit supplies field-level coordinates;
it does not assert integral lifting or integrality of prescribed opposite
factors and does not prove the host fixed-point theorem.
