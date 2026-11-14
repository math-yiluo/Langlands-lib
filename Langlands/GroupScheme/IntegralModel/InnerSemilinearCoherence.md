# Coherence of inner-twisted coefficient comparisons

This is an internal construction derived from the existing coefficient
comparison, inner-automorphism naturality, and integral generic-rigidity APIs.
All schemes and coefficient types have arbitrary common universe `u`.

For fields `k ⊆ L` and a group scheme `G` over `k`, write `G_L` for its specified
base change. The generic comparison `innerGaloisDescentIso` first applies the
canonical coefficient comparison for `σ`, then conjugates by an actual point
`x ∈ G_L(L)`.

The two existing conventions `baseChangeSectionHom` and `baseChangeBasePoint`
for pulling back a base section agree definitionally. The helper
`galoisDescentIso_baseChangeBasePoint` identifies the image of that pulled-back
point under the named canonical comparison with `rationalConjugate σ x`.
Its proof uses the published map-level equality for `galoisDescentIso` and the
published coefficient-transport formula.

The theorem `innerGaloisDescentIso_tower` assumes the actual scheme-map identity
`vσ ≫ vτ = vυ` and the point identity
`z = x * rationalConjugate σ y`. It proves the exact tower law, including the
canonical iterated-pullback comparison:

`comparison ≪≫ inner(υ,z) = baseChange(vσ)(inner(τ,y)) ≪≫ inner(σ,x)`.

The proof pulls the inner automorphism through base change using
`baseChange_innerIso_hom`, then through the coefficient comparison using
`innerIso_hom_comp`. Both imported identities are proved on every test scheme.
The transported-point formula and `innerIso_mul_hom` combine the conjugators
in the displayed order. The published coefficient-only tower law finishes the
equality of the actual group-scheme maps.

For the integral construction, `R` is a domain with specified fraction field
`L`, and `P` is a supplied smooth integral model of `G_L`. An indexed family of
invertible integral base maps `a i` is supplied with coefficient automorphisms
`σ i` and conjugators `z i`. The integral and generic maps commute with the
generic inclusion. A composition index `m` satisfies the two actual base-map
composition laws and
`z (m i j) = z i * rationalConjugate (σ i) (z j)`.
The premises also include `HasSmoothHomExtension` and preservation of
`P.integralPoints` by both the inner-twisted coefficient map and its explicit
inverse, for every index. These are the hypotheses of `innerGaloisTwistIso`;
none is inferred from a mere equality on rational points.

The theorem `innerGaloisTwistIso_tower` proves the corresponding integral tower
law for those constructed isomorphisms. It supplies their full generic
compatibility squares and the generic tower law to
`semilinear_tower_of_generic`, whose generic-rigidity argument proves equality
of the integral scheme maps.

The definition `datumOfStableInnerGaloisPoints` further assumes a map
`p : Spec R ⟶ B` with a supplied finite normalized component cover of its
overlap: the maps `q i` have first projection the identity, second projection
`a i`, and their coproduct is an isomorphism. It constructs an actual
`Descent.Datum p P.group` by `datumOfGenericSemilinear`.
The theorem `pullIso_datumOfStableInnerGaloisPoints` proves that every supplied
normalized component recovers the constructed integral isomorphism.

This unit constructs coherent Čech data from the supplied model, extension,
stability, and cover hypotheses. It does not construct any of those inputs,
prove effective descent, or assert the finite-field quotient, Frobenius,
or chamber witnesses required by the host task.
