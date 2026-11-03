# Canonical relative projective coordinate sections

For every scheme `X` in universe `u`, natural number `n`, and
`j : Fin(n+1)`, `basisSection n X j` is an actual morphism
`X → RelativeProjectiveSpace X n`. There are no affineness, reducedness,
nonemptiness or field hypotheses.

The construction uses the existing coordinate point in polynomial
projective space over `Γ(X,⊤)`, where the coefficient algebra is the
identity. Its structural composite is `X.toSpecΓ`. The existing
`liftOverPolynomial` therefore lifts this point with base component
`𝟙 X` to relative projective space. The two projection identities
`basisSection_toBase` and `basisSection_toPolynomial` state respectively
that its base component is the identity and its polynomial component is
the coordinate point.

`basisSection_naturality` holds for every scheme morphism `f : Y → X`:

`f ≫ basisSection n X j = basisSection n Y j ≫ RelativeProjectiveSpace.map n f`.

The proof compares base and polynomial projections. The polynomial
projections with coefficient rings `Γ(X,⊤)` and `Γ(Y,⊤)` are related
by the coefficient map induced by `f.appTop`; the required compatibility
of structural maps is the naturality of `toSpecΓ`. Source naturality
and coefficient restriction of the actual polynomial basis points then
identify those projections.

For every invertible `Γ(X,⊤)`-linear coordinate map
`e : (Fin(n+1) → Γ(X,⊤)) ≃ₗ[Γ(X,⊤)] (Fin(n+1) → Γ(X,⊤))`,
`basisSection_globalLinearAction_eq_iff` states

`basisSection n X j ≫ globalLinearAction n e = basisSection n X j`

if and only if there is a unit `u : Γ(X,⊤)ˣ` with
`e(Pi.single j 1) = u • Pi.single j 1`.
This is equality of actual scheme morphisms, equivalent to a single
global unit scaling the whole basis vector. It is not a condition only on
field-valued or reduced test points. Base and polynomial projections
detect equality, and the global action induces the existing polynomial
linear action on that projection. The polynomial basis-point scalar-unit
criterion, with identity coefficient algebra, proves the equivalence.

This is internal content derived from the existing relative pullback model,
the polynomial coordinate-point and restriction lemmas, and the proved
polynomial scalar-unit criterion. It supplies the geometric section and
comparison required by the projective-orbit route. It does not construct
the representation with a prescribed stabilizer, nor prove homogeneous
quotient existence.
