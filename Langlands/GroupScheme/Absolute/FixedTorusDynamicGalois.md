# Galois action on actual fixed-torus dynamic presentations

Worker 1270. This is an internal construction from the actual lattice Galois
representation, the subtype `FixedTorusDynamicPresentations`, and the naturality
and subgroup-functor formulas for canonical descent transport.

For arbitrary schemes `b : S → B` and `a : S → S` with `a ≫ b = b`, a commutative
group scheme `T` over `B`, a group scheme `G` over `B`, and a homomorphism
`j : T.toGrp → G`, `cocharacterLattice.groupHom_transport_comp` proves that
transporting a cocharacter of `T_S` and then composing with `j_S` agrees with
transporting the ambient composite. The proof combines the definition of
lattice transport with the naturality of cocharacter transport.

`Dynamic.parabolic_torus_transport_eq_baseChange` says that if this ambient
cocharacter defines the pullback of a subgroup functor `F` over `B`, each such
transport defines the same pullback. It follows by the preceding morphism
equality and the generic dynamic descent-transport comparison. This is equality
of subgroup functors on every scheme over `S`.

Now let `K/k` be any extension of fields in universe `u`, and take `T`, `G`,
`j`, and a homomorphism `i : P → G` over `k`. The theorem
`fixedTorusDynamicPresentation_galois` applies that comparison to `Spec σ` for
each `σ : K ≃ₐ[k] K` and uses base change of ranges. It proves that every Galois
translate of a cocharacter of `T_K` presenting the range of `i_K` is another
presentation of that same range.

The definition `fixedTorusDynamicPresentationGaloisAction` restricts the published
lattice Galois action to this actual subtype of presentations. Its action sends
`ν` to the same lattice element as `cocharacterLattice.galoisRepresentation σ ν`.
The preceding theorem supplies its subtype property; the identity and
composition laws follow from the representation laws and subtype extensionality.

No splitness, torus property, affineness, closed immersion, smoothness,
connectedness, reductivity, finiteness, normality or separability hypothesis is
used. The extension can be infinite. The presentation subtype may be empty.
This constructs the Galois action on individual presentations. It does not
assert that a presentation exists or that a sum of presentations is a
presentation; those require separate structural and sign arguments.
