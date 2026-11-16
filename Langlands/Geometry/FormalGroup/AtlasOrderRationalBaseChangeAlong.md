# Full-order rational atlas maps over supplied scalar structures

This is internal infrastructure derived from `AtlasOrderRationalBaseChange`,
`AtlasOrderBaseChangeAlong` and `AtlasRationalBaseChangeAlong`. It introduces no
additional original-literature assertion.

Let `O`, `R` and `S` be commutative rings, with specified `O`-algebra structures
where used. Let `D` be a ring with central `O`-algebra structure, and let `F` be a
field with an `O`-algebra structure. The coordinate types are finite and may
differ, and the original atlases have supplied equalities of their principal
covers. Coefficient rings and tests have the same universe. No division,
maximal-order or invariant hypothesis on `D` is needed for this construction.

Full-order rational Hom is the existing chartwise centralizer inside the
actual global tensor `F ⊗[O] BasicAtlas.Hom`. Its equations commute with every
element of `D` as actual rational formal chart maps. It is not defined by
tensoring integral full-order Hom.

For equal `O`-algebra structures `α` and `β` on `R`,
`OrderAction.RationalHom.reAlgebra` is an `F`-linear equivalence of the actual
centralizers, with the atlases and their order actions transported along the
equality. Equality elimination reduces its construction to the identity
equivalence. The `reAlgebra_val` theorem identifies its underlying global tensor
map with ambient scalar transport. The remaining transport theorems preserve
integral rationalization, the rational identity and actual composition, and
identify reflexive transport with the identity on every rational map.
The helper `BasicAtlas.reAlgebraOpens_eq` records the retained cover equality
with both transported atlases specified.

For an `O`-algebra homomorphism `f : R →ₐ[O] S`,
`OrderAction.RationalHom.baseChangeAlong` first applies actual full-order
rational coefficient extension to `coefficientTest f`, then transports the
result to the supplied `O`-algebra structure on `S`. The scalar structures are
equal by `coefficientAlgebraAlong_eq f`, using `f.commutes`. The target actions
are exactly `E.baseChangeAlong f` and `E'.baseChangeAlong f`, on the existing
supplied-target atlases. Their covers are image covers with the existing
selected preimage generators; noninjective coefficient maps are allowed.
`BasicAtlas.baseAlongOpens_eq` records equality of these image covers from the
supplied original equality, by the existing `baseOpens_eq` theorem.

The map is `F`-linear. `baseChangeAlong_val` proves that forgetting order
commutation gives precisely ambient supplied-target extension. The
rationalization, identity and composition theorems follow by the corresponding
ambient full-order extension laws and equality-transport laws.
`baseChangeAlongRingHom` bundles the endomorphism case with composition as
multiplication and the actual rational formal identity as one.

When `O` is additionally a domain and `F` its fraction field,
`OrderAction.QuasiIsogeny.baseChangeAlong` extends both stored full-order
rational maps. Preservation of identity and composition proves both inverse
equations. The field lemmas identify the forward and inverse maps. The
forgetful theorem recovers exactly ambient supplied-target quasi-isogeny
extension. Extension preserves `refl`, `symm`, `trans` and rationalization
`ofIso` of an actual integral full-order formal isomorphism. Forward-map
extensionality reduces these claims to the rational extension laws and the
existing identification of the extended integral isomorphism's forward map.

The construction retains global finite tensor sums and the supplied scalar
structure. It asserts no injectivity, surjectivity, independence of chosen
generators, successive-extension coherence, local rational gluing, heights,
framing, polarization, descent, levels or representability.
