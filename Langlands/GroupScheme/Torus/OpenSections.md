# Local sections of quotients by split tori

This is derived infrastructure for the full-center compactness proof. Work over
an arbitrary scheme `S : Scheme.{u}`, with group schemes `K`, `H`, `C`, an
inclusion `j : K ⟶ H` whose underlying morphism in `Over S` is a monomorphism,
and a homomorphism `q : H ⟶ C`. Assume that the range functor of `j` equals
the range functor of the actual kernel inclusion of `q`, on every test scheme.
Assume the underlying scheme map of `q` is affine, flat, surjective, and locally
of finite presentation, and that `K` is a split torus. No smoothness or
connectedness assumption is made on `H` or `C`.

`SplitTorusQuotient.LocalSection q y` stores an actual open neighbourhood `W`
of `y : C.X.left`, a scheme map `s : W.toScheme ⟶ H.X.left`, and the identity
`s ≫ q.hom.hom.left = W.ι`. The definition
`SplitTorusQuotient.localSection` constructs this data at every `y` under the
stated assumptions. The existence theorem `exists_localSection` exposes the
same result without making a choice.

The construction first transports the established cocycle trivialization from
the standard split-torus model to any group scheme satisfying `IsSplitTorus`.
`Cocycle.LocalTrivialization.of_map` composes the cochain with the inverse
isomorphism and transports its all-test coboundary identity.
`Cocycle.nonempty_localTrivialization_of_isSplitTorus` applies the actual
splitting isomorphism and the existing `Cocycle.localTrivialization`.

For the quotient section, base change to `C.X.left` and regard `H.X.left` as
the cover defined by `q`. Its universal point `F` gives a coboundary whose
image under the base-changed `q` is the identity. The exact kernel-range
assumption lifts that coboundary to a cocycle of the base-changed `K`, using
the existing kernel and base-change helpers in
`SplitUnipotentAffineTorsorProof`. Those helpers apply to arbitrary group
schemes and do not require the kernel here to be unipotent.

Trivialize this cocycle over a neighbourhood `W` of the given target point.
If `J` is the resulting cochain mapped into `H`, the corrected point is
`P = J⁻¹ * F` on the restricted cover. Its two pullbacks agree because the
coboundaries of `J` and `F` agree. Its image under `q` remains the restricted
cover map because `J` lies in the kernel. These identities hold on every
test scheme. The restricted affine flat surjective morphism, which is
locally of finite presentation, is an effective epimorphism. Applying
`EffectiveEpi.desc` to the corrected map constructs `s`; its factorization
law and epimorphic cancellation prove that `s` is a section over `W`.

Over any field `k : Type u`,
`SplitTorusQuotient.hasOpenSectionsAtPoints` proves precisely
`HasOpenSectionsAtPoints k k q.hom.hom`. The spectrum of `k` has one point,
so the whole image of each actual rational point lies in the neighbourhood
chosen for that point. The scheme section is a morphism over `Spec k`
because composing its section identity with `C.X.hom` gives its base
compatibility. This supplies the open-section input used by the existing
point-topology and full-center quotient-model constructions. The adapter
itself needs no topology on `k`.

The provenance is the internal derivation above, using the already established
unit-cocycle descent, split-torus point model, kernel/base-change helpers,
and effective-epimorphism descent. No additional external structural theorem
is assumed. This unit does not construct the algebraic full-center quotient,
prove that the full reductive center is of multiplicative type, establish the
quotient's anisotropy or compactness, or complete
`CenterSplitComponentCompactnessStatement`; those obligations remain.
