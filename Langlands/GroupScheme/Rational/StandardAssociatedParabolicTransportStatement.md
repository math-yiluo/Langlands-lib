# Whole standard families in associated Levis

This internal statement records the missing transport of the complete standard
parabolic and radical families between associated standard Levis. It uses the
published actual subgroup functors and finite Coxeter indexing. The structural
equalities are proof obligations.

Let `G` be a connected reductive group scheme over a field `k`, let
`i : T.toGrp ⟶ G` be a maximal split torus, and let `ν` be a generic cocharacter.
For a finite set `J` of the actual simple relative roots and `I : Finset J`,
`restrictedStandardParabolic i ν J I` is the intersection of `L_J` with the
ambient standard `P` indexed by the image of `I` in the actual simple-root type.
`restrictedStandardUnipotent` uses the ambient standard `U` in the same way.
These are subgroup functors on every test scheme, including nonreduced tests.
The names do not themselves prove that these intersections are the parabolic
and unipotent radical of a represented reductive Levi.

Fix a Coxeter system `cs` on the actual quotient
`relativeWeylGroup i = N(k)/Z(k)` with the published
`IsRelativeWeylCoxeterRealization i ν cs` property and finite enumerations of its
simple labels and its underlying group. Put `d = longestRep cs J` and
`K = associatedSubset cs J`. The literal published equivalence
`associatedFinsetEquiv cs J` sends `Finset K` to `Finset J`.
`IsStandardAssociatedParabolicTransport i ν cs` asserts, for every
`n : normalizerPoints i` with class `d` and every `I : Finset K`, the two
equalities

```
L_K ∩ P_I = comap(Int(n), L_J ∩ P_phi(I))
L_K ∩ U_I = comap(Int(n), L_J ∩ U_phi(I)),
```

where `phi = associatedFinsetEquiv cs J` and every subset is read in the
ambient simple-root type by its subtype embedding. Thus forward conjugation by
`n` carries the entire restricted source family to the target family.
The convention is `Int(n)(x) = n x n⁻¹`. No lift is chosen, and both empty
subsets and empty simple-root types are included.

`StandardAssociatedParabolicTransportStatement` quantifies this assertion over
every field at universe `u`, every connected reductive `G`, maximal split `i`,
generic `ν`, and every finite actual Coxeter realization. The finite
enumerations are required to form the existing `longestRep` and
`associatedFinsetEquiv`, and the statement quantifies every such enumeration.
Existence and finiteness of an actual Coxeter realization remain the separate
`RelativeWeylCoxeterStatement`. No characteristic, perfection, splitness of `G`,
quasi-splitness, local-field, reduced-test or smooth-centre hypothesis is imposed.
The full relative root system may be nonreduced.

The elementary theorem
`IsStandardAssociatedParabolicTransport.rationalPoints` evaluates supplied
functor equalities at `Spec k`. It applies `congrArg` to the actual rational-point
subgroup and then the published
`SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map`. Consequently the
source subgroup equals the target subgroup's image under conjugation by
`n⁻¹`. This is a conditional evaluation lemma; it proves neither structural
equality and introduces no comparison of sheaf quotients with point quotients.

The formulation comes from the actual associated-Levi transport interface
requested for the Aubert program. Standard-Levi transport alone identifies
only `L_K` with `L_J`. The separate
`StandardSourceTwistedIntersectionStatement` identifies minimum-double-coset
source intersections. The present target records transport of every restricted
positive family under the specified longest lift. It does not include the
outer ambient opposite-parabolic and opposite-radical identities or any
representation-theoretic comparison. The rational-point evaluation follows the
same elementary route as the source-intersection adapter.
