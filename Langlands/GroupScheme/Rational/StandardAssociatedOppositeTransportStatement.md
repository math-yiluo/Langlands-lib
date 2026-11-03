# Associated standard groups and ambient opposite groups

This internal statement records the outer ambient parabolic and radical
transport needed by the associated-Levi contragredient comparison. It combines
the published actual standard subgroup functors, relative-Weyl indexing, dynamic
opposite cocharacter and inner automorphism. Both structural equalities remain
proof obligations.

Let `G` be a connected reductive group scheme over a field `k`, let
`i : T.toGrp ⟶ G` be a maximal split torus, and let `ν` be a generic cocharacter.
Fix finite enumerations of the actual simple relative roots and actual relative
Weyl group, and a Coxeter system `cs` satisfying
`IsRelativeWeylCoxeterRealization i ν cs`. For a finite simple-root subset `J`,
put `d = longestRep cs J` and `K = associatedSubset cs J`. These are the
published longest representative in `D(J,∅)` and its inverse-image associated
subset; no replacement Weyl group or independent relabelling is introduced.

`IsStandardAssociatedOppositeTransport i ν cs` asserts, for every
`n : normalizerPoints i` of class `d` and every
`zeta : cocharacterLattice T` satisfying
`IsStandardCocharacter i ν (rootSet i ν J) zeta`, the equalities

```
P_K = comap(Int(n), Dynamic.parabolic(oppositeCocharacter(zeta ≫ i)))
U_K = comap(Int(n), Dynamic.unipotent(oppositeCocharacter(zeta ≫ i))).
```

Here `P_K` and `U_K` are the literal ambient `standardParabolic` and
`standardUnipotent` at `rootSet i ν K`. The notation `zeta ≫ i` means
`CommGroupScheme.groupHom zeta ≫ i`.
`Dynamic.oppositeCocharacter` precomposes this morphism by inversion on `G_m`.
Thus `Int(n)(x) = n x n⁻¹` carries the associated standard ambient groups to
the dynamic opposite groups for `J`. These are equalities of subgroup functors
on every test scheme, including nonreduced tests. They are not restricted
intersections inside a standard Levi. Both conclusions use the same actual
normalizer lift and standard cocharacter.

`StandardAssociatedOppositeTransportStatement` universally quantifies this
assertion over fields at universe `u`, connected reductive `G`, maximal split
`i`, generic `ν`, and every finite actual Coxeter realization. It derives the
affine and monomorphism instances from the displayed reductivity and
maximal-split hypotheses. It quantifies every finite enumeration, every lift
of `d`, and every standard `zeta`; it does not choose them. Existence and
finiteness of the Coxeter realization remain the separate
`RelativeWeylCoxeterStatement`, and existence of standard cocharacters remains
part of `StandardCocharacterStatement`. No characteristic, perfection,
splitness of `G`, quasi-splitness, local-field, nonempty-root, reduced-test or
smooth-centre hypothesis is added. The relative roots may be nonreduced.

The elementary theorem
`IsStandardAssociatedOppositeTransport.rationalPoints` applies `congrArg`
to evaluation of supplied functor equalities at `Spec k` and rewrites with
`SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map`. It identifies each
standard rational-point subgroup with the corresponding opposite subgroup's
image under conjugation by `n⁻¹`.
`IsStandardAssociatedOppositeTransport.mem_rationalPoints` instead rewrites
by the supplied equalities and applies
`SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom`. It gives membership
in `P_K(k)` or `U_K(k)` exactly when `n x n⁻¹` belongs to the respective
opposite subgroup. A consumer writing `g⁻¹ x g` takes `g = n⁻¹`.
Both are conditional evaluation lemmas, not proofs of the structural target.
They introduce no identification of sheaf quotients with quotients of points.

The provenance is the missing algebraic interface identified by the rational
Aubert consumers, using only the existing constructions. The dynamic
`inverseCocharacter` used in the consumer's `RationalOppositeParabolic` is
definitionally the same precomposition by inversion as the algebraic
`oppositeCocharacter` used here. Specializing these point equalities to the
consumer's named opposite subgroups is a separate adapter. The actual Levi
direction uses `StandardLeviConjugationStatement` and is not reproved or
assumed as part of this P/U proposition. The positive restricted-family
transport and the minimum-double-coset source intersections are distinct
targets. No representation-theoretic equality, induction-class compatibility,
represented-Levi construction or proof of the opposite structural identities
is supplied here.
