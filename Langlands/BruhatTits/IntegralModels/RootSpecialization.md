# Supplied integral root models and their actual residue roots

This is an internal structural interface for the unramified root-direction
descent program. It combines the Library's actual integral models, integral
tori, character specialization, all-test root subgroups and represented fppf
quotients. It asserts no existence theorem for these data and no descent
statement. Its provenance is this combination of existing definitions,
rather than a claim to translate a numbered literature assertion.

Let `R` be a local domain with fraction field `K`, in an arbitrary universe.
Fix a supplied relative-component model `D` of `G`, an actual integral torus
`T` with generic fibre `S` and map `i : S → G`, and a proof `hT` that the
integral torus is split. Fix supplied special-fibre quotient data `Q` for `D`
and a generic character `a` of `S`.

`IntegralRootSpecializationData T hT Q a` retains:

- An actual generic group, a map representing `RelativeRoot.subgroup i a`
  on every test scheme, a smooth integral model of that group, and a
  compatible integral-model map into `D.neutral`.
- An actual affine residue group, a projection from the root model's
  actual special fibre, and an inclusion into `Q.quotient`. Their composite
  equals the root model's actual map to the neutral special fibre followed
  by `Q.projection`.
- Root membership of `T.characterSpecialization hT a` for the actual map
  `T.specialFibreInclusion ≫ Q.projection`, and representation of that
  all-test residue root subgroup by the supplied residue inclusion.
- An actual smooth closed split-unipotent kernel subgroup and the
  represented fppf quotient property for the supplied residue projection.

The residue ambient group is `Q.quotient`; the residue root group is a
separate group included in it. The character comparison is the canonical
one through the same split integral torus, not a freely chosen lattice map.
The quotient data alone do not assert `Q.IsReductiveQuotient`, torus
maximality, or model existence; a consumer needing those properties must
supply them separately. No value function or integral-point filtration is
part of this geometric interface.

`RepresentsIntegralRoot` records a separate, stronger property: the model's
map into the neutral model represents the all-test root functor for the
integral character `(T.genericCharacterEquiv hT).symm a`. This property is
not included in the data and is not proved here. In particular, the
generic representing property, a compatible model map, or an equality of
integral-point images does not silently imply it.

`reduction_comm` is the implemented consequence of the supplied commutative
square. Naturality of reduction for the integral-model map, associativity,
and `residue_comm` identify the included residue-root image of a reduced
section with its actual image in the neutral special-fibre quotient.
