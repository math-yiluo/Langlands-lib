# Normal-factor retractions from the structural complement proposition

Authors: Worker 1356; Worker 1326 (consumer interface); Worker 1371
(structural complement interface).

This is a conditional internal construction. It takes an explicit proof
`hComplement : SemisimpleNormalIsogenyComplementStatement.{u}`. It does not
prove that proposition or the unconditional anisotropic-factor centralizer
statement.

For any field `k : Type u`, let `G` be simply connected and let
`j : H ⟶ G` be a closed inclusion with smooth connected source and normal
all-test range. The theorem
`IsSimplyConnected.exists_normalFactorRetraction_of_complement` supplies a
group-scheme homomorphism `p : G ⟶ H` satisfying:

- `j ≫ p = 𝟙 H`.
- For every test scheme `T`, every `h : T ⟶ H.X` and every `g : T ⟶ G.X`,
  if `g ≫ p.hom.hom = 1`, then `Commute (h ≫ j.hom.hom) g`.

The actual chosen homomorphism is
`IsSimplyConnected.normalFactorRetraction`. The section identity and
pointwise kernel commutation are exposed by
`IsSimplyConnected.comp_normalFactorRetraction` and
`IsSimplyConnected.commute_of_comp_normalFactorRetraction_eq_one`.
The choice is not asserted to be canonical or independent of the supplied
proof and subgroup data.

## Implemented argument and provenance

Apply the structural complement proposition to `j`. It supplies an actual
complement `K`, its inclusion `i`, a semisimple product `H ⊗ K`, all-test
commutation `hc`, and a central isogeny
`commutingSubgroupMultiplicationHom j i hc : H ⊗ K ⟶ G`.
The defining property `IsSimplyConnected.central_isogeny_isIso` makes this
actual homomorphism an isomorphism. The construction and theorems of
`CommutingFactorRetraction` then provide a projection, its section identity
and its kernel commutation. Classical choice selects one of the projections
with those proved properties.

This module derives its result from the published constructions and the
explicit structural premise. Its route does not require a separate
multiplication-isomorphism adapter or reflection of simple connectedness
to the factor. No extra field, perfectness, splitness, characteristic or
isotropy restriction is introduced. Applying this construction to an
almost-simple subgroup uses its semisimplicity to obtain smoothness and
connectedness. To close the unconditional centralizer target, a proof of
the structural complement proposition remains necessary.
