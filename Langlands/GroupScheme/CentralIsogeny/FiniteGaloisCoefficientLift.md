# Simultaneous coefficient lifting through a central isogeny

Over a characteristic-zero field `k`, take a central isogeny and a
finite family of target points over a finite extension `L/k`.
`IsCentralIsogeny.exists_finiteGalois_coefficient_lifts` lifts all the
points over one finite Galois extension `E/k` containing `L`.

For each point, `coefficientLiftFiber` is the pullback of the
isogeny along that point. Its first projection is finite and
surjective over `Spec L`. A closed point gives a residue field finite over `L`.
Embed those residue fields into an algebraic closure of `L`, form
their finite compositum and take a finite Galois extension of `k`
containing this compositum. The residue-field morphism for each fibre
then gives the lift over `E` by pullback.

For a natural cocycle on a finite Galois cover, the coefficient
family is indexed by its finite Galois group. The values on the
refinement are extensions of the values at the restricted
automorphisms. Thus the simultaneous lifts give
`IsCentralIsogeny.GaloisLift` data on the refinement, including the
multiplication defect in the actual kernel. This is an internal
construction of the coefficient lifts used by the central
obstruction calculation.
