# Rational-point reduction for the simply connected centralizer product

Author: Worker 1627.

This internal construction works over an arbitrary field `k : Type u`. Its
objects and homomorphisms are the published actual group schemes, rational
points, dynamic subgroups and relative Weyl quotient. It adds no geometric
assertion about reductive groups.

For a homomorphism `i : S.toGrp → G` and any subgroup `H` of `G(k)`,
`subgroupRelativeWeylMap i H` is the homomorphism from `H ∩ N_G(S)(k)` to
the actual quotient `relativeWeylGroup i`. It is the subgroup inclusion
followed by the quotient projection. The theorem
`subgroupRelativeWeylMap_surjective_iff` identifies its surjectivity with
factorization of every normalizer point as an element of `H` times an
actual centralizer point. Equal quotient classes give the centralizer
factor by multiplying the inverse of the chosen representative.

`centralizerPoints_conj_mem_dynamicUnipotent` uses the published inclusion
of the whole-torus centralizer in every cocharacter centralizer, followed
by the published fact that Levi points normalize dynamic unipotent
points. It does not require a maximal or split torus.

Assume that `G` is affine, that a cocharacter `ν` has dynamic centralizer
equal to `torusCentralizer i`, and that
`HasRationalBruhatDecomposition i ν` holds. The theorem
`exists_unipotent_normalizer_unipotent_centralizer_mul` starts with
`g = p n q`. The actual rational-point Levi factorizations write
`p = a l` and `q = r b`. Conjugation by `n⁻¹` preserves the whole-torus
centralizer, so `z = n⁻¹ l n r` is in that centralizer. Conjugation by `z`
preserves the dynamic unipotent group. Consequently
`g = a n (z b z⁻¹) z`, with the asserted actual factor memberships.
Only the covering part of Bruhat is used.

`exists_subgroup_mul_centralizer_of_bruhat` additionally assumes that the
dynamic unipotent points belong to `H` and that `subgroupRelativeWeylMap`
is surjective. Write the normalizer factor as `n = m t` with `m ∈ H`
and `t` centralizing the torus. Moving `t` across the remaining unipotent
factor puts the entire first factor in `H`. This proof requires no
normality hypothesis on `H`.

`exists_cover_mul_centralizer_of_bruhat` takes
`H = range(rationalPoints.map (π ≫ d))` for supplied actual maps
`π : C → D → G`, together with a supplied representative `j : Z → G`
of `torusCentralizer i`. Membership in that range gives the actual point
of `C(k)`. The published `IsRepresentedBy.pointsEquiv` lifts the final
centralizer point to `Z(k)`. This yields the precise existential point
formula used by `SimplyConnectedCentralizerProductStatement`, conditional
on the stated Bruhat, unipotent-image and Weyl-surjectivity inputs.

The construction is derived solely from the named published interfaces
and elementary group rearrangements. It does not prove those structural
inputs, prove the unconditional centralizer-product target, or assert
surjectivity of `C(k) → D(k)`. There is no local-field, perfectness,
characteristic or finite-field restriction.
