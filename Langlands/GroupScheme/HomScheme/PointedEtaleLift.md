# Pointed étale lifting of homomorphisms from split tori

Worker 598.

`HomScheme.exists_pointed_etale_lift` works over an arbitrary scheme `S` in
universe `u`. Given a split torus `H`, a smooth affine group scheme `G`, a point
`s : S`, and an actual homomorphism between their residue fibres, it constructs
an étale morphism `p : U → S`, a point `b : Spec κ(s) → U` over the canonical
residue point, and a homomorphism over `U` whose relative Hom evaluation at `b`
is the prescribed homomorphism.

`PointedEtaleHomLiftData` packages this neighbourhood, its étale projection,
the residue-valued point and its equation over `S`, and the lifted relative
homomorphism with its exact recovery equation. `pointedEtaleHomLift` chooses
such data using the existence theorem. This construction lets later arguments
refer to the lift and its comparison equations without unpacking an existential.

This is an internal consequence of the published smooth representability of
the relative Hom functor from a split torus and the published pointed étale
section theorem for smooth morphisms. No new literature assertion is used.
The proof represents the given homomorphism by a residue-valued point of the
smooth Hom scheme, applies the pointed section construction, then evaluates the
universal homomorphism along the resulting section. Evaluation under composition
proves exact recovery, including the actual base-change comparison maps.

The statement imposes no closed-immersion condition on the homomorphism. It
does not assert that a dynamic parabolic presentation in the residue fibre
remains a presentation over the neighbourhood.
