# A common finite field for exact model and inner-cocycle recovery

This internal construction combines exact finite unramified model recovery
above prescribed coefficients with scalar-tower cocycle recovery. Its inputs
and method come from the existing Library constructions; it asserts no
original-literature theorem. All fields and schemes have a common arbitrary
universe.

For a nonarchimedean local field `F`, let `K` be its actual inertia fixed
field in the chosen separable closure. An intermediate field `E` of that
separable closure is supplied with containment in `K`. All relative point
extensions use the algebra structure induced by this actual inclusion.

`mem_fixingSubgroup_of_restrictNormal_eq_one` assumes `E/F` normal and that
the image in the separable closure of a subfield `C` of `K` lies in `E`.
An automorphism of `K/F` restricting to one on `E` fixes each element of
`C`: regard its image as an element of `E` and use the restriction
commutation identity. Thus the automorphism belongs to `C.fixingSubgroup`.
The lemma needs no finite-degree assumption.

`restrictNormal_liftAutomorphism` proves that the actual selected lift
used by the finite integral constructions restricts to the supplied
`E/F` automorphism. It compares both maps after the injective field
inclusion, using `restrictNormal_commutes` and `liftAutomorphism_commutes`.

`HasFiniteInnerRecoveryAt` retains the supplied model `P`, its exact
`HasFiniteRecoveryAt` assertion and a genuine rational-point cocycle over
`E`. Extending the finite cocycle value at the restriction of any
`K/F` automorphism recovers the original cocycle value. In particular,
`recovery_at_liftAutomorphism` gives exact recovery at the chosen lift
required by the finite integral inner-descent construction.

`exists_common_finiteInnerRecovery` assumes a group scheme `G/F` with
affine underlying scheme, a supplied smooth integral model `P` of
`G_K` over the actual inertia integers, a rational-point cocycle `c`
on `Gal(K/F)`, and a finite subfield `C` of `K` on whose fixing subgroup
`c` is trivial. Map `C` into the separable closure. Its actual image is
finite-dimensional by the linear equivalence `IntermediateField.equivMap`
and lies in `K`.

Apply `finiteUnramifiedRecovery_above` to recover `P` exactly over a
finite Galois arithmetically unramified field `E` containing that image.
The fixing-subgroup lemma transfers the supplied finite triviality to the
kernel of restriction to `E`. Scalar-tower rational cocycle recovery then
gives the finite cocycle, its cocycle law and recovery at every upstairs
automorphism over the same actual field `E`.

The conclusion retains the prescribed generic identification of `P`.
It supplies neither a point-stabilizer model nor integral stability,
effectivity, residue, Frobenius, quotient or chamber data.
