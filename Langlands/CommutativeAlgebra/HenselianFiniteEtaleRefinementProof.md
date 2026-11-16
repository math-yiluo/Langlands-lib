# Finite étale local refinement over a Henselian local ring

The theorem
`Langlands.CommutativeAlgebra.henselianFiniteEtaleRefinement`
proves the unchanged
`Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementStatement`
in every universe `u`, with no additional hypotheses.

For a Henselian local commutative ring `R` and an affine étale morphism
`f : Spec A → Spec R` whose image contains the closed point, the theorem
provides a local commutative `R`-algebra `R'`, finite as an `R`-module and
étale over `R`, and an actual morphism `g : Spec R' → Spec A` satisfying
`g ≫ f = Spec.algebraMap R R'`. Neither Noetherianity nor a finite residue
field is required. The resulting local ring is nonzero.

The implemented proof applies
`henselianFiniteEtaleRefinement_of_ring` to the unconditional algebraic
construction
`HenselianFiniteEtaleRefinement.exists_local_finite_etale_refinement_via_weil`.
The bridge takes the ring homomorphism corresponding to `f`, equips `A`
with the corresponding `R`-algebra structure, and turns a point over the
closed point into a prime ideal `q` lying over the maximal ideal of `R`.

The algebraic construction uses the residue field `K` of `q`. Unramifiedness
makes `K` finite over the residue field of `R`. The imported finite étale
cover theorem supplies a local finite étale `R`-algebra `L` and a surjective
map `L → K`. The local unramified residue comparison identifies
`L ⊗[R] κ(R)` with `K` as `L`-algebras. The point of `A` extends to an
`L`-algebra map `L ⊗[R] A → K`, and hence to a point with values in
`L ⊗[R] κ(R)`.

The finite flat module `L` is free over the local ring `R`, so Weil
restriction along `L/R` applies. Smooth Weil restriction and Henselian
smooth lifting over `R` give an `L`-algebra map `L ⊗[R] A → L`.
Restricting it along `A → L ⊗[R] A` gives an `R`-algebra map `A → L`.
This step uses Henselianity of `R`; it requires no separate Henselian
inheritance theorem for `L`.

Finally, the bridge applies `Spec` to the resulting algebra map. Its scalar
compatibility is exactly the ring equation which, under contravariance,
gives the required factorization `g ≫ f = Spec.algebraMap R R'`.

This is an internal composition of the named Library results. The proof
uses finite étale covers and Weil restriction rather than the finite-part
decomposition described in the statement's source discussion. The statement
and its paired Markdown remain unchanged.
