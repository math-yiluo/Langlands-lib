# The adjoint torus of a relative Borel as a finite étale Weil torus

`Langlands.GroupScheme.RelativeBorelAdjointTorusWeilPresentationStatement.{u}`
is a proposition definition. This module states a focused prerequisite; it
does not prove it.

For every commutative ring `R`, let `G` be reductive over `Spec R`, let
`i : B ⟶ G` be a relative Borel subgroup, and let `T` be a commutative
group scheme with `t : T.toGrp ⟶ B`. Assume that `T` is a relative torus
and that the composite `t ≫ i` is a closed, fibrewise maximal torus of
`G`. For any supplied group scheme `D` and homomorphism `q : T.toGrp ⟶ D`
which is a full fppf quotient by

`(center G).comap (t ≫ i)`,

the statement asks for a commutative `R`-algebra `E` which is finite,
projective and étale over `R`, together with an actual group-scheme
isomorphism

`D ≅ WeilGm.groupScheme (CommRingCat.of R) E`.

The quotient predicate means that `q` is flat, surjective and locally of
finite presentation and that its full scheme-theoretic kernel has exactly
the specified subgroup functor on every test scheme. It does not require
surjectivity on each original test's group of points. The kernel uses the
whole ambient centre, including any nonsmooth part. Its inverse image in
`T` is the centre of `G` viewed inside this maximal torus; maximal tori in
reductive groups contain the full centre.

The target of the isomorphism is the existing represented Weil restriction
of the multiplicative group. On every test `Z` it has points naturally
identified with `(E ⊗[R] Γ(Z, 𝒪_Z))ˣ`. Projectivity is recorded explicitly
because this constructor takes a finite projective coefficient algebra;
it is a standard consequence of finite étaleness. The statement requires
neither a field nor semi-locality. It imposes no affineness hypothesis on
`D` and asks for an isomorphism of the supplied quotient itself.

The coefficient algebra is not required to be nonzero or faithfully flat.
When the root system is empty, `G` is a torus and its adjoint torus is
trivial; the finite étale scheme indexing the simple roots is then empty,
and its coefficient algebra is the zero ring. Ranks may also vary over
open and closed components of `Spec R`.

## Provenance and mathematical reduction

This is a derived statement motivated by Brian Conrad, *Reductive group
schemes* (2014), Proposition 7.2.11 and its proof, printed/PDF page 258.
The source constructs a particular quasi-split inner form with
`T'/Z(G') ≅ R_{S'/S}(Gm)`. Its proof identifies a split adjoint torus with
the product of copies of `Gm` indexed by the simple roots, and twists the
simple-root set by diagram permutations. The universal assertion for a
supplied Borel and maximal torus here is a derived extension of that
argument, not a verbatim assertion of the proposition.

The proposed reduction is as follows. Étale-locally, split the reductive
group together with its supplied Borel and maximal torus. On a split pair,
the simple roots form a basis of the adjoint torus's character lattice,
so evaluation on them identifies its full central quotient with the
corresponding product of multiplicative groups. Changes of splitting
which preserve the Borel and torus permute the simple roots. Their toral
inner part acts trivially on the torus, so the quotient descent maps are
precisely these coordinate permutations. The finite locally constant
simple-root sheaf is represented by a finite étale scheme over `Spec R`;
quasi-compactness permits varying finite ranks on finitely many open and
closed pieces. Its coordinate algebra is `E`. Descent of the products
identifies the quotient with `Res_{E/R} Gm`. Uniqueness of represented
full fppf quotients transfers this identification to the supplied `D`.
Establishing this reduction in Lean is the separate proof obligation.

The result isolates the torus presentation needed for the proof of
Conrad's Proposition 7.2.12, pages 258–259. It supplies no quasi-split
inner-form existence, adjoint-quotient representability, radical series,
cohomology vanishing or uniqueness theorem. In particular, a finite
étale Weil presentation is a conclusion to prove, not an additional
hypothesis on the unchanged semi-local inner-form target.
