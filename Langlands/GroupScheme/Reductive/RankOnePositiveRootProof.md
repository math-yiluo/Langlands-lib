# Uniqueness of the positive root in semisimple rank one

Worker 1549 assembles the final proof from the published projective Borel
route developed with Workers 1547, 254, 1162 and 317. The imported centralizer,
quotient, fixed-point and transport results retain their own authorship.

`Langlands.GroupScheme.rankOnePositiveRootUniqueness` has exactly the type
`Langlands.GroupScheme.RankOnePositiveRootUniquenessStatement.{u}`.
It has no additional structural premise. The field `k : Type u` is arbitrary,
including finite and imperfect fields, and its characteristic is unrestricted.
For every connected reductive `G`, split maximal torus `i : T.toGrp ⟶ G`,
and cocharacter `ν`, pairwise integral dependence of the actual roots implies
that any two roots positive on `ν` are equal. Positivity is the strict
inequality in `ℤ` given by `latticePairing T`; the cocharacter need not be
regular or nonzero. Roots are the nonzero characters occurring in the actual
adjoint Lie algebra, with the meaning of the unchanged published target.

## Implemented proof

The proof supplies the sole remaining premise of
`rankOnePositiveRootUniqueness_of_projectiveBorelInputs`, namely
`AlgClosedMaximalTorusCentralizerStatement.{u}`. It applies the published
`algClosedMaximalTorusCentralizer_fromQuotient` to the unconditional proofs
`dynamicCentralizerReductive` and `solvableTorusQuotient`.

That centralizer assembly works over an algebraically closed field.
A generic cocharacter realizes the whole-torus centralizer as a dynamic
centralizer, whose closed representative is connected reductive by the
first supplied proof. The original maximal torus factors through this
representative as a central maximal torus. Its quotient has no nontrivial
closed torus, and the published algebraically closed no-torus theorem
makes that quotient unipotent. Solvability and the second supplied proof
then give a normal unipotent subgroup with split torus quotient.
Reductivity kills the unipotent subgroup, and maximality makes the original
central torus inclusion an isomorphism. This proves
`torusCentralizer i = SubgroupFunctor.range i` on every relative scheme test,
including nonreduced tests. No arbitrary-field no-torus theorem is required.

The projective Borel reduction now applies. Over the algebraically closed
field, a root supplies a proper Borel containing the specified torus.
Published solvable maximal-torus conjugacy applies inside this Borel.
Self-centralization and the actual torus factorization give containment of
the whole-torus centralizer in the Borel on every test scheme. The published
solvable proper fixed-point theorem constructs an actual proper quotient
with smooth, surjective, quasi-compact projection and the exact right-coset
fiber law. Its equivariant projective embedding and the published projective
torus fixed-point dimension theorem, together with the rank-one fixed-point
sign embedding, force quotient dimension at most one.

The same rooted quotient construction supplies a nonidentity normalizer
class. Regular integral refinement and normalizer symmetrization preserve
positivity on the original cocharacter. The published quotient-curve
argument bounds the relevant dynamic tangent dimension and proves equality
of the two positive roots. These steps divide by no integer. Root membership
in the target supplies the needed root; when there are no positive roots,
the universally quantified implication needs no separate existence hypothesis.

Finally, the reduction pulls the actual group, torus inclusion, characters
and cocharacter back to `AlgebraicClosure k`, which remains in `Type u`.
Published connected reductivity, split-torus and maximal-torus base-change
theorems preserve the geometric hypotheses. The actual character-lattice
equivalence preserves and reflects root membership and integral dependence,
and preserves the integer pairing exactly. It therefore reflects the
algebraically closed equality back to `k`. Every input of this reduction is
supplied by a published theorem.

## Source and route comparison

The source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, content SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Proposition 20.11, printed pp.410–411 (PDF pp.426–427), gives the torus
fixed-point lower bound for a stable projective subvariety.
Corollary 20.12, printed p.411 (PDF p.427), transfers this bound to a complete
homogeneous quotient. Theorem 20.16, Section 20e, printed pp.412–413
(PDF pp.428–429), relates semisimple rank one, the two Borels through a
maximal torus, and the one-dimensional Borel quotient. The following
discussion on p.413 obtains the one-dimensional unipotent Borel subgroup.

The Lean proof uses the fixed-point and quotient-curve part of this geometry.
It constructs a prescribed Borel quotient and proves its dimension bound
directly from dependent actual roots and a sign embedding. It then uses
dynamic tangent bounds and integral normalizer symmetrization for root
uniqueness. It does not construct Milne's isogeny to `PGL₂` or identify the
unipotent Borel subgroup with `𝔾ₐ`. Explicit base-change equivalences supply
the all-field conclusion beyond the algebraically closed source passage.
The author's errata snapshot, source
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
contains no correction to these passages.

The final theorem is an internal composition of the named published proofs.
It changes neither the target pair nor any of its imported pairs. Its proof
uses none of `RegularCocharacterBorelStatement`, `ParabolicDynamicStatement`,
`RankOneSolvableObstructionStatement` or `RankOneBorelDynamicStatement`,
including proofs of those statements, and does not use
`RootReducednessStatement`.
