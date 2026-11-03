# Reduction of proper Borel quotients to orbit, stabilizer and flag prerequisites

Worker 1396.

`SchemeAction.act_eq_act_iff` shows that for an action `a`, test points
`g h : T ⟶ G.X` and `x : T ⟶ X`, `a.act g x = a.act h x` exactly when
`a.act (g⁻¹ * h) x = x`. The proof cancels `g` using `act_mul` and `act_one`.

`someBorelQuotientProper_of_prerequisites` proves
`SomeBorelQuotientProperStatement.{u}` from three propositions:
`GeneralLinearSolvableStabilizerStatement`, `ClosedOrbitStatement` and
`SolvableProperFixedPointStatement`. It uses the Library theorems
`orbitMapFaithfullyFlat` and `finiteIndexQuotientProperTransfer`, and two proved
helper results from the modules `StabilizerClosedSubgroup` and `ReducedSubgroup`
(Worker 1399): `SchemeAction.exists_isClosedSubgroup_stabilizer` and
`ReducedSubgroup.exists_reducedIdentityComponent`. It does not use Borel conjugacy or
dimension theory, and any Borel subgroup works.

The proof runs as follows. Fix an algebraically closed `k` and a smooth,
affine, connected group scheme `G` over `Spec k`.

1. `BorelExistence.exists_isBorelSubgroup` gives a Borel subgroup `i : B ⟶ G`.
   `affineLinearEmbeddingStatement` gives a homomorphism `ρ : G ⟶ GL_N` whose
   underlying map is a closed immersion.
2. The flag proposition gives a nonempty proper `X` with an action `a` of
   `GL_N`. The closed-orbit proposition, applied to the restricted action
   `a.restrict ρ`, gives a reduced closed subscheme `j : O ⟶ X` with an
   equivariant action `b` of `G`, transitive on rational points. `O` is proper
   because `j` is a closed immersion into a proper scheme.
3. `B` is smooth, connected and solvable, and is affine because its closed
   immersion into `G` is affine. The fixed-point proposition gives a rational
   point `y` of `O` fixed by `b.restrict i`.
4. `O` is separated because it is proper, so
   `SchemeAction.exists_isClosedSubgroup_stabilizer` gives a closed subgroup
   `iS : S ⟶ G` whose points on every test scheme are exactly the points of
   `G` fixing `y`. Since `B`
   fixes `y`, the range of `i` lies in the range of `iS`.
5. `ReducedSubgroup.exists_reducedIdentityComponent` (the identity component
   of `S_red`) gives a smooth connected closed
   subgroup `f ≫ iS : H ⟶ G` with `f : H ⟶ S` of open image. Every smooth
   connected closed subgroup inside `S` factors through it, so `i = e ≫ f ≫ iS`
   for some `e : B ⟶ H`.
6. `H` fixes the rational point `y ≫ j` of `X` under `a.restrict (f ≫ iS ≫ ρ)`.
   This follows from the equivariance of `j` and the stabilizer description.
   The composite `f ≫ iS ≫ ρ` is a closed immersion, so the flag proposition
   makes `H` solvable. Maximality of `B` then makes `e` an isomorphism, and the
   ranges of `i` and `f ≫ iS` agree.
7. Rational transitivity from the original point yields rational transitivity
   from `y`. The theorem `orbitMapFaithfullyFlat` then makes the orbit map at `y`
   flat, surjective and quasi-compact. By `act_eq_act_iff` and the stabilizer
   description, two points have equal images under the orbit map exactly when
   their quotient lies in `S`.
8. For any quotient `q : G.X ⟶ Q` as in the target, the theorem
   `finiteIndexQuotientProperTransfer`, applied to `S`, `H` and the proper `O`, makes `Q` proper. Its
   hypothesis on `q` holds because the ranges of `i` and `f ≫ iS` agree.

## Provenance

This is a derived route to Milne, *Algebraic Groups* (2017), Theorem 17.9(a),
printed p.354 (PDF p.370), source `milne-2017-algebraic-groups`. Milne takes a
Borel subgroup of maximal dimension, realizes it as a line stabilizer by
Chevalley's theorem 4.27, and uses Lie–Kolchin and the closed-orbit lemma 1.66 in
the variety of maximal flags. The proof here avoids Chevalley's theorem and
dimension counting. It takes an arbitrary Borel subgroup, a closed orbit in a
proper `GL_N`-scheme with solvable point stabilizers (supplied by
`GeneralLinearSolvableStabilizerStatement`, whose intended witness is the full
flag scheme of Milne 7.29–7.30), and a fixed point of the Borel subgroup on that
orbit, as in the Borel fixed point theorem, Milne Corollary 17.3, printed p.353
(PDF p.369). Maximality of the Borel subgroup then identifies it with the
reduced identity component of the stabilizer. The three propositions are
hypotheses of this theorem and are not proved here.
