# Rational conjugacy of minimal pseudo-parabolic subgroups

Author: Worker 1335.

`Langlands.GroupScheme.MinimalPseudoParabolicConjugacyStatement.{u}` states
Theorem C.2.5 of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), printed p.595 (PDF p.621). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
This is a proposition definition, not a proof of the theorem.

For every field `k : Type u`, the statement takes an actual group scheme
`G` over `Spec (CommRingCat.of k)` and explicitly assumes that its structure
morphism is smooth and affine and that its underlying space is connected.
For any two actual group schemes `P,Q` over the same base and homomorphisms
`i : P ⟶ G` and `j : Q ⟶ G`, it assumes
`IsMinimalPseudoParabolicSubgroup i` and
`IsMinimalPseudoParabolicSubgroup j` and concludes `SubgroupConjugate i j`.
The universe `u` is arbitrary. The field, all group schemes and their
relative test schemes lie in this single universe.

The imported minimality predicates require actual pseudo-parabolic
subgroups and minimality among their contained all-test images over `k`.
The pseudo-parabolic predicate retains the ground-field unipotent radical
in its represented fppf-local dynamic-parabolic product. It supplies
closedness of both inclusions. Smoothness and connectedness of their
sources are not extra hypotheses of this statement.

By the published definition of `SubgroupConjugate`, the conclusion means
that there are a rational point
`g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X` and an actual group-scheme
isomorphism `e : P ≅ Q` such that
`i ≫ (G.innerIso g).hom = e.hom ≫ j`.
Thus conjugation by a single point in `G(k)` identifies the actual
subgroups, including their scheme structures, on every test scheme.
This is the source's rational subgroup conjugacy, with an explicit
isomorphism because Lean allows different source objects for the two
inclusions. The orientation of conjugation does not restrict the source
assertion, since rational points have inverses.

No reductivity, pseudo-reductivity, splitting, perfection, infinitude or
characteristic restriction is imposed on the ambient group or field.
The statement neither constructs a minimal pseudo-parabolic subgroup nor
asserts the reflection representative needed by downstream rank-one
arguments.
