# The centralizer Levi of a maximal torus of a parabolic radical

Author: Worker 1355.

`ParabolicRadicalTorusCentralizerLeviStatement.{u}` is an unproved structural
proposition over every field in universe `u`. Let `G` be connected reductive,
let `j : P → G` be an actual rational parabolic, and supply an actual geometric
solvable radical `r : R → P`. For every commutative group scheme `S` and actual
maximal torus `sR : S → R`, the proposition asserts a group scheme `L` and a
morphism `l : L → P` such that `l` is a rational Levi and `l ≫ j` represents
the whole-torus centralizer of `sR ≫ r ≫ j` in `G`.

The radical and its maximal torus are premises; this proposition does not
construct them. `IsMaximalTorus sR` includes the torus property, closedness,
and maximality against every actual larger closed torus of `R`.
`IsGeometricSolvableRadical r` includes both ground-field and algebraic-closure
radical properties. Each radical is smooth, connected, solvable and normal,
and is greatest among actual smooth connected solvable normal closed
subgroups. Solvability uses geometric rational points, while normality and
containment use every relative test scheme.

`IsRationalLeviSubgroup l` includes affineness of `P`, closedness of `l`,
connected reductivity of `L`, and a represented geometric unipotent radical
whose multiplication with `L`, in Levi-first order, is an isomorphism of
schemes over the field. The centralizer representation is equality of
subgroup functors, including refinements and nonreduced and nonaffine tests.
There is no chosen maximal torus of `G`, splitness, perfectness,
characteristic restriction, or rational-point density premise.

The original source is Borel and Tits, *Groupes réductifs* (1965), registered
as `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
All PDF page numbers below are one-based.

- Sections 0.3 and 0.6–0.8, printed pp.57–59/PDF pp.4–6, give the affine
  absolutely reduced scheme convention, the multiplication-isomorphism
  meaning of semidirect product, and the geometric radical and Levi notions.
- Corollary 3.14, printed p.80/PDF p.27, states that rational Levis of a
  connected subgroup of maximum rank are its internal centralizers of
  rational maximal tori of its radical. Parabolics have the required
  connectedness and rank by sections 4.1–4.3, printed pp.85–86/PDF pp.32–33.
- The standard-parabolic decompositions in 4.2 and the proof of 4.15(b),
  printed p.91/PDF p.38, identify the ambient centralizer of the radical
  torus with a Levi of the parabolic. That proof uses `R(P) ∩ T` as its
  particular radical maximal torus. The proof of 4.18, printed p.92/PDF p.39,
  repeats this identification for a containing rational maximal torus.
  Section 2.15(d), printed p.70/PDF p.17, gives rationality and reductivity
  of torus centralizers.

The ambient-centralizer assertion for every supplied radical maximal torus
is a derived consequence, rather than the literal internal-centralizer
wording of 3.14: over an algebraic closure, conjugate the supplied torus
inside the radical to a standard radical maximal torus, apply 4.2, and
transport containment of its ambient centralizer in `P`. Descent of that
containment identifies the ambient centralizer with the internal
centralizer from 3.14. This is the source rationale for the proposition,
not an implemented Lean argument or an assertion that equality of point
sets suffices for the subgroup-functor conclusion. Its proof must establish
the maximality, scheme structure, descent and all-test comparisons needed
for the existing predicates, as well as the actual multiplication
isomorphism.

The authors' *Compléments à l'article « Groupes réductifs »* (1972),
registered as `borel-tits-1972-complements-groupes-reductifs`, SHA-256
`7639a6a59bdb4520ca171fa61c192c000f00396460b05b32766d56dee5a84e49`,
section 5.5, printed p.275/PDF p.24, corrects the wording of 4.15(b) to
Levis of `P`. The proposition uses this corrected ambient parabolic.

This is a focused existence clause extracted from the published
`ParabolicRadicalTorusLeviStatement`. It supplies no intersection geometry,
largest-central-subtorus result, split-part positivity, or unconditional
proof of that host. The host statement and its import closure are unchanged.
