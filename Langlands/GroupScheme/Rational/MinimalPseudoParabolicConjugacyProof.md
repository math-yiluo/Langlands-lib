# Borel–Tits conjugacy of minimal pseudo-parabolic subgroups

Author: Worker 4099. The composition was designed and compile-checked by Worker 15
of the previous project instance, in the public note
`notes/group-schemes/smooth-split-torus-conjugacy-route.md` (rows C.2.2, C.2.4
and C.2.5, and the hand-written C.2.4 body). That identity does not exist in
this instance, so the note is credited here rather than in the submission's
coauthor list. Worker 4099 checked that every ingredient is in the current
Library, put the composition into this module, checked it again and wrote this
description. The C.2.1 and C.2.3 inputs
are now published proofs, so this module uses them in place of the note's private
versions.

`Langlands.GroupScheme.minimalPseudoParabolicConjugacy` proves the exact
published proposition
`Langlands.GroupScheme.MinimalPseudoParabolicConjugacyStatement.{u}` (module
`Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyStatement`) at
an arbitrary universe `u`. Let `k : Type u` be any field and `G` a group scheme
over `Spec (CommRingCat.of k)` with `Smooth G.X.hom`, `ConnectedSpace G.X.left`
and `IsAffineHom G.X.hom`. Let `i : P ⟶ G` and `j : Q ⟶ G` satisfy
`IsMinimalPseudoParabolicSubgroup`. Then `SubgroupConjugate i j` holds: there
are a rational point `g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X` and an
actual group-scheme isomorphism `e : P ≅ Q` such that
`i ≫ (G.innerIso g).hom = e.hom ≫ j`.

The theorem has no hypotheses beyond those of the statement. The field may be
finite or infinite, perfect or imperfect, and of any characteristic. No
reductivity, pseudo-reductivity or splitting condition is placed on `G`. No
conjugacy is supplied as an input.

## Source

This is Theorem C.2.5 (Borel–Tits) of Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, second edition (2015), printed p.595 (PDF p.621). Its proof uses
Lemma C.2.2 (printed p.593), Theorem C.2.3 (printed p.593) and Proposition
C.2.4 (printed pp.594–595, PDF pp.620–621). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The top-level structure of the Lean proof follows the printed proof of Theorem
C.2.5. Every step is a published Library theorem, and this module only puts
them together. Those theorems' own modules describe their proofs, which may
differ from the printed ones.

## Declarations in this module

The two helper theorems are in the namespace
`Langlands.GroupScheme.MinimalPseudoParabolicConjugacyProof`. Each proves a
published proposition that has its own open proof task. The namespace keeps
these declarations from clashing with names those tasks may later publish.

1. `splitSolvableIntoPseudoParabolic` proves the published
   `SplitSolvableIntoPseudoParabolicStatement.{u}` (CGP Lemma C.2.2). Let `G` be
   smooth, connected and affine over `k`, `i : P ⟶ G` pseudo-parabolic, and
   `j : H ⟶ G` a closed subgroup with `H` split solvable. Then there are a
   rational point `g` of `G` and a homomorphism `f : H ⟶ P` with
   `f ≫ i = j ≫ (G.innerIso g).hom`. The proof applies the published reduction
   `splitSolvableIntoPseudoParabolic_of_components` (module
   `SplitTorusIntoPseudoParabolicReduction`) to five published proofs:
   - `smoothSubgroupQuotientExistence` (quotients by smooth closed subgroups);
   - `pseudoParabolicSubgroupStructure` (pseudo-parabolic subgroups are
     smooth, connected and affine);
   - `pseudoParabolicQuotientPseudoComplete` (the quotient by a
     pseudo-parabolic subgroup is pseudo-complete);
   - `splitSolvablePseudoCompleteFixedPoint` (a split solvable group acting on
     a pseudo-complete scheme with a rational point has a rational fixed point,
     CGP Proposition C.1.5);
   - `pseudoParabolicQuotientRationalLifting` (rational points of the quotient
     lift to rational points of `G`, CGP Lemma C.2.1).

   The reduction lifts a rational fixed point of `H` on the quotient to `G`.
   The inverse of that lift is the conjugator.
2. `pseudoParabolicMaximalSplitTorusStructure` proves the published
   `PseudoParabolicMaximalSplitTorusStructureStatement.{u}` (CGP Proposition
   C.2.4 and the maximality observation before it). Let `G` be smooth,
   connected and affine, `i : P ⟶ G` pseudo-parabolic and `s : S.toGrp ⟶ P` a
   maximal split torus of `P`. The theorem gives three conclusions.
   - `s ≫ i` is a maximal split torus of `G`.
   - `torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range i`.
   - For every split unipotent radical `j : U ⟶ P`, `i` is minimal exactly
     when it represents the fppf-local product of `torusCentralizer (s ≫ i)`
     and `SubgroupFunctor.range (j ≫ i)`.

   The first two clauses come from the published reduction
   `pseudoParabolicTorusCentralizerContainment_of_conjugacy`. It is applied to
   the published proof `smoothMaximalSplitTorusConjugacy` of CGP Theorem
   C.2.3. The forward direction of the criterion is the published reduction
   `pseudoParabolicCentralizerProductOfMinimality_of_statements`. It is
   applied to `smoothMaximalSplitTorusConjugacy` and two published proofs:
   - `pseudoParabolicSplitRadicalProduct` (CGP Proposition 2.2.4);
   - `pseudoParabolicSplitRadicalContainment` (CGP Corollary 2.2.5, its
     containment part).

   The reverse direction is the published reduction
   `pseudoParabolicMinimalityOfCentralizerProduct_of_statements`. It is applied
   to `smoothMaximalSplitTorusConjugacy`, the published
   `pseudoParabolicSplitSolvableEnvelope` and item 1.

The main theorem `minimalPseudoParabolicConjugacy` applies the published
assembly `minimalPseudoParabolicConjugacy_of_structure` (module
`Rational.MinimalPseudoParabolicConjugacyAssembly`) to five inputs:

- `pseudoParabolicSubgroupStructure`;
- `SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence` (every
  smooth connected affine group over `k` has a split unipotent radical
  `R_us,k`);
- `pseudoParabolicSplitSolvableEnvelope` (for a maximal split torus `S` of a
  pseudo-parabolic `P` and a split unipotent radical `U` of `P`, the closed
  split solvable group `S ⋉ U` maps onto the fppf-local product `S · U`
  inside `P`);
- item 1 (C.2.2);
- item 2 (C.2.4).

The assembly follows the printed proof of C.2.5. Let `i` and `j` be minimal.
Choose a maximal split torus `s` of `P`, using the published
`exists_maximalSplitTorus`. Also choose a split unipotent radical `z` of `P`
and the split solvable envelope `h` of `S ⋉ R_us,k(P)`. By item 1, a rational
point `g` conjugates `h ≫ i` into `Q`. The assembly keeps `P` fixed and
replaces `j` by its conjugate `j' = j ≫ (G.innerIso g).inv`, which is again
minimal. Then `s ≫ i` and `z ≫ i` lie in `j'` on every test scheme. By item 2,
`s ≫ i` is maximal split in `G`, so it lifts to a maximal split torus of `Q`.
Item 2 applied to `j'` then puts `torusCentralizer (s ≫ i)` inside `j'`. Since
`P` is minimal, item 2 makes `i` the fppf-local product of that centralizer
and the image of `z`. So the image of `i` lies in the image of `j'`.
Minimality of `j'` turns this containment into an equality of images, with an
actual source isomorphism. Composing with conjugation by `g` gives
`SubgroupConjugate i j`.

## Discharged prerequisites

The task context lists the prerequisites of the printed proof as proof
obligations: C.2.2, maximality transfer after C.2.3, and the centralizer
criterion C.2.4. Each one is discharged by a published proof or by a theorem
of this module, as follows.

- CGP Theorem C.2.3 is the published proof `smoothMaximalSplitTorusConjugacy`
  (module `Rational.SmoothMaximalSplitTorusConjugacyProof`). It is used only
  as an input to item 2, so the dependency runs from C.2.3 to C.2.5. Neither
  C.2.5 nor any relative-root reflection result is used.
- CGP Lemma C.2.1 is the published proof
  `pseudoParabolicQuotientRationalLifting` (module
  `PseudoParabolicQuotientRationalLiftingProof`).
- CGP Lemma C.2.2 and Proposition C.2.4 are items 1 and 2.

No unproved Library proposition appears as a hypothesis of any theorem in this
module. A compile check of `minimalPseudoParabolicConjugacy` reported only the
axioms `propext`, `Classical.choice` and `Quot.sound`.
