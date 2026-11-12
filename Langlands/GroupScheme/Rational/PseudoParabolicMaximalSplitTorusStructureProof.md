# Maximal split tori and the minimality criterion for pseudo-parabolics

Authors: Worker 4243 and Worker 15. Worker 15 designed and compile-checked
this composition of published results in the note
`notes/group-schemes/smooth-split-torus-conjugacy-route.md` (section
"Hand-written steps"). Worker 4243 put it into this module, checked it
again against the current Library and wrote this description.

`Langlands.GroupScheme.pseudoParabolicMaximalSplitTorusStructure` proves
exactly the published proposition
`Langlands.GroupScheme.PseudoParabolicMaximalSplitTorusStructureStatement.{u}`
(module `Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureStatement`)
at an arbitrary universe `u`. The statement and its imported definitions
are unchanged, and the theorem has no hypotheses beyond those of the
statement.

## What is proved

Let `k : Type u` be any field and `G` a group scheme over `Spec k` with
`Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`. Let
`i : P ⟶ G` satisfy `IsPseudoParabolicSubgroup i`, and let
`s : S.toGrp ⟶ P` satisfy `IsMaximalSplitTorus s`. Then:

1. `IsMaximalSplitTorus (s ≫ i)`: `S` is a maximal split torus of `G`.
2. `torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range i`: the centralizer
   of the whole torus, `Z_G(S)`, lies in `P` on every relative scheme test.
3. For every `j : U ⟶ P` with `IsSplitUnipotentRadical j`,
   `IsMinimalPseudoParabolicSubgroup i` holds if and only if
   `SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i))
   (SubgroupFunctor.range (j ≫ i)) i` holds, that is, `i` represents the
   fppf-local product `Z_G(S) · R_us,k(P)`.

The field may be finite or infinite, perfect or imperfect, of any
characteristic. No reductivity, pseudo-reductivity or splitting condition
is placed on `G`. Clause 3 quantifies over every supplied split radical
representative; the proof does not choose a radical and does not assert
that one exists.

## Proof

The proof introduces the data of the statement and applies three published
conditional reductions. Each reduction's theorem-valued premises are
supplied by published unconditional proofs, so the resulting theorem is
unconditional. Only the axioms `propext`, `Classical.choice` and
`Quot.sound` occur.

**Clauses 1 and 2.** The published reduction
`pseudoParabolicTorusCentralizerContainment_of_conjugacy` (module
`Rational.PseudoParabolicMaximalSplitTorusStructureReduction`) takes
`SmoothMaximalSplitTorusConjugacyStatement` as its only premise. The proof
supplies the published `smoothMaximalSplitTorusConjugacy` (CGP Theorem
C.2.3; module `Rational.SmoothMaximalSplitTorusConjugacyProof`). Applied to
`k, G, P, i, hi, S, s, hs`, the reduction returns both conclusions. Inside
the reduction, C.2.3 applied to `P` conjugates a cocharacter `χ` with
`P_G(χ) ⊆ P` into `S` by a rational point of `P`. This gives
`Z_G(S) ⊆ P_G(ξ ≫ s ≫ i) ⊆ P` for a cocharacter `ξ` of `S`. Maximality in `G`
then follows from the published criterion
`IsMaximalSplitTorus.comp_of_torusCentralizer_le_range`.

**Clause 3, minimal implies product.** The published reduction
`pseudoParabolicCentralizerProductOfMinimality_of_statements` (module
`Rational.MinimalPseudoParabolicCentralizerProduct`) has three premises.
The proof supplies the following published proofs:

- `smoothMaximalSplitTorusConjugacy` (CGP C.2.3);
- `pseudoParabolicSplitRadicalProduct` (CGP Proposition 2.2.4; module
  `PseudoParabolicSplitRadicalProductProof`);
- `pseudoParabolicSplitRadicalContainment` (the containment part of CGP
  Corollary 2.2.5; module `PseudoParabolicSplitRadicalContainmentProof`).

The reduction is applied to the full data, the radical `j`, its predicate
`hj` and the minimality hypothesis. As described in that module's Markdown,
it chooses a cocharacter `ψ` of `S` with `Z_G(ψ) = Z_G(S)` and
`P_G(ψ) ⊆ P`. Minimality then forces `P = P_G(ψ) R_u,k(G)`, and 2.2.4 turns
this into `P = P_G(ψ) R_us,k(G)`. The dynamic decomposition
`P_G(ψ) = Z_G(ψ) ⋉ U_G(ψ)` and the containment
`U_G(ψ) R_us,k(G) ⊆ R_us,k(P)` finish the proof.

**Clause 3, product implies minimal.** The published reduction
`pseudoParabolicMinimalityOfCentralizerProduct_of_statements` (module
`Rational.PseudoParabolicMinimalityCriterionReduction`) has three premises.
The proof supplies the following:

- `smoothMaximalSplitTorusConjugacy` (CGP C.2.3);
- `pseudoParabolicSplitSolvableEnvelope` (the split solvable subgroup
  `S ⋉ R_us,k(P)` of `P`; module
  `Rational.PseudoParabolicSplitSolvableEnvelopeProof`);
- the term
  `splitSolvableIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
  pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
  splitSolvablePseudoCompleteFixedPoint pseudoParabolicQuotientRationalLifting`,
  a proof of `SplitSolvableIntoPseudoParabolicStatement` (CGP Lemma C.2.2).

C.2.2 has no standalone published proof in the Library. The term above
applies its published reduction (module
`SplitTorusIntoPseudoParabolicReduction`) to five published proofs:

- `smoothSubgroupQuotientExistence`: existence of the quotient of `G` by a
  smooth closed subgroup, here `G/P`;
- `pseudoParabolicSubgroupStructure`: `P` is smooth, connected and affine;
- `pseudoParabolicQuotientPseudoComplete`: CGP Proposition C.1.6;
- `splitSolvablePseudoCompleteFixedPoint`: CGP Proposition C.1.5;
- `pseudoParabolicQuotientRationalLifting`: CGP Lemma C.2.1.

The term is inlined and adds no declaration. The reduction is applied to
the full data, `j`, `hj` and the product hypothesis. As described in that
module's Markdown, it conjugates `S ⋉ R_us,k(P)` into a smaller
pseudo-parabolic `Q` by C.2.2. Clauses 1 and 2 (for `P` and for `Q`) give
`Z_G(S)` inside that conjugate of `Q`. The product hypothesis then puts `P`
inside the conjugate. A Noetherian lemma shows that a closed subgroup
contained in its own conjugate equals it, so the ranges agree.

## Source and route

The target formalizes the maximality observation immediately before
Proposition C.2.4 and the proposition itself in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), printed pp.594–595
(PDF pp.620–621). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

Clauses 1 and 2 follow the printed argument: the last paragraph of the proof
of C.2.4 and the observation before it. The printed proof of the minimality
criterion passes to `P/R_u,k(P)` and uses Remark 3.5.6, Proposition 3.5.8,
Lemma 2.2.3, Proposition A.2.5, Corollary B.3.5 and Proposition B.4.4. The
Lean route avoids these quotient and wound-group inputs. Instead it uses
the dynamic description of `P` with Proposition 2.2.4 and Corollary 2.2.5
for the forward direction. For the reverse direction it uses the
containment argument that CGP gives in the proof of Theorem C.2.5:
`S ⋉ R_us,k(P)`, Lemma C.2.2 and the maximality observation. The
Markdown of the two criterion reductions documents these differences.

The reverse direction uses Lemma C.2.2 and the envelope `S ⋉ R_us,k(P)`.
It does not use the statement of Theorem C.2.5,
`MinimalPseudoParabolicConjugacyStatement`, or any relative-root or
reflection result. The dependency order C.2.1 → C.2.2 → C.2.3 → C.2.4 is
preserved.
