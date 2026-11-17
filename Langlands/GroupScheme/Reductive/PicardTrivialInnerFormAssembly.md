# Quasi-split inner forms over Picard-trivial bases from the geometric prerequisites

This module reduces the published proposition
[`ReductivePicardTrivialQuasiSplitInnerFormStatement`](PicardTrivialQuasiSplitInnerFormStatement.md)
(Conrad, *Reductive group schemes*, Remark 7.2.13) to six explicit inputs: four geometric
statements already published as statements, and two ring-theoretic facts about Picard
groups. It proves none of the six inputs. All of them remain hypotheses, so the module does
not prove the target unconditionally.

The four geometric statements are the ones used by the semi-local assembly
[`SemilocalInnerFormAssembly`](SemilocalInnerFormAssembly.md):

- `RelativeQuasiSplitInnerFormExistenceStatement`;
- `RelativeAdjointQuotientExistenceStatement`;
- `RelativeUnipotentRadicalFiltrationStatement`;
- `RelativeBorelAdjointTorusWeilPresentationStatement`.

The module imports `SemilocalInnerFormAssembly` (and through it the APIs listed there) and
the target statement module `PicardTrivialQuasiSplitInnerFormStatement`. It adds two
declarations.

## `quasiSplitInnerFormsIsoOfGeometricPrerequisitesOfPicTrivial`

This noncomputable definition constructs an actual isomorphism `H₁ ≅ H₂` of group schemes
over `Spec R`. Its inputs are:

- the four geometric statements (`hModel`, `hQuot`, `hFil`, `hWeil`), in universe `u`;
- a commutative ring `R : Type u` and the hypothesis `hPic`: every `R' : Type u` with
  `[CommRing R']`, `[Algebra R R']`, `Algebra.Etale R R'` and `Module.Finite R R'` has
  `Subsingleton (CommRing.Pic R')`;
- a reductive group `F` over `Spec R`, an fppf quotient `qF : F ⟶ Fad` by the centre
  `center F`, and an action `a : AutomorphicAction Fad F` whose restriction along `qF` is
  conjugation;
- two groups `H₁`, `H₂` over `Spec R` that are relatively quasi-split and étale inner forms
  of `F` relative to `a` (`a.IsEtaleInnerForm`).

The construction is the semi-local one, step for step, with one change. The semi-local
construction uses semi-locality only to show that the finite étale algebra from the Weil
presentation has trivial Picard group. Here `hPic` supplies that fact instead.

1. The model statement supplies a quasi-split inner form `G` of `F`, a Borel subgroup `B`
   of `G` with inclusion `i`, and a closed fibrewise maximal torus of `G` whose range lies
   in `B`. The represented-subgroup factorization turns the torus into a homomorphism
   `t` into `B` with `t ≫ i` equal to the torus inclusion.
2. The quotient statement supplies an affine fppf quotient `q : G ⟶ A` by the centre of
   `G`. The inner-action constructor gives its action `c` on `G`, which restricts to
   conjugation.
3. `adjointBorelExtensionData` builds the Borel stabilizer, the torus quotient, the
   sectioned Borel retraction with its unipotent radical, and the factorization of the
   centre. `torusWeilPresentation` applies `hWeil`. It yields a finite étale `R`-algebra
   `w.algebra` and an isomorphism `w.iso` that presents the torus quotient as the Weil
   restriction of `Gm` from `w.algebra`.
4. The filtration statement gives a finite vector-bundle series for the unipotent radical.
   Closed subgroups of affine groups give the remaining affineness and monicity instances.
5. `hPic w.algebra w.etale` (finiteness by instance) gives
   `Subsingleton (CommRing.Pic w.algebra)`.
6. The published `SectionedQuotientExtension.quasiSplitInnerFormsIsoOfPicTrivial`, with
   coefficient ring `CommRingCat.of w.algebra`, compares `H₁` and `H₂` through the anchor
   `G` and returns `H₁ ≅ H₂`.

The model, quotient and Weil choices are existential, so the construction is wrapped in
`Classical.choice` of a nonempty isomorphism type.

## `reductivePicardTrivialQuasiSplitInnerFormStatement_of_prerequisites`

This theorem has exactly `ReductivePicardTrivialQuasiSplitInnerFormStatement.{u}` as its
conclusion. Its hypotheses are the four geometric statements and:

- `hZ`: for every commutative ring `R : Type u` with `Nonempty (R ≃+* ℤ)`, every
  `R' : Type u` with `[CommRing R']`, `[Algebra R R']`, `Algebra.Etale R R'` and
  `Module.Finite R R'` has `Subsingleton (CommRing.Pic R')`;
- `hAff`: for every field `k : Type u` with `[CharZero k]`, every `n : ℕ` and every
  `A : Type u` with `[CommRing A]` and `[Algebra (MvPolynomial (Fin n) k) A]`, if `A` is
  étale and module-finite over `MvPolynomial (Fin n) k` then
  `Subsingleton (CommRing.Pic A)`.

`hAff` is, word for word, the body of the separately stated
`Langlands.Algebra.AffineSpaceFiniteEtalePicardTrivialStatement.{u}`. `hZ` is the
statement "finite étale covers of `Spec ℤ` have trivial Picard group", transported to rings
isomorphic to `ℤ`. Both are written inline, so this module does not depend on either
Picard-group development.

The proof unfolds the target and introduces its local predicate `QSInner`. It first proves
clause 1, for every `R` satisfying the `hPic` hypothesis:

- existence: the model statement gives a quasi-split inner form directly;
- uniqueness: `quasiSplitInnerFormsIsoOfGeometricPrerequisitesOfPicTrivial` gives an
  isomorphism between any two quasi-split inner forms.

Clause 2 is clause 1 applied with `hZ R`, and clause 3 is clause 1 applied with `hAff k n`
at `R = MvPolynomial (Fin n) k`.

## Provenance

The provenance is internal. The module combines the named statements with the
represented-subgroup, inner-action, adjoint Borel extension, Weil-presentation and
sectioned inner-descent APIs of the Library. It follows Conrad's Remark 7.2.13 (p.259 of
`conrad-2014-reductive-group-schemes`): "The only role of semi-locality for the affine S in
the proof of Proposition 7.2.12 is to ensure that every finite étale cover of S has trivial
Picard group." The Library's semi-local assembly is the formal version of that proof, and
this module isolates the single place where semi-locality enters. It claims no new
structural theorem. Its purpose is to name a sufficient set of proof obligations for the
unchanged target: the four geometric statements, `hZ` and `hAff`.
