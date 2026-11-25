# Renard VI.10.6 Proposition (i) from the Bernstein decomposition and the criterion

Uniqueness of inertial support is derived from the
Bernstein decomposition at carrier universe `max uF uV`.

This module proves two conditional theorems and one entry declaration. They
reduce the published
`Langlands.Jacquet.StandardIwahoriFixedVectorBlockDecompositionStatement`
(Renard VI.10.6 Proposition (i), `M(G)_K ≃ ∏_{𝔰 ∈ B(G)_K} M(G)_𝔰`), and the
fixed-vector visibility of Bernstein classes, to two published Library
statements. Their proofs are not part of this module. The module proves neither
the target nor visibility unconditionally.

It improves on the sibling module `StandardIwahoriFixedVectorCategoryFromInputs`.
That module also needs VI.5.4 (represented association) to get uniqueness of
inertial support. Here uniqueness comes from the off-diagonal clause of the
Bernstein decomposition, so VI.5.4 is not a premise.

## Statements

The hypotheses are exactly these published Library statements:

- `hBernstein`: `CuspidalSupport.BernsteinDecompositionStatement.{uF, uV}`
  (Renard VI.7.2, the Bernstein decomposition of the category of smooth
  representations whose carriers live in universe `uV`);
- `hBernsteinSat`: `CuspidalSupport.BernsteinDecompositionStatement.{uF, max uF uV}`
  (the same statement at carrier universe `max uF uV`, where the inertial
  supports of the target live);
- `hCrit`: `CuspidalSupport.StandardRepresentativeFixedVectorCriterionStatement.{uF, uV}`
  (Renard VI.10.6, first claim of the proof of the Corollary: `[a]_G ∈ B(G)_K`
  iff the cuspidal representation of the datum `a` has a nonzero
  `K ∩ M_a`-fixed vector).

`hBernstein` and `hBernsteinSat` are two universe instances of one
statement. A universe-polymorphic proof of it supplies both.

The module proves the following.

- `standardIwahoriBernsteinFixedVectorVisibility_of_decomposition hBernsteinSat hCrit`
  takes the binders, hypotheses and `letI` instances of the target statement,
  in the target's order, up to and including `_hIwahori` and the three
  instances `T2Space F`, `LocallyCompactSpace (rationalPoints G)` and
  `NonarchimedeanGroup (rationalPoints G)`. It concludes
  `bernsteinFixedVectorVisibility.{uF, uV} i ν (standardBernsteinFamily i ν hG hi hν) K`.
  So two irreducible smooth representations (carrier universe `max uF uV`)
  with the same inertial support either both have nonzero `K`-fixed vectors
  or both have none.
- `standardIwahoriFixedVectorBlockDecomposition_of_decomposition hBernstein hBernsteinSat hCrit`
  has type exactly `StandardIwahoriFixedVectorBlockDecompositionStatement.{uF, uV}`.
- `standardIwahoriFixedVectorBlockDecompositionOfDecomposition` (the entry
  declaration) is the same implication stated as a declaration whose type is
  the implication: the three hypotheses in the order above, then the target.
  It is a `def` of Prop-valued type, so the `defProp` linter is disabled for
  this declaration only.

The field universe `uF` and the carrier universe `uV` stay independent. The
proofs add no premise beyond the hypotheses listed. In particular they assume
no admissibility, finite-length, canonical-section or VI.5.4 statement.

## Proof

For the visibility theorem, the proof introduces the binders and instances
of the target. It applies `bernsteinFixedVectorVisibility_of_uniqueness_of_necessity`
(module `StandardIwahoriVisibilityReduction`) to the standard family, with
three inputs:

- `_hstandard`, compactness of `K` and `_hIwahori` from the binders;
- uniqueness of inertial support, from the published
  `CuspidalSupport.bernsteinInertialSupportUniqueness_of_offDiagonalHomsZero`
  (module `Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionAssembly`).
  Its input is the second component of `hBernsteinSat` at the standard family,
  which says morphisms between objects of different blocks are zero. That
  published proof works as follows. An irreducible representation with two
  inertial supports `s ≠ t` lies in both blocks. Its identity is then an
  off-diagonal morphism, hence zero, so the representation is zero. This
  contradicts irreducibility.
- the forward direction of `hCrit`, applied to the same binders.

The binders `K₀`, `_hK₀`, `_hIwasawa`, `_hKK₀` and `_hnormal` are used only
to instantiate `hCrit`.

For the block decomposition, the proof introduces the same binders and an
object `V`. The direction (⇒) is
`isCoproductOfFixedClasses_of_fixedVectorGenerated` (module
`StandardIwahoriBlockDecompositionReduction`), applied to the first component
of `hBernstein` at the standard family. That component says every object is
a coproduct of block objects. The direction (⇐) is
`fixedVectorGenerated_of_isCoproductOfFixedClasses` (same module), applied to
the visibility just proved. The index predicate `bernsteinFixedClass` of that
module unfolds to the target's index predicate, so the conclusion has the
target's exact form.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VI.10.6: the Theorem and its proof, the
Proposition (i) and its proof, and the proof of the Corollary (printed
pp.213–215 / PDF pp.219–221). The input is VI.7.2 (printed pp.181–184 / PDF
pp.187–190). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The provenance is derived. Renard deduces Proposition (i) from the Bernstein
decomposition together with the fact that `K`-fixed vectors are visible on
inertial classes. The latter comes from the criterion of the Corollary's
proof and Jacquet's lemma. The implemented route uses the admissibility-free
nonvanishing form of Jacquet's lemma (module `IwahoriJacquetNonvanishing`),
only the necessity direction of the criterion, and uniqueness of inertial
support. In Renard that uniqueness, which makes the inertial support of an
irreducible representation well defined, rests on VI.5.4. Here it is derived
instead from the orthogonality of the blocks in VI.7.2.

Applied to proofs of the two input statements, these theorems prove the
target and the visibility helper unconditionally. The criterion is proved by
`Langlands.CuspidalSupport.standardRepresentativeFixedVectorCriterion`
(module `CuspidalSupport.StandardRepresentativeFixedVectorCriterionProof`);
the Library has no proof of `BernsteinDecompositionStatement` (VI.7.2).
