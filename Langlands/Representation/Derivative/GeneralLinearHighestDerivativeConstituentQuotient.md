# Actual general-linear highest-derivative constituents and dual quotients

Author: Worker 357.

This derived construction takes an actual smooth representation `A` of
`GL_(N+1)(F)` and a supplied representation `B` equivalent to the
modulus-twisted smooth contragredient of `A`. A nonzero finite-length highest
order-`k` derivative of `A` yields an actual irreducible admissible
subrepresentation `S`, an invariant ambient derivative form, and an actual
surjection from the order-`k` derivative of `B` onto the smooth contragredient
of `S`, with its evaluation formula. Finite length of the left derivative
and its highestness remain explicit inputs.

## Interface and actual data

The sole new declaration is
`Langlands.Derivative.chooseGeneralLinearHighestDerivativeConstituentQuotient`.
Its independent universe parameters are `uF` and `uV`. It takes arbitrary
`{p : ℕ} [Fact p.Prime]`, `{F : PadicField.{uF} p}`, a supplied
`T : F.TopologicalData`, and a supplied
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`.
The character bundle already includes continuity and nontriviality. The
remaining inputs, in order, are:

- `N k : ℕ` and `hk : 0 < k ∧ k ≤ N + 1`;
- actual `A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (N + 1) F.Carrier)`;
- an actual representation equivalence
  `B.representation.Equiv (twist (T.determinantPowerCharacter (N + 1) 1)
  (smoothContragredient A.representation))`;
- nontriviality of `DA := (generalLinearDerivative T ψ (N + 1) k hk.2).obj A`;
- `DA.HasFiniteLength`;
- `Subsingleton ((generalLinearDerivative T ψ (N + 1) j hj).obj A)` for every
  natural number `j`, every `hj : j ≤ N + 1`, and every `k < j`.

The supplied topology is installed before the representations are quantified.
The supplied topological-group instances at ranks `N + 1` and `N + 1 - k`
are installed where the twist, smooth dual and output require them. Both
ambient carriers have universe `uV`; no relation between `uF` and `uV` is
assumed. A consumer can specialize `uV` to `max uF uV` without changing the
construction or resizing a carrier. The valid top order `k = N + 1` has
rank-zero target, and `N = 0` is included. The interface requires positive
order, so it does not cover `k = 0`.

Write `DB := (generalLinearDerivative T ψ (N + 1) k hk.2).obj B`.
The result is the existing structure
`Langlands.InvariantBilinear.ConstituentDualQuotientData DA DB`.
It retains these actual fields:

- `constituent : Subrepresentation DA.representation`, denoted `S`;
- irreducibility and admissibility of `SmoothRep.subrepresentation DA S`;
- `form : InvariantBilinear.forms DA.representation DB.representation
  (fun _ => 1)` and its `SeparatingLeft` proof;
- `quotient`, an actual intertwiner from `DB.representation` onto
  `smoothContragredient (SmoothRep.subrepresentation DA S).representation`;
- surjectivity of that map;
- for every `w : DB` and `x : SmoothRep.subrepresentation DA S`, the equality
  `(quotient w).val x = form.val x.val w`.

Thus `S` is a literal invariant subspace of the given derivative, and the
codomain consists of all smooth functionals on its actual restricted smooth
representation. Neither it nor the map is replaced by an isomorphism class.
The ambient form has simultaneous covariance one and separates the left
input. The result makes no uniqueness or canonicity assertion about the
chosen subrepresentation or form.

## Implemented construction and provenance

Put `RA := (generalLinearRestriction T N).obj A` and
`RB := (generalLinearRestriction T N).obj B`. Apply the published
`Classification.MirabolicDerivativeContragredient.exists_determinant_pairing`
to `A`, `B`, their supplied equivalence, `W = RA` and the identity inclusion
`RA ⟶ RA`. The identity is injective. This produces a form `β` on `RA × RB`
with simultaneous covariance
`g ↦ ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)`
which separates `RA`. The implementation selects the form and its separation
proof by `Classical.choose` and `Classical.choose_spec` before returning data.

The determinant-pairing proof evaluates the smooth functional corresponding
to a vector of `B` on a vector of `A`. Equivariance of the supplied
representation equivalence and invariance of the smooth evaluation pairing
give covariance `|det|^1 = |det|`. Smooth functionals separate vectors of a
smooth general-linear representation by smooth-bidual injectivity and the
proved compact-open basis. No admissibility of `A` is needed for this step.

The published equality
`Classification.MirabolicDerivativeContragredient.mirabolicDerivativeOfOrder_restriction`
identifies the actual order-`j` mirabolic derivative of `RA` with the actual
order-`j` general-linear derivative of `A`, for every positive valid `j`.
The equality follows by unfolding the positive general-linear derivative and
commuting its rank transport with restriction. Use it to transport the
nontriviality, finite-length and higher-vanishing inputs to `RA`. If
`hj : 0 < j ∧ j ≤ N + 1`, the general-linear vanishing hypothesis is applied
to `hj.2`. There is no positivity gap: `j > k` and `hk.1` ensure that all
higher orders needed by the mirabolic constructor are positive.

Apply the published
`Derivative.Mirabolic.chooseHighestDerivativeConstituentQuotient` to
`RA`, `RB`, these transported inputs, `β` and its left-separation proof.
That constructor chooses an invariant form on the highest derivatives from
the proved general mirabolic highest-pairing theorem. Finite length makes
the nontrivial left derivative's group-algebra module Artinian; an atom
provides its actual irreducible subrepresentation. The proved cuspidal
embedding theorem gives admissibility, including the rank-zero case.
The compact-open basis and the published
`InvariantBilinear.smoothDualQuotientOfLeftEmbedding` then give the actual
surjection onto the constituent's full smooth dual and its evaluation
formula. In this last construction the formula is definitional. Neither
finite length of the right derivative nor highestness of `B` is required.

Finally rewrite both derivative objects by the restriction equality, once
for `A` and once for `B`. This transports the entire returned structure to
`ConstituentDualQuotientData DA DB`, preserving all its fields. The returned
ambient form is the chosen highest-derivative form; no formula relating it
to `β`, and no naturality assertion, is added here.

The provenance is derived composition of unchanged published constructions.
This pair adds no new assertion from an original source and has no new
source-citation tuple. Its proof dependencies are the determinant evaluation
pairing, the objectwise derivative restriction equality, and the actual
mirabolic constituent-and-quotient constructor just described. Statements,
citations and pending artifacts do not occur as proved inputs.

## Published inputs and reuse

Both direct imports were independently accepted and published before this
construction. The mirabolic constructor was approved by Reviewer 8072 and
published at Library commit `d08b5767dba1139a70ed7ebfc0438a31c2587868`.
The determinant-pairing and restriction helper was approved by Reviewer 6113
and published at `9a8ca758097242bde4147f33304f43fceef22fa4`. Their native,
frozen and published paired files agree byte for byte with the pairs in the
Library base below.

The existing `exists_derivative_hom_contragredient` in the second import
accepts a supplied irreducible subrepresentation and concludes a nonzero
map. This construction instead selects an actual constituent under an
explicit finite-length premise and returns the surjection, ambient invariant
form and evaluation formula supplied by the first import. The existing
mirabolic constructor is reused directly. No second proof of it, no new
pairing-to-dual construction, and no broad support-shift module is needed.

## Import and proof-dependency audit

At Library base `f5419c02a38b007a5bcd6dc3abfa87954cc89f5f`, the two direct
imports, both under `Langlands.Representation`, are:

1. `Derivative.HighestDerivativeConstituentQuotient`;
2. `Classification.MirabolicDerivativeContragredient`.

Their project closures contain respectively 190 and 145 modules including
their roots. The union with this new module has 197 project modules and 118
external import roots. Appendices A and B give the complete inventories.
Every one of the 196 inherited Lean/Markdown pairs matches the base Library
byte for byte, and every pair has nonempty Markdown.

Relative to the published mirabolic constructor's closure, the six inherited
additions are `Category.Contragredient`,
`Classification.ConstituentRelations`,
`Classification.MirabolicDerivativeContragredient`, `Twist.DualProof`,
`Twist.DualStatement` and `Twist.SmoothPartDefinitions`, all under
`Langlands.Representation`. Their full Lean implementations were inspected.
They supply the actual evaluation/transport helper and generic smooth-dual,
inverse-character twist, and constituent-relation infrastructure. The
constituent relations are definitions and assert no segment head or socle
existence or classification theorem.

The mathematical route inside the mirabolic constructor was also inspected:
`chooseHighestDerivativePairing` chooses the form from the proved general
`mirabolicHighestDerivativePairing`; its proof iterates the general `Φ⁻`
pairing step and descends through `Ψ⁻` under the left highestness hypothesis.
The general Artinian-atom argument selects the subrepresentation.
`CuspidalSupport.cuspidalEmbedding` supplies admissibility.
`smoothDualQuotientOfLeftEmbedding` restricts the invariant form, maps the
smooth right input into the full smooth dual, and uses irreducibility of
that dual to prove surjectivity. Its dual-irreducibility proof uses smooth
bidual injectivity and admissible bidual surjectivity with compact-open
cofinality. These are general representation-theoretic steps.

The six classification modules in the closure are `Supercuspidal`,
`SupercuspidalTwist`, `SupercuspidalContragredientStatement`,
`SupercuspidalContragredientAux`, `ConstituentRelations` and
`MirabolicDerivativeContragredient`. The statement modules provide
proposition definitions; the actual used duality and pairing conclusions
come from their proved helpers. The inherited Rankin–Selberg, Whittaker
and matrix-coefficient branches enter through the general highest-pairing
and cuspidal-embedding foundations, rather than through segment
classification or Whittaker coinvariant-finiteness conclusions.

This is within the general derivative/duality route permitted by trusted
operator response `bd71b9185aab5d6eafffb7891bd3a3ca`; response
`0edda6122ce65ed7ac51603c37473920` retains this host's exclusions when
allowing the specified general infrastructure. The support-only permission
`30144f6f9b59540b88b6d4c1517892d9` supplies no mathematical premise here:
this constructor asserts no segment support bound. The permissions have not
been interpreted as permission to use stronger segment conclusions.

The complete import inventory, source-name scan and inspected proof routes
exclude Ze80 3.5/9.6 and their proof successors; the segment-socle part of
`8e5b4563-0365-41c7-b134-70f2a0b36292`; segment head, socle and full Jacquet
formulas and special Jacquet exponent formulas; two-supercuspidal product
irreducibility or structure; segment-socle commutation, gluing and unlinked
or linked structure; special-head product irreducibility in either direction;
`GenericSegmentProductUniqueness`; multisegment, socle, square-integrable
and regular exhaustion; ordered strong-head or multisegment-socle existence;
quotient coverage; ordered conversion; tempered uniqueness;
`SquareIntegrableLanglandsClassification`; analytic segment classification;
forward special-segment essential square-integrability; and Whittaker
coinvariant-finiteness conclusions. No task listed under the host's
Independence, or its excluded mathematical conclusion under a new name,
is used as a proof input. The lexical scan supplements the proof-route
inspection; it does not replace it.

Compilation and declaration inspection report independent `uF` and `uV`,
and only `propext`, `Classical.choice` and `Quot.sound`. The submitted module
contains no proof holes, new axioms or kernel-bypassing commands. These
checks are development evidence; this contribution still requires its own
independent semantic review and publication.

## Scope remaining for the host

Only the left derivative is assumed highest. The finite length of that
derivative is explicit and is not inferred from finite length of `A`.
The result provides a quotient onto one actual constituent's smooth dual;
it asserts no equivalence with the entire right derivative and no
irreducibility of the entire left derivative. It gives no support existence,
shifted support equality, segment derivative identification, multiplicity
formula, linked-pair argument or irreducibility criterion.

The full repeated-segment proposition
`Langlands.Classification.SegmentHeadProductIrreducibility.{uF,uV} F T`
remains the host's separate proof obligation, in its original universes.

## Appendix A: complete project import closure

- `Langlands.Analysis.Local.QuotientMeasure`
- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.BlockModulus`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.CartanProof`
- `Langlands.Group.GL.CartanStatement`
- `Langlands.Group.GL.CompactOpen`
- `Langlands.Group.GL.IntegralSubgroup`
- `Langlands.Group.GL.Maps`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement`
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.OneBlockShape`
- `Langlands.Group.GL.OppositeBlocks`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.PadicBlocks`
- `Langlands.Group.GL.PadicOppositeBlocks`
- `Langlands.Group.GL.PadicUpperUnipotent`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.SingleBlock`
- `Langlands.Group.GL.TriangularParabolic`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.HarmonicAnalysis.CharacterTransport`
- `Langlands.HarmonicAnalysis.Conductor`
- `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof`
- `Langlands.HarmonicAnalysis.PadicHaarScalingStatement`
- `Langlands.HarmonicAnalysis.PadicLatticeTopology`
- `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.HarmonicAnalysis.RowSchwartzAction`
- `Langlands.HarmonicAnalysis.RowTestSmoothProof`
- `Langlands.HarmonicAnalysis.RowTestSmoothStatement`
- `Langlands.LocalFactor.Euler`
- `Langlands.LocalFactor.Euler.Definitions`
- `Langlands.LocalFactor.Harmonic.Statement`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.Contragredient`
- `Langlands.Representation.Category.Subquotients`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Classification.ConstituentRelations`
- `Langlands.Representation.Classification.MirabolicDerivativeContragredient`
- `Langlands.Representation.Classification.Supercuspidal`
- `Langlands.Representation.Classification.SupercuspidalContragredientAux`
- `Langlands.Representation.Classification.SupercuspidalContragredientStatement`
- `Langlands.Representation.Classification.SupercuspidalTwist`
- `Langlands.Representation.Compact.Definitions`
- `Langlands.Representation.Compact.FiniteMean`
- `Langlands.Representation.Compact.OrbitMeanTranslation`
- `Langlands.Representation.Compact.ProjectionProof`
- `Langlands.Representation.Compact.ProjectionStatement`
- `Langlands.Representation.Conductor.Congruence`
- `Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof`
- `Langlands.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups`
- `Langlands.Representation.CuspidalSupport.LeviDefinitions`
- `Langlands.Representation.CuspidalSupport.LeviGapVanishing`
- `Langlands.Representation.CuspidalSupport.LeviSplitContraction`
- `Langlands.Representation.CuspidalSupport.MinimalJacquetProof`
- `Langlands.Representation.CuspidalSupport.MinimalJacquetStatement`
- `Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement`
- `Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof`
- `Langlands.Representation.Derivative.GeneralLinearHighestDerivativeConstituentQuotient`
- `Langlands.Representation.Derivative.HighestDerivativeConstituentQuotient`
- `Langlands.Representation.Derivative.Homogeneity`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.MinusVanishing`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement`
- `Langlands.Representation.Derivative.MirabolicDerivativeVanishing`
- `Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent`
- `Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof`
- `Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement`
- `Langlands.Representation.Derivative.MirabolicLatticeBox`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof`
- `Langlands.Representation.Derivative.MirabolicMinusPairingTransferStatement`
- `Langlands.Representation.Derivative.MirabolicPairingLevelComparison`
- `Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Filtration.InvariantBilinear`
- `Langlands.Representation.Filtration.InvariantBilinearBounds`
- `Langlands.Representation.Filtration.InvariantBilinearSmoothDual`
- `Langlands.Representation.Filtration.ObjectDefinitions`
- `Langlands.Representation.Filtration.SmoothDualEvaluation`
- `Langlands.Representation.Geometric.GeometricLemmaStatement`
- `Langlands.Representation.Geometric.IntersectionTransport`
- `Langlands.Representation.Geometric.RefinementDefinitions`
- `Langlands.Representation.Geometric.RefinementFunctors`
- `Langlands.Representation.Geometric.WeylDefinitions`
- `Langlands.Representation.Hecke.TestFunction`
- `Langlands.Representation.Induction.CompactQuotientProof`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.Parabolic`
- `Langlands.Representation.Induction.StructuralStatement`
- `Langlands.Representation.Jacquet.CharacterAveraging`
- `Langlands.Representation.Jacquet.CharacterTwistEquiv`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.ExactProof`
- `Langlands.Representation.Jacquet.ExactStatement`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.Normalized`
- `Langlands.Representation.Jacquet.Parabolic`
- `Langlands.Representation.Jacquet.PositiveCharacter`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement`
- `Langlands.Representation.Parabolic.AdmissibilityStatement`
- `Langlands.Representation.Parabolic.GeometricPrerequisitesStatement`
- `Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof`
- `Langlands.Representation.Parabolic.NormalizedAdmissibilityProof`
- `Langlands.Representation.Parabolic.NormalizedInductionStatement`
- `Langlands.Representation.Parabolic.QuotientCompactProof`
- `Langlands.Representation.Parabolic.RefinementCharacter`
- `Langlands.Representation.Parabolic.RefinementComposition`
- `Langlands.Representation.Parabolic.RefinementPreimage`
- `Langlands.Representation.RankinSelberg.AnalyticStatement`
- `Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof`
- `Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement`
- `Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly`
- `Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction`
- `Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement`
- `Langlands.Representation.RankinSelberg.LocalFactor`
- `Langlands.Representation.RankinSelberg.Measures`
- `Langlands.Representation.RankinSelberg.QuotientIntegrals`
- `Langlands.Representation.RankinSelberg.RationalContinuation`
- `Langlands.Representation.RankinSelberg.RationalZeta`
- `Langlands.Representation.RankinSelberg.TwistInvariance`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement`
- `Langlands.Representation.Schur.CountableDimensionProof`
- `Langlands.Representation.Schur.CountableDimensionStatement`
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement`
- `Langlands.Representation.Smooth.Admissibility.EmbeddingProof`
- `Langlands.Representation.Smooth.Admissibility.EmbeddingStatement`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceProof`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceStatement`
- `Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof`
- `Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement`
- `Langlands.Representation.Smooth.Contragredient.CompactDualityProof`
- `Langlands.Representation.Smooth.Contragredient.CompactDualityStatement`
- `Langlands.Representation.Smooth.Contragredient.Definitions`
- `Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions`
- `Langlands.Representation.Smooth.Contragredient.LawsProof`
- `Langlands.Representation.Smooth.Contragredient.LawsStatement`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.FixedVectors.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement`
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement`
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement`
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement`
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.DualProof`
- `Langlands.Representation.Twist.DualStatement`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothPartDefinitions`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement`
- `Langlands.Representation.Unitary.Basic`
- `Langlands.Representation.Whittaker.Algebraic`
- `Langlands.Representation.Whittaker.AlgebraicTwist`
- `Langlands.Representation.Whittaker.DualTransform`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Representation.Whittaker.Iwasawa`
- `Langlands.Representation.Whittaker.Twist`
- `Langlands.Topology.CompactNormCharacter`
- `Langlands.Topology.CompactOpen.NeighborhoodBasis`
- `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement`
- `Langlands.Topology.Nonarchimedean.Subgroup`

## Appendix B: external import roots

- `Lean.Elab.Tactic.Omega`
- `Mathlib.Algebra.BigOperators.Fin`
- `Mathlib.Algebra.BigOperators.Finprod`
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Mathlib.Algebra.CharP.Basic`
- `Mathlib.Algebra.Field.Subfield.Basic`
- `Mathlib.Algebra.Group.Hom.Instances`
- `Mathlib.Algebra.Group.Subgroup.Ker`
- `Mathlib.Algebra.Order.Archimedean.Basic`
- `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Mathlib.Algebra.Polynomial.Laurent`
- `Mathlib.Algebra.Polynomial.Lifts`
- `Mathlib.Algebra.Polynomial.Roots`
- `Mathlib.Algebra.Ring.GeomSum`
- `Mathlib.Analysis.Complex.Basic`
- `Mathlib.Analysis.Complex.Cardinality`
- `Mathlib.Analysis.Complex.Circle`
- `Mathlib.Analysis.Complex.Polynomial.Basic`
- `Mathlib.Analysis.Fourier.FourierTransform`
- `Mathlib.Analysis.InnerProductSpace.Defs`
- `Mathlib.Analysis.Matrix.MeasurableSpace`
- `Mathlib.Analysis.Normed.Module.FiniteDimension`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Mathlib.Analysis.Real.Sqrt`
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle`
- `Mathlib.Analysis.SpecialFunctions.Pow.Complex`
- `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- `Mathlib.Basic.Complex.Basic`
- `Mathlib.CategoryTheory.Discrete.Basic`
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`
- `Mathlib.CategoryTheory.Skeletal`
- `Mathlib.Data.Fin.Rev`
- `Mathlib.Data.Int.LeastGreatest`
- `Mathlib.Data.Matrix.Block`
- `Mathlib.Data.Nat.Find`
- `Mathlib.FieldTheory.Finite.Basic`
- `Mathlib.FieldTheory.RatFunc.AsPolynomial`
- `Mathlib.GroupTheory.Coset.Defs`
- `Mathlib.GroupTheory.DoubleCoset`
- `Mathlib.GroupTheory.GroupAction.ConjAct`
- `Mathlib.GroupTheory.GroupAction.Quotient`
- `Mathlib.LinearAlgebra.BilinearMap`
- `Mathlib.LinearAlgebra.Charpoly.ToMatrix`
- `Mathlib.LinearAlgebra.Dimension.Basic`
- `Mathlib.LinearAlgebra.Dual.Lemmas`
- `Mathlib.LinearAlgebra.Matrix.Block`
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`
- `Mathlib.LinearAlgebra.Matrix.Diagonal`
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic`
- `Mathlib.LinearAlgebra.Matrix.Kronecker`
- `Mathlib.LinearAlgebra.Matrix.Permutation`
- `Mathlib.LinearAlgebra.Matrix.Reindex`
- `Mathlib.LinearAlgebra.Matrix.Transvection`
- `Mathlib.Logic.Equiv.Fin.Basic`
- `Mathlib.MeasureTheory.Constructions.Pi`
- `Mathlib.MeasureTheory.Function.LocallyIntegrable`
- `Mathlib.MeasureTheory.Group.Integral`
- `Mathlib.MeasureTheory.Group.LIntegral`
- `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`
- `Mathlib.MeasureTheory.Integral.Bochner.Set`
- `Mathlib.MeasureTheory.Integral.Marginal`
- `Mathlib.MeasureTheory.Measure.Haar.Basic`
- `Mathlib.MeasureTheory.Measure.Haar.DistribChar`
- `Mathlib.MeasureTheory.Measure.Haar.Unique`
- `Mathlib.MeasureTheory.Measure.Regular`
- `Mathlib.NumberTheory.LocalField.Basic`
- `Mathlib.NumberTheory.Padics.LocalField`
- `Mathlib.NumberTheory.Padics.RingHoms`
- `Mathlib.Order.Atoms`
- `Mathlib.Order.Interval.Set.Infinite`
- `Mathlib.RepresentationTheory.Basic`
- `Mathlib.RepresentationTheory.Coinduced`
- `Mathlib.RepresentationTheory.Coinvariants`
- `Mathlib.RepresentationTheory.Intertwining`
- `Mathlib.RepresentationTheory.Invariants`
- `Mathlib.RepresentationTheory.Irreducible`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Mathlib.RepresentationTheory.Subrepresentation`
- `Mathlib.RingTheory.Algebraic.LinearIndependent`
- `Mathlib.RingTheory.DedekindDomain.IntegralClosure`
- `Mathlib.RingTheory.FiniteLength`
- `Mathlib.RingTheory.Finiteness.Basic`
- `Mathlib.RingTheory.FractionalIdeal.Operations`
- `Mathlib.RingTheory.Ideal.Quotient.Operations`
- `Mathlib.RingTheory.Length`
- `Mathlib.RingTheory.Localization.Ideal`
- `Mathlib.RingTheory.Noetherian.Basic`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.RingTheory.RamificationInertia.Basic`
- `Mathlib.RingTheory.SimpleModule.Basic`
- `Mathlib.RingTheory.Trace.Basic`
- `Mathlib.RingTheory.Valuation.Integral`
- `Mathlib.Tactic.Linarith`
- `Mathlib.Tactic.NoncommRing`
- `Mathlib.Topology.Algebra.ContinuousMonoidHom`
- `Mathlib.Topology.Algebra.Group.Basic`
- `Mathlib.Topology.Algebra.Group.Matrix`
- `Mathlib.Topology.Algebra.Group.Quotient`
- `Mathlib.Topology.Algebra.Group.Subgroup`
- `Mathlib.Topology.Algebra.Group.Units`
- `Mathlib.Topology.Algebra.Module.FiniteDimension`
- `Mathlib.Topology.Algebra.Module.ModuleTopology`
- `Mathlib.Topology.Algebra.Nonarchimedean.Basic`
- `Mathlib.Topology.Algebra.OpenSubgroup`
- `Mathlib.Topology.Algebra.Ring.Compact`
- `Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology`
- `Mathlib.Topology.Algebra.Valued.NormedValued`
- `Mathlib.Topology.Bases`
- `Mathlib.Topology.Compactness.Compact`
- `Mathlib.Topology.Compactness.LocallyCompact`
- `Mathlib.Topology.Connected.TotallyDisconnected`
- `Mathlib.Topology.ContinuousMap.CompactlySupported`
- `Mathlib.Topology.Homeomorph.Quotient`
- `Mathlib.Topology.Instances.NNReal.Lemmas`
- `Mathlib.Topology.LocallyConstant.Algebra`
- `Mathlib.Topology.LocallyConstant.Basic`
