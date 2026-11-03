# Actual quotients from derivatives of the untwisted smooth dual

Author: Worker 357.

This internal construction composes the published highest-derivative
constituent quotient with the published natural determinant-twist isomorphism.
It retains an actual irreducible admissible invariant subspace S of the
order-k derivative of A and a surjection from the order-k derivative of
A's smooth contragredient onto the inverse determinant-twist of S's smooth
dual. Nonzero, finite-length and highestness hypotheses on the left derivative
remain explicit. The entire left derivative is not asserted irreducible.

The construction first takes the published actual quotient from the derivative
of the determinant-twisted dual onto S's smooth dual. The inverse component of
the natural derivative-twist isomorphism moves the determinant character to
the output of the derivative. Twisting this map by the inverse character and
cancelling the source twists gives the retained surjection. Both operations
preserve surjectivity. The generic cancellation isomorphism and source-untwist
map use the existing twist algebra laws on actual carriers and maps.

The returned structure contains the literal invariant subspace, its
irreducibility and admissibility, the actual quotient map, and its
surjectivity proof. Its target is the inverse-character-twisted smooth dual
of that subrepresentation. Under compact-open cofinality, admissible duality
and twist preservation show that target is irreducible and admissible.
The targetDualIso construction applies the actual contragredient-twist
isomorphism, cancels the inverse of the inverse character, and twists the
inverse admissible bidual isomorphism. Thus the dual of the target is actually
isomorphic to the original subrepresentation twisted by the determinant
character with exponent one.

All fields use actual smooth representations and maps. The generic helpers
allow arbitrary commutative coefficient rings for source untwisting and
complex coefficients for admissible smooth duality. The final construction
allows arbitrary primes, fields, supplied topology and nontrivial continuous
unitary additive characters, independent field and carrier universes, every
positive feasible derivative order, and residual rank zero. Consumers may
specialize the carrier universe to max uF uV without changing the construction.

This is a direct internal composition of published constructions, with no
new original-source assertion. It assumes no support existence, support
uniqueness, segment derivative identification, classification or irreducibility
criterion. The full host SegmentHeadProductIrreducibility remains open.


## Declaration and actual maps

The selected definition is
`Langlands.Derivative.chooseGeneralLinearHighestDerivativeUntwistedQuotient`.
Its universe parameters `uF` and `uV` are independent. It takes arbitrary
`{p : ℕ} [Fact p.Prime]`, `{F : PadicField.{uF} p}`, the supplied
`T : F.TopologicalData`, and
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`.
After `N k : ℕ` and `hk : 0 < k ∧ k ≤ N + 1`, the supplied topology and
its general-linear topological-group instances at ranks `N + 1` and
`N + 1 - k` are installed. Its remaining inputs are the actual smooth
representation `A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (N + 1) F.Carrier)`,
nontriviality and finite length of `D_k A`, and subsingleton carriers for
all `D_j A` with `k < j ≤ N + 1`. Here `D_j` is the published actual
`generalLinearDerivative T ψ (N + 1) j hj` functor, with the explicit
bound proof `hj`.

Set `χ = T.determinantPowerCharacter (N + 1 - k) 1`. The output is actual
`UntwistedConstituentDualQuotientData (D_k A) (D_k A.contragredient) χ hχ`.
This new structure has an actual invariant subspace `S` of `D_k A`, its
irreducibility and admissibility, an actual smooth morphism
`D_k(A.contragredient) ⟶ S.contragredient.twist χ⁻¹ (isOpen_ker_inv hχ)`,
and surjectivity of its underlying intertwiner. The `target` abbreviation
is this literal codomain. No form or evaluation formula is retained in
this structure, and no uniqueness or canonicity of the chosen `S` is
asserted.

For the construction, put `B = A.contragredient.twist |det|` at rank
`N + 1`. Its representation is definitionally the modulus-twisted smooth
dual required by
`chooseGeneralLinearHighestDerivativeConstituentQuotient`; the supplied
representation equivalence is `equivOfRepresentationEq rfl`. That published
constructor supplies `S` and a surjective intertwiner `q : D_k B → S.dual`.
Bundle `q` with its explicit smooth source and target. The component `e` of
`DeterminantTwist.generalLinearDerivativeTwistIso T ψ 1 (N + 1) k hk.2`
at `A.contragredient` is an actual isomorphism
`D_k B ≅ (D_k A.contragredient).twist χ hχ`. Thus `e.inv ≫ q` is a
surjection from the latter twist. Its surjectivity follows by composing
the surjectivity of `q` with that of the equivalence underlying `e.symm`.

`SmoothRep.twistInverseCancelIso` bundles the published algebraic equality
`twist_inv_twist` as an actual smooth isomorphism. Its inverse, followed by
the inverse-twist functor applied to `e.inv ≫ q`, defines
`SmoothRep.untwistSourceHom`. The underlying map is definitionally the same
map as before, so `untwistSourceHom_surjective` reuses exactly its given
surjectivity proof. This yields the quotient field of the returned data.

For an arbitrary complex smooth pair `A,B` over a topological group,
`target_irreducible` and `target_admissible` use compact-open cofinality,
the retained admissibility of `S`, the proved smooth-duality theorems,
and the proved twist preservation theorems. `targetDualIso` applies
`SmoothRep.contragredientTwistIso` at `χ⁻¹`, proves `χ⁻¹⁻¹ = χ` by
`MonoidHom.ext`, `MonoidHom.inv_apply` and pointwise `inv_inv`, and
composes with the twist of `(SmoothRep.bidualIso hG S w.admissible).symm`.
This has exactly the direction `target.contragredient ≅ S.twist χ hχ`.
Compact-open cofinality is an explicit input to these generic conclusions;
it is not an extra input to the general-linear quotient constructor.

## Published inputs and independence

There are exactly two direct imports:

- `Langlands.Representation.Derivative.GeneralLinearHighestDerivativeConstituentQuotient`;
- `Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistProof`.

Both are independently accepted and published at Library commit
`e9121d2f8e2a84b24a5c3d710d82082ab261845c`. This unit uses their actual
constructors, not a Prop statement as a proved theorem. The first's
inherited route is the general BZ77 highest-derivative pairing, an
Artinian-atom subrepresentation, the general cuspidal embedding for
admissibility, and the smooth-dual quotient from a separating form.
The second's route is equality of character-localization relation
submodules, restriction of determinant characters, commuting twists,
and pasting actual natural isomorphisms. It uses no segment formula.
The generic smooth duality, biduality and twist theorems used here are
already in the first import's closure. No input is taken from the
support-twist helper or from a pending candidate.

A recursive native import audit has 202 project modules, including this
new module, and 119 directly named external import roots. All 201 inherited
Lean/Markdown pairs equal that Library commit byte for byte; every pair is
present with nonempty Markdown. The complete inventories follow below.
The six Classification modules are `ConstituentRelations`,
`MirabolicDerivativeContragredient`, `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`, and
`SupercuspidalTwist`. They supply lower predicates, actual constituent
relations, elementary twists and proved general pairing/duality helpers.
No segment, head, socle, multisegment, full Jacquet or classification
conclusion enters the closure. The inherited Whittaker, matrix-coefficient
and Rankin--Selberg infrastructure enters through the independently
published general pairing and cuspidal-embedding foundations, as documented
in the first direct import; no Whittaker coinvariant-finiteness conclusion
is used here.

The trusted operator responses
`/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md` and
`/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md`
permit fully proved, independently accepted general BZ77 derivative and
duality infrastructure, while preserving the host's exclusions. The
support-only permission
`/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md`
supplies no mathematical premise in this general quotient construction.
The later rulings
`/home/taskhub/pilot/correspondence/ed80148e21e7523abfc048f455e98eb0.md`,
`/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md`, and
`/home/taskhub/pilot/correspondence/ca18fd5005bf5e12a3f7cade18dca865.md`
were read in full and are unnecessary to this proof. In particular neither
`core_mid` nor its consequences, nor adjacent-product reducibility, is
used.

The complete import inventory, unchanged inherited pairs and proof-route
inspection exclude Ze80 3.5/9.6 and their proof successors; the segment-socle
part of `8e5b4563-0365-41c7-b134-70f2a0b36292`; segment head, socle and
full Jacquet formulas; two-supercuspidal product irreducibility or
structure; special-head product irreducibility in either direction;
`GenericSegmentProductUniqueness`; multisegment exhaustion; ordered
strong-head existence; quotient coverage; ordered conversion; tempered
uniqueness; `SquareIntegrableLanglandsClassification`; square-integrable
exhaustion; and regular exhaustion. No task or mathematical conclusion
listed under the host's Independence is used as an input under a new name.
A lexical source scan supplements these proof-route checks and reports no
prohibited-name hit, proof hole, new axiom, unsafe code or kernel-bypassing
command. Declaration inspection reports only `propext`, `Classical.choice`
and `Quot.sound`. Compilation is development evidence; independent semantic
review and publication are separate requirements.

This internal unit proves neither direction of the full repeated-segment
`Langlands.Classification.SegmentHeadProductIrreducibility.{uF,uV} F T`.
The support assembly, unlinked sufficient direction and linked converse
remain separate host obligations in the original universes.

## Complete project import closure

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
- `Langlands.Group.LeftQuotient`
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
- `Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistProof`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistStatement`
- `Langlands.Representation.Derivative.GeneralLinearHighestDerivativeConstituentQuotient`
- `Langlands.Representation.Derivative.GeneralLinearHighestDerivativeUntwistedQuotient`
- `Langlands.Representation.Derivative.HighestDerivativeConstituentQuotient`
- `Langlands.Representation.Derivative.Homogeneity`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.MinusVanishing`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement`
- `Langlands.Representation.Derivative.MirabolicDerivativeVanishing`
- `Langlands.Representation.Derivative.MirabolicDeterminant`
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

## Complete direct external import roots

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
- `Mathlib.Topology.Algebra.ProperAction.Basic`
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
