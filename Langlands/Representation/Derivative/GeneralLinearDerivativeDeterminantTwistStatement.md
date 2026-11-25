# Determinant twists and actual general-linear derivatives

This module defines
`Langlands.Derivative.GeneralLinearDerivativeDeterminantTwistStatement`.
It supplies a proposition for a separate proof; it proves no derivative
comparison or irreducibility assertion.

The parameters are an arbitrary prime `p`, a supplied
`F : PadicField.{uF} p`, and `T : F.TopologicalData`. The field and
representation universes `uF` and `uV` are independent. With the topology of
`T` installed, the proposition quantifies over every supplied nontrivial
unitary additive character `ψ`, every source rank `N`, every derivative order
`k` with `hk : k ≤ N`, and every real exponent `s`.

Write `D` for the actual functor `generalLinearDerivative T ψ N k hk`,
and write `Twist_m(s)` for the actual smooth endofunctor
`SmoothRep.twistFunctor (T.determinantPowerCharacter m s)
(T.isOpen_ker_determinantPowerCharacter m s)` on representations of `GL_m(F)`.
The assertion is the existence of a natural isomorphism

`Twist_N(s) ⋙ D ≅ D ⋙ Twist_(N-k)(s)`.

Functor composition is in application order: the left side first twists the
source, then takes its derivative. At every actual source object `A`, an
isomorphism component therefore identifies
`D(A ⊗ |det_N|^s)` with `D(A) ⊗ |det_(N-k)|^s`. It is natural for all
actual smooth intertwiners. The existential wrapper is `Nonempty`, so the
declaration returns `Prop` while retaining an actual natural isomorphism as its
witness. This is stronger than an equality of Grothendieck classes or equality
of supports.

The exponent is the same on both groups. `D` uses the published normalized
minus functors, including their determinant exponent `-1/2`; the proposed
commutation introduces no additional normalization shift. There is no
finite-length, admissibility, irreducibility, segment or induction hypothesis.
The statement includes `k = 0`, `k = N`, `N = 0`, and zero representations.
Its carrier universe is the arbitrary existing `uV`; a consumer may
instantiate it with `max uF uV` for actual induced representations without
identifying the base universes.

## Source and derivation

This is a derived general derivative statement. Its source is Bernstein and
Zelevinsky, *Induced representations of reductive p-adic groups I* (1977),
registered as `bernstein-zelevinsky-1977-induced-i`, retained source SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant passages are Proposition 1.9(f), printed p.445, the mirabolic
subgroups and normalized minus-functor definitions in §§3.1–3.2,
pp.450–451, and the iterated derivative definition in §3.5, p.452.
The latter is a passage in BZ77, not the segment derivative formula in
Zelevinsky 1980 §3.5.

Proposition 1.9(f) describes how a character twist passes through localization,
with the corresponding change in the localizing character. A determinant
character is trivial on each unipotent radical used by the minus functors.
Consequently that change leaves the localizing character unchanged.
Restriction to the embedded smaller general-linear or mirabolic group
restricts `|det|^s` to its same-exponent determinant character.
The normalization twist commutes with this scalar twist. Iterating these
observations through `Φ⁻` and `Ψ⁻`, and restricting from the source
general-linear group, gives the displayed proposed natural comparison.
This paragraph explains the mathematical derivation of the target; the module
contains no implementation of that argument.

## Existing definitions and use

`Derivative.Iteration` defines restriction, normalized iterated minus
functors, rank transports and the actual functor for every `k ≤ N`.
`Classification.SupercuspidalTwist` supplies the already published
determinant-power character and its open-kernel theorem. The present
proposition uses those character definitions and the general smooth twist
functor. The filename of that import imposes no supercuspidal hypothesis.
No new character, derivative, localization or representation model is defined.

The motivating consumer is the special-head product
irreducibility criterion `SegmentHeadProductIrreducibility`. Its published
general highest-derivative pairing bridge
produces a quotient from a derivative of a modulus-twisted dual.
Specializing this statement to `s = 1` would move that modulus twist to the
output derivative. With its proof (`generalLinearDerivativeDeterminantTwist` in
`GeneralLinearDerivativeDeterminantTwistProof`), the comparison can
therefore be combined with actual dual-product support constructions.
This statement supplies none of the support comparison, nonlinkage
combinatorics, linked converse or product irreducibility proof.

## Independence boundary

The statement uses only the two named definition-level imports. Its proof
uses only general
Bernstein–Zelevinsky derivative/localization and character-twist foundations,
with these exclusions: no Zelevinsky 1980 §3.5 or §9.6 segment
derivative formula or its proof; no special-head product criterion in
either direction; no downstream segment, head, socle, full Jacquet formula or
classification conclusion; and no segment-socle part of the derivative
statements (`SegmentSocleDerivativesStatement`).
The stronger internal length-two helpers of the published support-only proof
are not inputs to this statement or a route for its proof.

The native import closure and inherited-pair comparison are recorded below.

The recursive native import traversal contains 61 project modules, including
this entry, and 56 direct external roots. Each of the 60 inherited Lean and
Markdown pairs is byte-identical to the current published Library and to the
previously audited terminal-support closure. There are no missing imports or
paired Markdown files. A scan of code after removing comments and strings
finds no proof holes, new axioms, prohibited execution syntax or excluded
declaration name. The closure contains no segment or head module and no
segment derivative, socle, Jacquet formula or classification conclusion.
Its only derivative modules are this statement, `Iteration`, `MirabolicMinus`
and `MirabolicCharacter`; its only Classification modules are `Supercuspidal`
and `SupercuspidalTwist`. The normalization and quotient constructions are
therefore the existing general definitions.

The exclusions also cover, for the separate proof, the conclusions of
`GenericSegmentProductUniqueness`,
multisegment exhaustion,
ordered strong-head existence,
quotient coverage,
ordered conversion,
tempered uniqueness,
`SquareIntegrableLanglandsClassification`,
square-integrable exhaustion,
regular exhaustion,
`SegmentFullJacquetFormula`,
`SegmentSocleJacquetFormula`,
`SegmentHeadJacquetFormula`,
`SegmentSpecialJacquetExponentNormFormula`,
`SegmentSocleProductIrreducibility`, and the consuming criterion
`SegmentHeadProductIrreducibility` itself.
The published proposition alone is not a proved input to that consumer.

### Project modules

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement`
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Classification.Supercuspidal`
- `Langlands.Representation.Classification.SupercuspidalTwist`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistStatement`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Jacquet.CharacterTwistEquiv`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement`
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceProof`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceStatement`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.FixedVectors.Definitions`
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
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement`
- `Langlands.Representation.Unitary.Basic`
- `Langlands.Representation.Whittaker.Algebraic`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Topology.CompactNormCharacter`
- `Langlands.Topology.Nonarchimedean.Subgroup`

### External roots

- `Lean.Elab.Tactic.Omega`
- `Mathlib.Algebra.BigOperators.Fin`
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Mathlib.Algebra.CharP.Basic`
- `Mathlib.Algebra.Group.Hom.Instances`
- `Mathlib.Algebra.Order.Archimedean.Basic`
- `Mathlib.Algebra.Polynomial.Lifts`
- `Mathlib.Algebra.Ring.GeomSum`
- `Mathlib.Analysis.Complex.Basic`
- `Mathlib.Analysis.Complex.Circle`
- `Mathlib.Analysis.InnerProductSpace.Defs`
- `Mathlib.Analysis.Normed.Module.FiniteDimension`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- `Mathlib.CategoryTheory.Skeletal`
- `Mathlib.Data.Matrix.Block`
- `Mathlib.FieldTheory.Finite.Basic`
- `Mathlib.GroupTheory.GroupAction.ConjAct`
- `Mathlib.LinearAlgebra.Matrix.Block`
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic`
- `Mathlib.LinearAlgebra.Matrix.Reindex`
- `Mathlib.Logic.Equiv.Fin.Basic`
- `Mathlib.MeasureTheory.Integral.Bochner.Set`
- `Mathlib.MeasureTheory.Measure.Haar.Basic`
- `Mathlib.NumberTheory.Padics.LocalField`
- `Mathlib.NumberTheory.Padics.RingHoms`
- `Mathlib.Order.Atoms`
- `Mathlib.RepresentationTheory.Basic`
- `Mathlib.RepresentationTheory.Coinvariants`
- `Mathlib.RepresentationTheory.Intertwining`
- `Mathlib.RepresentationTheory.Invariants`
- `Mathlib.RepresentationTheory.Irreducible`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Mathlib.RepresentationTheory.Subrepresentation`
- `Mathlib.RingTheory.DedekindDomain.IntegralClosure`
- `Mathlib.RingTheory.FiniteLength`
- `Mathlib.RingTheory.Finiteness.Basic`
- `Mathlib.RingTheory.Noetherian.Basic`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.RingTheory.RamificationInertia.Basic`
- `Mathlib.RingTheory.Valuation.Integral`
- `Mathlib.Tactic.Linarith`
- `Mathlib.Tactic.NoncommRing`
- `Mathlib.Topology.Algebra.ContinuousMonoidHom`
- `Mathlib.Topology.Algebra.Group.Matrix`
- `Mathlib.Topology.Algebra.Group.Units`
- `Mathlib.Topology.Algebra.Module.FiniteDimension`
- `Mathlib.Topology.Algebra.Nonarchimedean.Basic`
- `Mathlib.Topology.Algebra.OpenSubgroup`
- `Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology`
- `Mathlib.Topology.Algebra.Valued.NormedValued`
- `Mathlib.Topology.Bases`
- `Mathlib.Topology.Connected.TotallyDisconnected`
- `Mathlib.Topology.Instances.NNReal.Lemmas`
- `Mathlib.Topology.LocallyConstant.Basic`
