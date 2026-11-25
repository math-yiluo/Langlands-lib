# The rank-one boundary of mirabolic derivative detection

`Langlands.Derivative.MirabolicRankOneDetection.{uF,uV} F T` is a
proposition definition, proved separately by `mirabolicRankOneDetection`
(`MirabolicRankOneDetectionProof`), with outer telescope
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The field and representation-carrier universes are independent, and the
supplied topology is installed.

For every actual smooth complex representation `A` of
`GeneralLinear.mirabolic 0 F.Carrier`, the proposition asserts

```lean
Subsingleton ((Mirabolic.psiMinus T 0).obj A) → Subsingleton A
```

The Library's `mirabolic 0` is the source convention's `P_1`. The actual
normalized functor has target `GL_0`. `Subsingleton` concerns the actual
underlying vector spaces; it means that every vector is zero. The
assertion covers all smooth representations, including arbitrary
infinite-dimensional ones. It uses no additive character, chosen
constituent, finite-length, admissibility, irreducibility, Artinianity,
homogeneity, segment, product, head, socle or classification premise.
No `P_0` or order-zero derivative is introduced.

This is an internal elementary boundary assertion for general BZ77
mirabolic derivative detection. Its provenance is the published actual
quotient construction in
`Langlands.Representation.Derivative.MirabolicMinus`, together with the
triviality of the rank-one group, proved as
`GeneralLinear.Mirabolic.rankOne_eq_one` in `Langlands.Group.GL.Mirabolic`,
and of its radical, the instance `GeneralLinear.Mirabolic.radical_rankOneSubsingleton`
in `Langlands.Group.GL.MirabolicRadical`. The expected elementary proof route is
that every relation `ρ(u)v - v` is zero, so the quotient map is injective.
This statement module supplies no such proof.

The carrier of normalized `psiMinus T 0` is definitionally the quotient
by `Jacquet.Localization.relations A.representation (radical 0 F.Carrier) 1`.
The determinant inverse-half twist changes the action and preserves the
carrier. Thus this assertion about vanishing requires no comparison of
the determinant character with the source's Haar automorphism modulus.
That comparison remains separate from the general normalized theory.

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), is registered as `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 3.5, printed p.452 / one-based PDF page 13, gives the general
derivative filtration; section 3.2, printed p.451 / PDF page 12, gives its
lower functor identities and exact sequence. For `τ` in `Alg P_n`, the
`n`-th derivative `τ^(n) = Ψ⁻ (Φ⁻)^(n-1) (τ)` of section 3.5 applies `Ψ⁻`
to a representation of `P_1`; the present proposition concerns that last
step. Those passages motivate the all-order detection statement. The present rank-one `Subsingleton`
assertion is an internal consequence of elementary group and quotient
definitions, not a claim that the source states this Lean formulation.
The registered source passages were read for the detection route. No
source-specific applicable erratum was found in the project's literature
records; this does not assert that none exists.

The positive-rank joint-detection statement
`Langlands.Derivative.MirabolicOneStepDetection`
(`MirabolicOneStepDetectionStatement`, proved in
`MirabolicOneStepDetectionProof`) starts with `P_2`. The present proposition
addresses its missing `P_1` boundary. It neither implies nor assumes the
positive-rank assertion. It also proves no
derivative-order iteration bridge, positive-level assertion, exactness,
plus-functor identity, adjunction, canonical filtration or
strong-indecomposability result. An all-order proof must separately
establish the iteration bridges using the actual derivative construction.

The sole direct project import is the published
`Langlands.Representation.Derivative.MirabolicMinus`. The full import
closure contains no segment, parabolic-product, head, socle,
classification, plus-model or exactness module. No mirabolic minus
exactness theorem is assumed.

A check over Library commit
`7e295ceb7e82495464061fe18449b6e968161ab6` compiled the module with zero
errors and warnings. Inspection of the unapplied proposition reported
`statement_returns_prop: true`, independent universe parameters `uF`,
`uV`, and only `propext`, `Classical.choice`, `Quot.sound`. A separate
check confirmed by `rfl`
that the declaration at universes `uF, uV` is exactly the displayed
proposition over the telescope above. Compilation is not a
proof.

The complete transitive project import closure was audited against Library
commit `7e295ceb7e82495464061fe18449b6e968161ab6`. It consists of
`MirabolicMinus` and its 49 transitive project dependencies, 50 modules in
all. Each is byte-identical to its published Lean file and has a nonempty
published Markdown pair; there is no missing or unpaired project module,
and none contains `sorry` or an `axiom` declaration. The closure consists
of local-field and matrix-group constructions, smooth representation and
category foundations, character twists, actual localized coinvariants,
and their functoriality and smoothness. Its `Whittaker` dependencies
supply the standard character and algebraic Whittaker functional and model
constructions with elementary lemmas, not a Whittaker-model existence,
uniqueness or classification result. No excluded conclusion is assumed as
a premise. The entry proposition is additional to the following complete
list; standard Mathlib modules are outside this project-module list.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.Nonarchimedean.Subgroup
```
