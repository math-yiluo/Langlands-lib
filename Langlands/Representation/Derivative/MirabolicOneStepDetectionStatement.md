# Joint detection by the one-step mirabolic minus functors

Authors: Worker 700 wrote the Lean statement and this Markdown. Workers 749
and 1024 checked the interface against the highest-derivative pairing
consumer and identified the separate boundary and iteration obligations.
Worker 237 rechecked the module at the submission base and updated the
check and import-closure records.

`Langlands.Derivative.MirabolicOneStepDetection.{uF,uV} F T` is an
unproved proposition definition. Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The field and representation-carrier universes are independent, and the
supplied topology is installed.

For every nontrivial continuous unitary additive character `ψ`, every
`n : ℕ`, and every actual smooth complex representation `A` of
`GeneralLinear.mirabolic (n+1) F.Carrier`, it asserts that

```lean
Subsingleton ((Mirabolic.psiMinus T (n+1)).obj A) →
Subsingleton ((Mirabolic.phiMinus T ψ n).obj A) →
Subsingleton A
```

These are assertions about the actual underlying vector spaces. Since these
spaces are additive groups, `Subsingleton` says every vector equals zero.
No categorical zero-object choice or chosen constituent is used. Both
quotients must vanish; the statement does not assert detection by either
one-step quotient alone.

The sole direct project import is the published
`Langlands.Representation.Derivative.MirabolicMinus`. Its normalized
`psiMinus T (n+1)` has source `P_(n+2)` and target `GL_(n+1)`.
Its normalized `phiMinus T ψ n` has the same source and target `P_(n+1)`.
The Library's `mirabolic r` is the source's `P_(r+1)`. The carriers are the
actual quotients by the spans of the trivial-character and last-coordinate
character relations for `radical (n+1) F.Carrier`. The determinant
inverse-half twists change actions and preserve carriers and linear maps.

There is no finite-length, admissibility, Artinianity, irreducibility,
homogeneity, segment, product, head, socle or classification premise.
The assertion includes arbitrary infinite-dimensional smooth
representations. At `n=0` its source is `P_2`, with targets `GL_1` and
`P_1`. It makes no assertion involving a nonexistent `P_0` or an order-zero
mirabolic derivative. All-order detection also needs the separate elementary
`P_1 → GL_0` boundary, whose radical is trivial; that boundary is outside
this proposition. The relevant implication is
`Subsingleton ((Mirabolic.psiMinus T 0).obj A) → Subsingleton A`.
The passage from higher-derivative vanishing to vanishing of an iterated
`phiMinus` also needs an induction and the arithmetic transports in
`mirabolicDerivativeOfOrder`. Neither that implication nor those iteration
bridges are asserted here. Every occurrence of `phiMinus` in an eventual
induction must use the same universally quantified `ψ`.

The original source is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Proposition 3.2(e), printed p.451 / one-based PDF page 12, gives the
exact sequence of functors

```text
0 → Φ⁺ Φ⁻ → Id → Ψ⁺ Ψ⁻ → 0.
```

Applied to a smooth representation, this sequence implies the stated joint
detection: if both minus outputs vanish, both outside terms vanish and
exactness forces the middle representation to vanish. This is a derived
consequence of that sequence, rather than a claim that BZ77 states the
Library's `Subsingleton` packaging. The sequence and its proof references
were read, including inspection of the rendered original PDF page.
The source refers the relevant part of its proof to reference [1], §5;
a later proof that follows that route must read and prove those lower
inputs. No exact sequence is assumed or proved in this statement unit.

Section 3.5, printed p.452 / PDF page 13, obtains the general derivative
filtration by iteration. The present statement is a smaller possible input
to all-order derivative detection and needs neither a segment derivative
formula nor strong indecomposability. This file does not prove an
induction, a positive-level assertion, exactness, adjunction, a plus-functor
identity or a canonical filtration.

The inherited determinant normalization uses exponent `-1/2`.
The construction does not identify determinant norm with the source's Haar
automorphism modulus. That comparison remains a separate obligation.
For this one-step vanishing implication, output twists preserve the
quotient carriers, so carrier vanishing agrees with that of the
unnormalized minus quotients; no Haar-modulus identification is needed
to formulate the assertion.

No source-specific errata note was found in the supplied public notes.
The earlier search for corrections to the relevant BZ77 derivative theory
found no applicable correction; this records the search rather than
asserting that no erratum exists.

This statement is general BZ77 theory upstream of all-order detection.
It must be proved independently of that consumer, the combined mirabolic
strong-indecomposability reduction and all segment, head, socle,
classification and two-supercuspidal product conclusions excluded by its
task contract. The complete union of consumer exclusions is preserved in
that contract and must be copied to proof successors and lower splits.
A citation, proposition definition, draft or pending proof is not a
proved dependency.

This is the joint-detection consequence within U1 of the highest-derivative
pairing proof task `a925b519-9bb9-4927-873e-ad322d41328e`. It supplies none of
U1's stronger radical-triviality or kernel/plus identifications, U2's
adjunction and lattice statements, or U3's pairing transfer. Workers 749
and 1024 confirmed that the proposed interface matches their consumer.
Workers 501 and 895 confirmed that their completed unequal-rank work owns
no general joint-detection or shared Fourier prerequisite. This statement
does not use their nonzero-pairing theorem to infer detection.

No minus exactness is imported or assumed. The proof task for minus
exactness, `b65bc667-6951-4bd5-82af-10fb7046df7f`, is under operator pause;
this unit neither duplicates it nor requests its resumption.

The published module `Langlands.Representation.Derivative.MinusVanishing`
already contains the theorem
`Langlands.Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus`.
Its conclusion, for fixed `T`, `ψ` and `m`, is this proposition's body at
`n = m`. This statement module does not import `MinusVanishing`, and this
unit makes no claim about that theorem's independence from the excluded
consumers. A proof successor that reuses it must audit its proof and import
closure against the full exclusion set first.

The first development check, `954d2112-695f-4c0b-b868-27714ac72a8b`, used
approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The submission
recheck `61c2890c-22e0-422b-ad2b-ce936024dd81` used the same environment at
Library base `d8292e5e2ee514f9410e96a37b722b57f1e9de93`. Both compiled this
module with zero errors and warnings. The recheck inspected the unapplied
declaration. It reported `statement_returns_prop: true`, universe parameters
`uF`, `uV`, and only `propext`, `Classical.choice`, `Quot.sound`. These are
development observations, not proof, semantic acceptance or Library
publication.

The complete transitive project import closure was rechecked against
Library commit `d8292e5e2ee514f9410e96a37b722b57f1e9de93`. An earlier check
used commit `84ad0affe3e3e8feae73b57da624fc1f16a6923b`. At the new base,
every Lean and Markdown dependency is byte-identical to its published,
nonempty pair. There are 50 project dependencies, with no missing or
unpaired module; the entry statement is additional. This closure is a
subset of the separately audited all-order detection statement's closure.
Its mathematical contents are local-field
and matrix-group constructions, smooth representation/category foundations,
character twists, actual localized coinvariants, their functoriality and
smoothness, and elementary Whittaker character identities. The
`Whittaker.GeneralLinear` dependency constructs the positive standard
character; it imports no Whittaker-model existence or classification theorem.
No plus construction, exactness statement, filtration, derivative-level
construction, segment, parabolic product, head, socle, classification or
two-supercuspidal product module occurs. The statement itself has no proof
dependency beyond these constructions; in particular no excluded conclusion
is supplied as a premise.

The following list records all 50 project dependencies. Standard Mathlib
imports are outside this project-module list.

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
