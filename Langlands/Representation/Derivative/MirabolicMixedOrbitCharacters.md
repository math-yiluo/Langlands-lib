# Positive characters at the actual mixed-orbit representatives

Author: Worker 499.

This internal helper calculates the positive ambient character on each of
the four actual radical intersections from `MirabolicMixedOrbitData`.
It factors the actual coefficient homomorphisms through the source
radical, proves the two surviving positive-character identities and the
right identity's trivial-character identity, and proves a linear
vanishing result at the left cycle. All ranks include zero values of
the two indexing parameters.

## Provenance and conventions

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, retained PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 1.8, printed pp.444–445 (PDF pp.5–6), defines character
localization. Sections 3.1–3.2, printed pp.450–451 (PDF pp.11–12), fix
the positive last-coordinate character and the minus functors.
Section 4.12(II),(III), printed pp.456–458 (PDF pp.17–19), specifies the
mixed subgroups. Section 7.2, printed p.471 (PDF p.32), gives the cycles
for 4.13(b,c). These passages and the cycle page image were read during
the host development. A bounded project and literature errata search
found no specific BZ77 errata entry; this is no global absence assertion.

The source supplies the groups, representatives, character and intended
comparisons. The source-radical homomorphisms, their factorizations and
the proofs below are internal derived content. They follow from the
explicit coefficient formulas in `MirabolicMixedOrbitRadicals` and the
coordinate formula `Derivative.Mirabolic.theta_radicalElement`. The
source leaves the comparison details to the reader; this helper does
not import those comparisons as proved inputs.

Write `K=k+1`, `m=r+2`, `n=k+r+3`, and `t=k+r+1`. The ambient group is
`mirabolic (k+r+2) R = P_n`, and an ambient radical column `v` has
length `k+r+2`. Its positive character is

```text
(theta ψ (k+r+1) U(v) : ℂ) = ψ.complex (v[t]).
```

The source is `mirabolic (r+1) R = P_m`, and its radical column has
length `r+1`. Its positive character is `theta ψ r`, evaluating that
column at coordinate `r`. All coordinates are zero based.
Representative `0 : Fin 2` is the published descending cycle;
representative `1` is the identity. The underlying radical helper
uses the actual inverse conjugation `w⁻¹ U(v) w` and actual rank
transport `rankCast (totalRank_eq k r)`, without changing either map.

The algebraic declarations require only `[CommRing R]`.
Character declarations additionally use an arbitrary topology on `R`
and `ψ : UnitaryAdditiveCharacter R`, whose data include continuity
and nontriviality. Only the two continuity theorems additionally
require `[IsTopologicalRing R]`.

## Actual source-radical maps

`leftRadicalCoefficient_mem_radical` proves that the second component
of the actual left coefficient belongs to `radical (r+1) R`.
`rightRadicalCoefficient_mem_radical` proves the same for the first
component of the actual right coefficient. Each proof writes an
arbitrary intersection element in its actual radical coordinates and
applies the corresponding complete coefficient formula.

The definitions `leftRadicalSource` and `rightRadicalSource` package
these components as monoid homomorphisms into that source radical.
Their group laws follow by projecting the group laws of the actual
coefficient homomorphisms and using subtype extensionality. Thus these
maps retain the original coefficient maps rather than choosing new
coordinate maps.

`leftRadicalCoefficient_eq` and `rightRadicalCoefficient_eq` establish
the entire pairs

```text
leftRadicalCoefficient  i u = (1, (leftRadicalSource  i u).val)
rightRadicalCoefficient i u = ((rightRadicalSource i u).val, 1).
```

These equalities include the GL component. The element theorems
`leftRadicalSource_element` and `rightRadicalSource_element` recover
the explicit columns of the radical helper by projecting its complete
coefficient identities.

`continuous_leftRadicalSource` and
`continuous_rightRadicalSource` use the induced topology on the source
radical. Their proofs compose the published coefficient continuity
with the relevant product projection and then pass to that induced
topology. No openness, surjectivity or geometric identification of
these maps is asserted.

## Restricted ambient characters

`leftOrbitTheta i` and `rightOrbitTheta i` compose the ambient positive
`theta ψ (k+r+1)` with the actual intersection subtype. They are
homomorphisms to `ℂˣ`. Their element formulas evaluate to
`ψ.complex (v[t])` on every actual `U(v)` in the relevant intersection.
No inverse character is inserted.

The implemented identities are:

| Actual representative | Ambient character on its radical intersection |
| --- | --- |
| Left identity (`1`) | `(theta ψ r).comp (leftRadicalSource k r 1)` |
| Right cycle (`0`) | `(theta ψ r).comp (rightRadicalSource k r 0)` |
| Right identity (`1`) | The constant identity homomorphism |
| Left cycle (`0`) | A translation exists with complete coefficient `1` and complex character value different from `1` |

`leftOrbitTheta_one` represents an arbitrary intersection element as
`U(v)`. The left identity's source column is `j ↦ v[k+1+j]`.
At its terminal coordinate `j=r` this is `v[t]`; the proof establishes
the exact `Fin` index equality and applies the positive character.
It proves equality of the unit-valued homomorphisms.

`rightOrbitTheta_zero` similarly uses the right cycle's actual
membership witness. Its source column has terminal entry `v[t]`;
the earlier entries are the first `r` ambient coordinates. Evaluating
at the source terminal coordinate proves the displayed unit-valued
homomorphism equality.

`rightOrbitTheta_one` applies the radical helper's consequence that
the ambient terminal coordinate is zero on the right identity
intersection. The additive character of zero is one, proving that the
restricted ambient character is the identity homomorphism. This
identity concerns the ambient character alone; the source radical
coefficient at this representative can be nontrivial.

`exists_leftOrbitTheta_zero_ne_one` first derives some `c : R` with
`ψ.complex c ≠ 1` from the bundled nontriviality of `ψ`. If every
complex value were one, extensionality of the circle-valued additive
character would contradict that nontriviality. It then takes the
actual radical translation whose column is supported only at `t`
with value `c`. The radical helper proves that its entire left
cycle coefficient is the identity. The ambient character evaluates
to `ψ.complex c`, as required.

## Linear vanishing at the left cycle

`leftOrbitTheta_zero_equivariant_eq_zero` allows arbitrary complex
representations

```text
σ : Representation ℂ (GL_(k+1)(R) × P_(r+2)(R)) V
```

and arbitrary complex linear maps `f : V →ₗ[ℂ] W`, with independent
carrier universes `uV` and `uW`. Its hypothesis is the explicit
equivariance equation

```text
f (σ (leftRadicalCoefficient k r R 0 u) v)
  = (leftOrbitTheta k r ψ 0 u : ℂ) • f v.
```

The theorem concludes `f=0`. It selects the translation just
constructed. Its coefficient identity reduces equivariance to
`f v = θ(u) • f v`. Consequently `(θ(u)-1) • f v=0`; the complex
scalar is nonzero, so `f v=0` for every `v`. This proof uses no
smoothness or finite-dimensional hypothesis on either carrier.

This is a statement about explicit linear equivariance. It does not
identify an induced representation with an orbit piece, construct a
filtration, or claim a normalized Phi comparison. Those constructions,
their natural maps, determinant normalizations and exactness remain
separate host obligations.

## Proof-dependency and inherited restriction audit

The direct imports are
`Langlands.Group.GL.MirabolicMixedOrbitRadicals` and
`Langlands.Representation.Derivative.MirabolicCharacter`.
The former supplies the actual matrix coefficient formulas. The latter
supplies the positive character and its coordinate evaluation.
All new proof bodies use those formulas, radical coordinates,
product/subtype extensionality, monoid-homomorphism laws, induced
topology, character nontriviality, elementary complex scalar algebra
and finite-index arithmetic. The `omega` calls prove only index
bounds and equalities.

The character module's transitive imports include ordinary character
localization, smooth pullback/subquotient/twist proofs, continuous
character open-kernel infrastructure and elementary Whittaker
character/matrix-coefficient laws. These constructions and elementary
laws require no finiteness, segment, classification or derivative
comparison input. The present proofs use neither the Whittaker
restriction theorem nor the character open-kernel theorem.
The concrete orbit root contributes stabilizer definitions, not a
geometric-lemma proof or any orbit-coverage assertion.

Every row below covers direct and transitive proof dependencies.
Excluded families include their mathematical conclusions, parent
tasks, proof successors and downstream consequences.

| Host condition or excluded family | Audit of this helper |
| --- | --- |
| Actual coefficients and rank transports | The source maps are restrictions of the published coefficient projections. Both GL components are proved to be `1`. The underlying inverse conjugation, representatives and `totalRank_eq` transport are unchanged. |
| Arbitrary inputs and universes | Every `k,r : ℕ` is allowed. The ring universe and both carrier universes are independent. No admissibility, irreducibility, finite dimension, finite length, genericity, chosen vector, unit input or saturation hypothesis occurs. Zero carriers and repeated factors remain allowed. |
| Supplied topology and GL₀ boundary | The character uses any supplied coefficient topology. This successor-source helper concerns `P_(r+2)` only; it creates no `P_0`, applies no Phi to `P_1`, and imposes no condition on the host's entire arbitrary GL₀ carrier. |
| Plus functors and adjunction | No plus functor, plus comparison or adjunction theorem occurs in the closure or the proof. The matrix `plusSubgroup` in the concrete data is permitted group infrastructure. |
| BZ77 4.13(d), general Leibniz and derivative comparisons | No submodule-detection, general Leibniz, derivative-filtration or minus-comparison conclusion is used. Imported filtration and localization definitions are not treated as proofs of comparisons. |
| Orbit geometry, normalization and exactness | No orbit cover, disjointness, openness, Haar-scaling or induction theorem supplies a premise. This helper proves none of the six host clauses or their natural maps. |
| Segment derivative and Jacquet formulas | No Ze80 §3.5 or §9.6 result, `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula` or `SegmentSpecialJacquetExponentNormFormula` supplies an input. |
| Individual segment existence | No individual special-head/reverse-socle or segment-socle/reverse-head existence is used. |
| Linked and unlinked socle consumers | `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom` are absent as inputs. |
| Segment product, commutation and gluing | No `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing` or Ze80 4.2 or 9.7 criterion is used. |
| Special-head criterion and generic uniqueness | Neither `SegmentHeadProductIrreducibility` nor `GenericSegmentProductUniqueness` supplies an input. |
| Ordered existence and multisegment exhaustion | No `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, ordered strong-head existence, special-head multisegment exhaustion, quotient coverage or ordered conversion supplies an input. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, `SegmentSpecialEssentialSquareIntegrability`, tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither `TwoSupercuspidalNonadjacentProductIrreducible` nor `TwoSupercuspidalProductStructure` or its full-product assembly supplies an input. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and single-block finiteness | No `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block conclusion or arbitrary-character finiteness theorem supplies an input. |
| Other Whittaker finiteness exclusions | Neither `IrreducibleCoinvariantFinitenessStatement` nor `LeviCuspidalCoinvariantFinitenessStatement` supplies an input. No prohibited mirabolic finite-length route through that finiteness occurs. The elementary Whittaker character definitions and laws in the closure assert no such finiteness. |
| Published-input requirement | Both direct roots and all 44 imported project pairs are published and were checked unchanged against the audited Library commit. Proposition definitions, citations and pending derivative proofs supply no mathematical premise. No downstream consumer conclusion is used upstream. |
| Separate owners and run controls | The helper does not duplicate restriction-sequence or exactness work, invoke a consumer as an upstream premise, or alter Worker 127's operator pause, Worker 8's suspension or Worker 114's hold. |

The audit against published Library commit
`cb42061b82d3b398d42ee1f25159daec0f54e40d` finds the 44 project imports
listed below. Every imported Lean/Markdown pair is byte-identical to
that Library and matches its manifest, including the radical-calculation
prerequisite. The complete independent semantic review of that prerequisite
and its accepted publication were verified before this submission. A source scan finds no inherited excluded
task identifier or any of the 24 named consumer declarations in Lean
code, and no proof holes, new axioms or unsafe evaluation commands.
Occurrences of excluded names in paired Markdown explain independence.
The inspection of the terminal vanishing theorem reports only
`propext`, `Classical.choice` and `Quot.sound`, with independent level
parameters `u`, `uV`, `uW`. Development checking supplies no independent
semantic acceptance or publication.

## Complete project import closure

This list contains both direct roots and every transitive project
import, excluding the current module. Mathlib uses the supplied pinned
environment and has not been modified.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.Nonarchimedean.Subgroup
```
