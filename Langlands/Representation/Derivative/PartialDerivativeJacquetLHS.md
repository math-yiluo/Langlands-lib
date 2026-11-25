# Iterated minus quotients as partial character localizations

This internal construction identifies the entire carrier of the actual positive
ordinary derivative with a single partial character-localized quotient. Its
principal definition is `JacquetLHS.generalLinearLinearEquiv`. For every supplied
p-adic topological datum `T`, the same bundled unitary additive character `ψ`,
all `k j : ℕ` and every smooth representation `A` of `GL_(k+j+1)`, it gives

```
(generalLinearDerivativePositive T ψ k j).obj A
  ≃ₗ[ℂ] Localization.Coinvariants A.representation
    (PartialLocalization.partialUpper k (j+1))
    (PartialLocalization.character ψ.complex k (j+1)).
```

The universes of the field and representation carrier remain independent. The
carrier is the original `Type uV`, with no finite-length, admissibility,
irreducibility, dimension or genericity assumption. The actual functors and
quotient maps are unchanged. This module supplies a linear equivalence and both
representative formulas. It does not package `GL_k` equivariance or
naturality, or prove the final positive two-block comparison; those are in
`PartialDerivativeJacquetComparisonProof`. The auxiliary
induction is stated at all natural `k,j`; this is no claim about a two-block
shape with a zero block or the separate top-derivative comparison.

## Sources and internal provenance

The motivating source is Zelevinsky, *Induced representations of reductive
p-adic groups II* (1980), §3.7 and Proposition 3.7(b), printed p.182 / PDF p.19,
registered as `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The present module implements only the iterated-minus side of that comparison.

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §1.8(b), printed pp.444–445 / PDF pp.5–6, fixes localization by the span
of `ρ(u)v − θ(u)v` and the negative half normalization. Proposition 1.9(c),
printed p.445 / PDF p.6, motivates successive localization; §§3.5 and 4.3,
printed pp.452 and 454 / PDF pp.13 and 15, motivate the successive minus
construction. The registered identifier is `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Those original passages, including the inverse-half sign, were checked in a
source audit; no applicable registered erratum changes these conventions.

The proof itself is an internal specialization of the already published
`LocalizationTower` and `LocalizationTransport`, using the already published
actual recursive matrices and characters from `PartialLocalizationCharacter`.
The one-step transport organization adapts the `TopLocalizationStep`
construction (module `Derivative.TopLocalizationStep`) to the partial group;
this module does not import it. Every proof dependency
here is published. No source assertion of transitivity or comparison is used as
an assumption, and no Haar modulus is identified by this module.

## Implemented proof

`mirabolicCharacter T ψ k j` is the published character of
`partialUpper k (j+1)` pulled back along `fromMirabolic`. Thus it is exactly the
same adjacent-entry character on the final block, with no inverse or change of
additive character.

For one nonterminal step, `stepDatum T ψ k j` takes the ambient group
`mirabolic (k+j+1)`, its actual final-column radical as `U`, the actual successor
mirabolic range as `M`, and `partialLeviSubgroup k (j+1)` as `W`. The published
matrix identity `partialUpper_eq_radical_sup` identifies `U ⊔ W` with the larger
mirabolic partial group. The final acting subgroup in this intermediate tower is
bottom: only the underlying linear equivalence is extracted. Final general-linear
equivariance is proved separately, in `PartialDerivativeJacquetComparisonProof`,
and is not inferred from this choice.

The first character is the actual supplied `T.mirabolicTheta ψ (k+j)`.
`character_recursiveRadical_succ` proves that the combined character restricts to
this exact positive Phi-minus character on `U`. The second character is the
restriction of the combined character to `W`.
`stepInnerEquiv` composes `mirabolicEquiv` with `successorPartialEquiv` and
identifies the actual smaller partial group with the tower's inner subgroup.
Its underlying successor-range element is `successorEquiv u.val`.
`character_recursiveLevi` proves that its character is precisely the smaller
`mirabolicCharacter`, as stated by `stepInnerEquiv_character`.

`stepTwist` is the actual published `phiMinusCharacter T (k+j)` transported back
along `successorEquiv.symm`. The elementary determinant calculation
`determinant_partialUpper` uses upper triangularity and the diagonal entries one.
It follows that the normalized determinant norm and its real inverse half are
one on this subgroup. `stepTwist_inner` discharges the generic tower's required
triviality of the supplied twist on the second localizing subgroup. It does not
assert triviality on the final `GL_k` action.

`stepIteratedEquiv` is `Localization.transportEquiv` applied to the actual
normalized Phi-minus object and this specific subgroup equivalence, with the
identity coefficient equivalence. Its action-compatibility calculation retains
the exact Phi-minus determinant scalar and simplifies only the inverse successor
equivalence. `stepDirectEquiv` transports the join quotient by the proved subgroup
equality. `stepLinearEquiv` composes these transports with
`TowerDatum.twistedEquiv`. The class formula is `[[v]] ↦ [v]`, exposed by
`stepLinearEquiv_mk_mk`. The generic tower and transports supply genuine inverse
maps and both inverse laws on the full quotient carriers.

For the terminal Psi-minus step, `mirabolicPartialUpper_zero` proves that
`mirabolicPartialUpper k 0` is exactly the final-column radical. The forward
inclusion is its fixed-first-columns condition; the converse is the published
radical inclusion. The final block now has rank one, so its character is one by
`entrywiseCharacter_rankOne`. `terminalLinearEquiv` transports the actual
normalized Psi-minus carrier to this quotient. Normalization changes the action,
while the carrier remains the actual radical quotient.

`mirabolicLinearEquiv` iterates the preceding step equivalence, starting at
`terminalLinearEquiv`. This recursion uses the actual functor order: first the
Phi-minus quotient at rank `k+j`, then the smaller derivative. Induction proves
`mirabolicLinearEquiv_mk` for the existing composite
`JacquetNormalization.mirabolicDerivativeMk`. At the successor step the induction
hypothesis changes the derivative class to its smaller direct class, and
`stepLinearEquiv_mk_mk` collapses the nested quotient.

Finally, `ambientLinearEquiv` forgets the redundant mirabolic certificate using
`mirabolicEquiv`, with the identity coefficient map and the actual restricted
ambient representation. Composing gives `generalLinearLinearEquiv`. The lemma
`generalLinearLinearEquiv_mk` says that the existing
`generalLinearDerivativePositiveMk(v)` maps to the ambient direct class of `v`.
`generalLinearLinearEquiv_symm_mk` applies injectivity and the forward class
formula to prove the inverse formula. No carrier replacement, finite-dimensional
argument or quotient-surjectivity assumption is introduced.

## Dependency and independence audit

The four direct imports are `PartialLocalizationCharacter`,
`PartialDerivativeJacquetNormalization`, `LocalizationTower` and
`LocalizationTransport`. A recursive project-import audit at Library
`c6045fe1328899de3416096b16eb72db93a6c7fc` found 68 dependency modules, listed
below. All their Lean/Markdown pairs agree with that published Library. The
actual helper proofs use elementary matrices and characters, determinant powers,
quotient universal properties, smooth pullback/twist definitions and category
packaging. Imported Whittaker interface predicates are definitions, not
finiteness, classification or derivative comparison inputs. The historical
RankinSelberg namespace in the real-power character infrastructure introduces no
consumer theorem dependency. There is no dependency on the older
`Whittaker.TopDerivativeCoinvariantComparison` or
`Classification.SupercuspidalDerivatives` route. The supplied topology is installed
throughout; the canonical-field imports provide definitions rather than a choice
of canonical field or topology for the theorem.

The full exclusion set of the comparison proof applies to this construction and all its
helpers. No plus, adjunction, duality, pairing, derivative filtration, segment,
classification, socle, product-structure, or Whittaker-finiteness conclusion is
used. The explicit exclusion obligations are retained here:

Preserve direct and transitive independence from `SegmentHeadProductIrreducibility` itself; `GenericSegmentProductUniqueness`; multisegment exhaustion; ordered strong-head existence; quotient coverage; ordered conversion; tempered uniqueness; `SquareIntegrableLanglandsClassification`; square-integrable exhaustion; regular exhaustion; socle exhaustion; analytic segment classification; and forward special-segment essential square-integrability. Exclude their conclusions and transitive prerequisite/proof-successor routes. Audit shared lower helpers and the actual transitive project import closure before reuse.

As shared infrastructure for the socle route, also exclude `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; `SegmentSocleProductIrreducibility`; juxtaposed structure and quotient-Hom; adjacent socle commutation; two-segment socle commutation; linked socle gluing; and ordered multisegment socle existence. Audit actual direct and transitive project imports and shared helper provenance. No plus, adjunction, duality, derivative filtration, pairing, segment or classification theorem is required by this comparison statement. The actual partial and ordinary derivative constructions are required; their definitions are not comparison proofs.

The complete dependency modules are:

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization
Langlands.Representation.Derivative.PartialLocalizationCharacter
Langlands.Representation.Derivative.PartialLocalizationData
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationTower
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Shahidi.TwoBlocks
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
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
