# Actual RHS-to-direct partial-localization comparison

Author: Worker 593.

This module constructs the linear equivalence between the actual normalized
Jacquet-then-partial-derivative quotient and the direct character quotient
at the published partial-upper subgroup. It proves both representative
formulas, both inverse laws, naturality in both directions for every ambient
intertwiner, and the exact first-factor inverse-half action formula.
All new names are in `Langlands.Derivative.JacquetRHSComparison`.

## Parameters and the two actual carriers

The parameters are `{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}`,
supplied `T : F.TopologicalData`, and
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`.
Every topological declaration installs exactly `T.topology`. The comparison
takes `k m : ℕ`, `hk : 0 < k` and `hm : 0 < m`, and every

```lean
A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier).
```

The universes `uF` and `uV` remain independent. No finite-length,
admissibility, irreducibility, genericity or dimension hypothesis occurs.

Write `B = Shahidi.twoBlocks k m hk hm`,
`J = positiveTwoBlockNormalizedJacquet T k m hk hm`, and
`R = J ⋙ partialDerivative T ψ k m`. The source carrier of the main
equivalence is literally `R.obj A`. In particular, `J` uses the actual
normalized Jacquet quotient and pullback along
`(Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm`.
The second quotient is the existing partial derivative of this object.
The published `JacquetRHS.rhsMk T ψ k m hk hm A` sends an original
vector `v` to its iterated class `[[v]]` in this carrier.

The abbreviation `Direct T ψ k m A` is exactly

```lean
Jacquet.Localization.Coinvariants A.representation
  (PartialLocalization.partialUpper k m F.Carrier)
  (PartialLocalization.character ψ.complex k m).
```

It remains in `Type uV`, with its existing complex module structure.
Write `q_A` for the published `Jacquet.Localization.mk` into this quotient.
`Direct` itself needs no positivity premises; every comparison map and law
in this unit retains both positive-block premises.

## Concrete subgroup and character inputs

Let `N = PartialLocalization.partialUpper k m F.Carrier`,
`U = B.unipotentSubgroup F.Carrier`, and
`W = PartialLocalization.finalLeviRange k m F.Carrier`.
These are actual subgroups of `GL_(k+m)`. The unchanged published
`PartialLocalizationData` proves

```text
N = U ⊔ W,
W = image of u ↦ blockSum (1,u) for u in upperUnipotent m F.Carrier.
```

Here `N` consists of matrices with identity upper-left `k` block, zero
lower-left block, and upper-unipotent final `m` block. The subgroup `U` is
the actual ambient image of the two-block parabolic radical.
The character `Θ = PartialLocalization.character ψ.complex k m` reads
the final block and applies the original `ψ` to its sum of adjacent entries.
The published `character_radical` proves that `Θ` is one on `U`;
`character_finalLevi` proves that its restriction along the actual
`finalLevi` map is `Whittaker.entrywiseCharacter ψ.complex m`.
These facts are proved matrix and character identities in the imported pair,
not additional compatibility assumptions on the comparison.

`rhsMk_covariant` proves, for every `u : N` and `v : A`,

```text
rhsMk A (A.representation u.val v) = (Θ u : ℂ) • rhsMk A v.
```

The proof transports `Θ` to the actual join using the inclusion supplied
by `N = U ⊔ W`, and invokes the published
`Jacquet.Localization.covariant_sup`. On `U`, it uses
`JacquetRHS.rhsMk_unipotentSubgroup` and `character_radical`. On `W`,
it unpacks the actual image witness, identifies the whole subgroup element
by subtype extensionality, and uses `rhsMk_upperUnipotent` together with
`character_finalLevi`. The join lemma proves that covariance along the two
inclusions implies covariance along the join: the covariant elements form a
subgroup containing both images. It requires no product decomposition or
trivial-intersection assumption.

## Quotient lifts in both directions

The map

```text
backward T ψ k m hk hm A : Direct T ψ k m A →ₗ[ℂ] R.obj A
```

is `Jacquet.Localization.lift` of `rhsMk`, using `rhsMk_covariant`.
`backward_mk` is the literal representative formula

```text
backward A (q_A v) = rhsMk A v.
```

The forward construction uses the two actual successive quotients.
`directMk_radical` proves that `q_A` kills the actual ambient
parabolic-radical relations: insert the radical element into `N`, apply
`Localization.mk_apply_subgroup`, and use `character_radical`.
`firstToDirect` is therefore the published `Jacquet.lift` through the
first quotient. It is typed as

```text
firstToDirect T ψ k m hk hm A : J.obj A →ₗ[ℂ] Direct T ψ k m A.
```

The representation supplied to this lift is the restriction of
`A.representation` to the actual parabolic. An actual radical element
inside that parabolic is explicitly mapped into its ambient subgroup;
distinct subgroup carriers are not identified implicitly.
`firstToDirect_mk` proves

```text
firstToDirect A (JacquetRHS.jacquetMk T k m hk hm A v) = q_A v.
```

`firstToDirect_covariant` proves covariance under the second quotient's
actual subgroup `Partial.unipotent F.Carrier k m`, with the exact
`Partial.character ψ.complex k m`. Surjectivity of `jacquetMk` reduces
an arbitrary first-quotient vector to an original `v`. An element of this
subgroup is explicitly `(1, Partial.second ... u)`. The proof applies
`jacquet_action_mk`, removes its scalar by the published
`inverseHalf_leviModulus_upperUnipotent`, and then applies the direct
quotient relation at `PartialLocalization.finalLevi`. The equality
`character_finalLevi` identifies precisely the second-quotient character.
The original additive character is preserved throughout.

Consequently `forward` is a second `Jacquet.Localization.lift`, now for
the actual representation `J.obj A` and the actual partial-derivative
subgroup and character. Its type and evaluation law are

```text
forward T ψ k m hk hm A : R.obj A →ₗ[ℂ] Direct T ψ k m A,
forward_rhsMk : forward A (rhsMk A v) = q_A v.
```

All three lift evaluation formulas above are definitional equalities.

## Inverses and the main equivalence

`backward_forward` proves `backward A (forward A x) = x` for every
`x : R.obj A`. It writes `x = rhsMk A v` using the published
`rhsMk_surjective` and then closes by the representative formulas.
`forward_backward` proves `forward A (backward A x) = x` for every
`x : Direct T ψ k m A`, using the actual direct quotient's
`Localization.mk_surjective`. Thus the inverse laws hold on all vectors.

The definition

```text
linearEquiv T ψ k m hk hm A :
  R.obj A ≃ₗ[ℂ] Direct T ψ k m A
```

bundles these maps and inverse laws with `LinearEquiv.ofLinearMap`.
Its public representative formulas, both definitional, are

```text
linearEquiv_rhsMk :
  linearEquiv A (rhsMk A v) = q_A v,
linearEquiv_symm_mk :
  (linearEquiv A).symm (q_A v) = rhsMk A v.
```

## Naturality and the retained normalized action

For every actual ambient intertwiner `f : A ⟶ A'`, let `D(f)` be
`Jacquet.Localization.mapLinear N Θ (SmoothRep.hom f)` and let `R(f)`
be `SmoothRep.hom (R.map f)`. With `e_A = linearEquiv ... A`,
the two naturality theorems state

```text
linearEquiv_natural       : D(f) (e_A x) = e_A' (R(f) x),
linearEquiv_symm_natural  : R(f) (e_A.symm x) = e_A'.symm (D(f) x).
```

Their quantifiers cover every `x` of the appropriate quotient carrier.
The forward law reduces by `rhsMk_surjective` and uses the actual
composite functor's `rhsMk_natural`. The inverse law reduces by direct
quotient surjectivity and uses the same map evaluation formula. The direct
map's evaluation on `q_A v` is definitional.

For `g : GL_k`, write

```text
λ(g) =
  Jacquet.inverseHalfCharacter (T.leviModulus B)
    ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm (g,1)).
```

The theorem `linearEquiv_action_rhsMk` proves the exact representative
action formula

```text
e_A ((R.obj A).representation g (rhsMk A v)) =
  (λ(g) : ℂ) • q_A (A.representation (blockSum (g,1)) v).
```

It applies the published `rhs_action_mk`, linearity, and
`linearEquiv_rhsMk`. The inverse-half scalar at the actual inverse Levi
image remains explicit. For the final-block upper-unipotents used in the
forward lift, its value is one by the actual two-block modulus formula and
the determinant-norm-one theorem. For the first factor, the explicit
two-block modulus specializes to `|det g|^m`; the displayed theorem retains
its inverse half without erasing it. This module does not prove a new
determinant-power simplification or identify another Haar modulus.

No descended `GL_k` action or smooth functor is bundled on `Direct` in this
unit. The formula above is an identity in its complex module. The LHS
ordinary-derivative adapter, the direct action, the accumulated derivative
normalization and the final natural isomorphism remain in the separate
assembly of the positive comparison.

## Original sources and derived provenance

This is an internal derived quotient construction. The implemented route
specializes the quotient universal properties directly to the actual RHS
carrier, and uses only the join-covariance part of the published localization
tower. It does not assume a transitivity or derivative comparison theorem.

Zelevinsky, *Induced representations of reductive p-adic groups II.
Irreducible representations of GL(n)* (1980), registered as
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
§3.7 and Proposition 3.7(b), printed p.182 / one-based PDF19, supplies the
positive two-block comparison motivating this RHS construction. Its partial
derivative uses the same final-block upper-unipotent subgroup and positive
adjacent-entry character. The neighboring segment derivative formulas are
not proof inputs.

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), registered as `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
§1.8(b), printed pp.444–445 / PDF5–6, fixes localization by the relations
`ρ(u)v − θ(u)v` and the inverse-half-modulus normalization. Proposition
1.9(c),(g), printed p.445 / PDF6, motivates the transitivity and functorial
route; §§3.5 and 4.3, printed pp.452,454 / PDF13,15, fix the ordinary
derivative conventions used by the parent comparison. This module proves
its displayed maps and laws from the Library, rather than importing the
truth of those source propositions as assumptions.

The retained originals are
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`
and
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
The cited pages were read and visually inspected during this task, with
the original fingerprints verified. No applicable source-specific errata
file was found in the checked literature and public-note locations; that
is a bounded check.

## Import and proof-dependency audit

The three direct imports are
`Derivative.PartialDerivativeJacquetRHS`,
`Derivative.PartialLocalizationData` and `Jacquet.LocalizationTower`,
with the common `Langlands.Representation` prefix. Recursively following
their actual project imports gives 91 imported modules and 182 paired
Lean/Markdown files. Every imported file agrees byte for byte with Library
`c6045fe1328899de3416096b16eb72db93a6c7fc`. The entry pair is the only new
public source in this contribution; no imported pair is edited.

The actual mathematical inputs are the quotient lifts, evaluation and
surjectivity laws from `Jacquet.Coinvariants` and `Jacquet.Localization`;
the literal RHS composite, actual mapped intertwiners and action/character
laws from `PartialDerivativeJacquetRHS`; the concrete subgroup/character
identities from `PartialLocalizationData`; and `covariant_sup` from
`LocalizationTower`. The proofs of those shared inputs use the published
group, matrix, character, twist and quotient constructions. This unit
assumes no quotient equivalence, theorem-truth field or supplied
normalization compatibility.

The integrated RHS helper additionally imports `TopLocalizationData`.
Its complete pair was checked: the reused `determinantNorm_upper` is
proved from `determinant_upper` and `map_one`; that determinant identity
uses the upper-triangular determinant formula and unit diagonal.
`TopLocalizationData` also imports `Whittaker.MirabolicQuotientMeasure`.
The latter's membership lemmas are direct entrywise matrix calculations;
its remaining construction transports a group quotient measure through the
actual mirabolic projection and Levi embedding. Its Rankin–Selberg
dependencies prove group unimodularity and construct compatible quotient
measures. The general-linear proof uses diagonal and transvection
generation and regular Haar uniqueness; the unipotent proof uses finite
denominator clearing, compact open subgroups and regular Haar uniqueness.
The averaging and induction infrastructure loaded below them defines
quotient integrals, translations, positive functionals, and spaces of
functions. None of those measure or induction results is invoked by this
comparison's quotient lifts or normalization calculation.

`Dual.Definitions` in the closure supplies elementary linear-functional
definitions. `Whittaker.PrerequisitesStatement` defines propositions and
does not supply their truth. `Category.Basic.HasFiniteLength` is only a
predicate. Field-degree and residue-field occurrences of `finrank` in
arithmetic normalization concern fields, not representation dimensions.
No finiteness, uniqueness, duality or classification result is used.

The following table checks all exclusion families of the positive task
and the stronger shared tower restrictions. Both the actual import
closure and the mathematical dependencies described above avoid the
listed conclusions, proof successors and downstream theorem routes.

| Excluded family | Audit result |
| --- | --- |
| Special-head product irreducibility, generic segment-product uniqueness, individual special-head/reverse-socle and segment-socle/reverse-head existence | No segment, head, socle or irreducibility module or proof input. |
| Multisegment exhaustion, ordered strong-head existence, quotient coverage and ordered conversion | No multisegment, ordering or representation coverage input. The only surjectivity used is that of the actual relation-quotient maps. |
| Tempered uniqueness, square-integrable classification or exhaustion, regular exhaustion, analytic segment classification and forward special essential square-integrability | No such module or mathematical conclusion. The actual determinant and modulus evaluations are group-character calculations. |
| Unlinked socle-product irreducibility, linked reverse-product structure, linked pair reducibility, general socle-product irreducibility, juxtaposed structure and quotient-Hom | No product-of-representations, socle or quotient-Hom theorem. |
| Adjacent and two-segment socle commutation, linked gluing, ordered multisegment socle existence and socle exhaustion | No commutation, gluing or socle existence/exhaustion input. |
| Full, head and socle segment Jacquet formulas, special Jacquet exponent-norm formulas, all segment derivative formulas, and parts (b),(d),(e),(f) of the shared upstream six-statement contribution | Only general quotient constructions and actual derivative definitions occur. None of the excluded formula conclusions is used. |
| Two-supercuspidal nonadjacent-product irreducibility or full product structure; Ze80 §§3.5,9.6 segment formulas and Theorems 4.2,9.7,9.3 | No two-supercuspidal, segment criterion, analytic or classification input. The §3.7 citation is only motivation for the construction. |
| Supercuspidal proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` | No `Classification` module or such theorem input. `TopDerivativeCoinvariantComparison` is also absent. |
| Irreducible, Levi-cuspidal and supercuspidal Whittaker coinvariant finiteness, including the dependent mirabolic finite-length route | No representation-finiteness premise or conclusion; the unused predicate and arithmetic degree facts described above do not provide one. |
| Plus, adjunction, duality, pairing, derivative filtration, exterior-tensor comparison or unproved general derivative results | No such proof input. The smooth derivative definitions and the already proved localization constructors do not assert any excluded consumer conclusion. |

The complete import list appears below. It contains only lower group, field,
topology, measure, category, smooth-representation, twist, localization,
Jacquet, derivative-definition and character infrastructure. A scan for the
named excluded declarations and all 38 excluded task identifiers found no
reference in its Lean sources. This scan supplements the proof-provenance
check above; a string scan alone does not establish independence.

This construction covers positive `k,m`. It proves neither boundary
comparison, the ordinary-derivative comparison, nor the final natural
isomorphism requested by the parent task.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Complete transitive project import list

The list excludes this entry module and includes all three direct imports.

```text
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
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
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.Partial
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement
Langlands.Representation.Derivative.PartialDerivativeJacquetRHS
Langlands.Representation.Derivative.PartialLocalizationData
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationTower
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.RankOneQuotient
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentQuotient
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.Definitions
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
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
