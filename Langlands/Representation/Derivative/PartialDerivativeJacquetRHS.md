# Actual right-hand quotient in the positive Jacquet comparison

Author: Worker 593.

This module constructs the composite quotient map into the actual functor

```
positiveTwoBlockNormalizedJacquet T k m hk hm ⋙ partialDerivative T ψ k m
```

and proves its surjectivity, naturality, first-factor action, parabolic-radical
relations and final-block upper-unipotent character relation. All declarations
are in `Langlands.Derivative.JacquetRHS`. The main construction is `rhsMk`.
The underlying functors, quotients, actions and mapped intertwiners are the
published constructions, used unchanged.

## Parameters and actual quotient maps

Except for the first determinant lemma, the parameters are
`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}`,
`T : F.TopologicalData`, and, where needed,
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`.
The two positive block sizes are `k m : ℕ` with `hk : 0 < k` and `hm : 0 < m`.
Each topological declaration installs exactly `T.topology`.

Write `B = Shahidi.twoBlocks k m hk hm` and
`J = positiveTwoBlockNormalizedJacquet T k m hk hm`. For every
`A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k+m) F.Carrier)`,

```
jacquetMk T k m hk hm A : A →ₗ[ℂ] J.obj A
```

is exactly `B.jacquetMk A.representation`. The codomain is the actual
normalized Jacquet object transported to `GL_k × GL_m` through the inverse
of `Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier`. Pullback leaves its
carrier and quotient map unchanged. `jacquetMk_surjective` reuses the
published surjectivity theorem for this quotient.

The main map has type

```
rhsMk T ψ k m hk hm A :
  A →ₗ[ℂ] (J ⋙ partialDerivative T ψ k m).obj A
```

and is defined as the linear composite

```
(partialDerivativeMk T ψ k m (J.obj A)).comp
  (jacquetMk T k m hk hm A).
```

Thus it sends `v` to the iterated class `[[v]]` in the actual two quotients.
`rhsMk_surjective` composes the two published surjectivity results. The field
universe `uF` and carrier universe `uV` stay independent, and the final
quotient remains in `Type uV`. All representations and all intertwiners are
allowed; there are no finite-length, admissibility, irreducibility,
genericity or dimension assumptions.

## Action and naturality

For `a : GL_k × GL_m`, put

```
λ(a) =
  Jacquet.inverseHalfCharacter (T.leviModulus B)
    ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm a).
```

This is a complex unit, with the canonical inverse positive square root.
The inverse continuous Levi map is part of the formula, rather than an
informal identification of distinct groups.

`jacquet_action_mk` proves

```
(J.obj A).representation a (jacquetMk T k m hk hm A v) =
  (λ(a) : ℂ) •
    jacquetMk T k m hk hm A
      (A.representation (GeneralLinear.blockSum a) v).
```

The proof unfolds only the transported action, applies
`T.normalizedJacquet_mk`, and uses
`Shahidi.twoBlocks_leviEmbedding` to identify the ambient action with the
actual block-sum matrix. `jacquet_map_mk` is the representative formula for
the actual image of every intertwiner under `J`; it is definitional.

`rhs_action_mk` proves, for every `g : GL_k`,

```
((J ⋙ partialDerivative T ψ k m).obj A).representation g
    (rhsMk T ψ k m hk hm A v) =
  (λ(g, 1) : ℂ) •
    rhsMk T ψ k m hk hm A
      (A.representation (GeneralLinear.blockSum (g, 1)) v).
```

It first applies the published `partialDerivative_action_mk`, then the
Jacquet action formula, and moves the scalar through the linear quotient
map. The partial derivative contributes no extra twist. The exact
first-factor inverse-half Jacquet scalar is retained.

For any `f : A ⟶ A'`, `rhsMk_natural` proves

```
SmoothRep.hom ((J ⋙ partialDerivative T ψ k m).map f)
    (rhsMk T ψ k m hk hm A v) =
  rhsMk T ψ k m hk hm A' (SmoothRep.hom f v).
```

The proof successively applies `partialDerivative_map_mk` and
`jacquet_map_mk`. This concerns the published composite functor's actual
mapped intertwiner, not a newly chosen map between quotient carriers.

## Radical and character relations

For `u : B.unipotentRadical F.Carrier`, `rhsMk_radical` proves

```
rhsMk T ψ k m hk hm A (A.representation u.val.val v) =
  rhsMk T ψ k m hk hm A v.
```

It applies the second quotient map to `Jacquet.mk_apply_subgroup` for the
actual first coinvariant quotient. The nested value belongs first to the
parabolic subgroup and then to the ambient general linear group.
`rhsMk_unipotentSubgroup` gives the same equality for
`u : B.unipotentSubgroup F.Carrier`, the radical's actual image in ambient
`GL_(k+m)`. Its proof takes a witness in the subgroup image and applies
`rhsMk_radical`; the two subgroup types are not identified silently.

For every `u : GeneralLinear.upperUnipotent m F.Carrier`,
`rhsMk_upperUnipotent` proves

```
rhsMk T ψ k m hk hm A
    (A.representation (GeneralLinear.blockSum (1, u.val)) v) =
  (Whittaker.entrywiseCharacter ψ.complex m u : ℂ) •
    rhsMk T ψ k m hk hm A v.
```

The character is the existing entrywise character for the original `ψ`,
namely `ψ` of the sum of adjacent upper entries in the final block.
The proof first removes the Jacquet scalar at `(1,u)`, using the lemmas
below, and then applies the existing `partialDerivativeMk_unipotent`.

The scalar calculation is proved for the actual matrix:

- `determinant_upperUnipotent` proves `det u = 1` over every commutative
  ring and in every rank, including zero. It uses the determinant formula
  for an upper triangular matrix and its unit diagonal.
- The published `Langlands.Derivative.TopLocalization.determinantNorm_upper`
  applies the supplied normalized determinant character to the determinant-one
  equality. This module reuses that result directly.
- `leviModulus_upperUnipotent` applies `T.leviModulus_twoBlocks` at the
  inverse continuous Levi image of `(1,u)`. Both determinant norms are one,
  so the actual two-block modulus is one.
- `inverseHalf_leviModulus_upperUnipotent` uses the published equivalence
  `inverseHalfCharacter δ h = 1 ↔ δ h = 1`.

These are evaluations of the Library's explicit modulus character. The
module needs no additional Haar-modulus theorem or supplied scalar
compatibility assumption.

## Original sources and derived provenance

This is an internal derivation from the published quotient, action and
character APIs. The sources motivate the right-hand functor and fix its
normalization; they do not state this Lean adapter separately.

Zelevinsky, *Induced representations of reductive p-adic groups II.
Irreducible representations of GL(n)* (1980),
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
§3.7 and Proposition 3.7(b), printed p.182 / one-based PDF19. The partial
derivative localizes by the final-block upper-unipotent subgroup with the
same adjacent-entry additive character. The proposition compares its
composition with the normalized Jacquet functor to the ordinary derivative.
This module constructs and studies the actual right-hand composite only.
The source's neighboring segment derivative formula is not used.

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
§1.8(b), printed pp.444–445 / PDF5–6, defines localization by the relations
`π(u)v − θ(u)v` and normalizes the descended action by inverse half modulus.
Proposition 1.9(c),(g), printed p.445 / PDF6, gives the transitivity and
functorial compatibilities motivating the full comparison. Sections 3.5
and 4.3, printed pp.452,454 / PDF13,15, fix the order of the ordinary
derivative. Those transitivity and derivative comparisons are not used as
unproved inputs to this helper.

The retained originals are
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`
and
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
All the cited pages were read and visually inspected during this task, and
both original-file fingerprints were verified again for this unit.
No applicable source-specific errata file was found in the checked
literature/public-note locations; this is a bounded check.

## Imports, independence and scope

At the reviewed submission, the sole direct project import was
`Derivative.PartialDerivativeJacquetComparisonStatement`. Its transitive
project closure had 65 modules including that statement and 130 paired
Lean/Markdown files, all matching Library commit
`7b0be54f6fdff0448d87d389ed9dc8b01c6f048f` byte for byte. The candidate added
only this pair. The directly reused `Partial`, `Parabolic`, `TwoBlocks`,
`Coinvariants`, `PositiveCharacter`, `BlockModulus` and upper-unipotent pairs
were read in full.

Integration additionally imports the published `Derivative.TopLocalizationData`
and reuses its `determinantNorm_upper`, removing the repeated norm lemma.
The target pair and all imported pairs remain unchanged. Relative to Library
`3a4a075669d8c6e332c349566f8c1a7f96d2f5e6`, the final transitive project
closure contains 88 imported modules. The additional imports provide quotient
measure and top-localization infrastructure; the reused theorem's proof uses
only the determinant-one identity and `map_one`. The commutative-ring
`determinant_upperUnipotent` remains distinct from the existing field-only
lemma and the Rankin–Selberg lemma with a separate membership hypothesis.

The actual proof dependencies are the published quotient maps and their
evaluation/surjectivity laws, the normalized Jacquet action,
the partial derivative's action, map and unipotent laws, the explicit
two-block modulus, and elementary determinant and scalar identities.
The closure otherwise consists of lower group, field, topology,
representation, twist, quotient and character constructions. Its
`Dual.Definitions` is elementary algebraic dual infrastructure;
`Whittaker.PrerequisitesStatement` is a proposition definition, whose
unproved truth is not used. No duality, multiplicity-one or finiteness
theorem enters the implemented arguments.

The full positive/socle exclusions of the parent task and the stronger
BZ77/Whittaker-finiteness restrictions of the shared localization-tower
task were checked against the actual closure and these proof inputs.
There is no classification, segment, multisegment, special-head, socle,
tempered, square-integrable, exhaustion, coverage, ordered-conversion,
two-supercuspidal product, segment-Jacquet-formula or consumer finiteness
input. In particular the closure avoids `SegmentHeadProductIrreducibility`,
`GenericSegmentProductUniqueness`,
`SquareIntegrableLanglandsClassification`,
`UnlinkedSegmentSocleProductIrreducible`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, `SupercuspidalDerivatives`,
`SupercuspidalCoinvariantFinitenessStatement`,
`IrreducibleCoinvariantFinitenessStatement` and
`LeviCuspidalCoinvariantFinitenessStatement`, their excluded proof successors
and their downstream theorem routes. No plus, adjunction, pairing,
derivative filtration or exterior-tensor comparison is used.

This unit does not import a pending localization tower, identify the
combined subgroup or its character, compare the left-hand derivative
kernel, or construct the final natural isomorphism. Those remain separate
obligations of the comparison proof. The functorial constructions here
cover positive `k,m`; the arbitrary-rank determinant lemma does not extend
the two-block comparison to either boundary.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
