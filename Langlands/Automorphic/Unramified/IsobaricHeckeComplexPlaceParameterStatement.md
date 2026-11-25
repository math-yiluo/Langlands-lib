# Complex-place parameters at a Hecke-family Euler endpoint, conditional on C2

This module contains one proposition definition,
`Langlands.Automorphic.Unramified.IsobaricHeckeComplexPlaceParameterStatement`,
with universe parameters `uF, uV` in that order. It is an internal comparison
theorem target. The B6 endpoint uses it in the exact-stabilizer branches of
Harris's Proposition 4.8. The target is conditional on C2, the published
Euler-polynomial constituent-recovery target. Nothing is proved here.

## The proposition

The definition is the implication

```text
CuspidalEulerConstituentRecoveryStatement.{uF, uV} →
  ∀ (F : Type uF) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)]
    (n : ℕ) (D : IsobaricData F) (μ : Fin n → HeckeCharacter F),
    IsobaricData.HasHeckeFamily.{uF, uV} D μ →
      ∀ (v : {v : NumberField.InfinitePlace F //
                NumberField.InfinitePlace.IsComplex v})
        (ds : List Langlands.LocalFactor.Archimedean.ComplexCharacterData),
        D.HasComplexPlaceParameter v ds ↔
          Langlands.Global.HeckeCharacter.FamilyHasComplexPlaceParameter μ v ds
```

All objects are the Library's actual objects.

- `Langlands.Automorphic.Unramified.CuspidalEulerConstituentRecoveryStatement`
  is used unchanged from `CuspidalSpectralRigidityStatement`. It is the
  premise of the whole implication. It is neither restated nor proved here.
- `F` is an arbitrary number field. The explicit
  `CompactSpace (AdeleQuotient F)` assumption is the one required by the
  Library's actual cuspidal-class vocabulary, as in the C2 target.
- `D : IsobaricData F` is an actual finite multiset of positive-rank cuspidal
  classes `PositiveRankCuspidalClass F`, repetitions allowed.
  `μ : Fin n → HeckeCharacter F` is a finite family of actual continuous
  idele-class quasi-characters, repetitions allowed.
- `IsobaricData.HasHeckeFamily.{uF, uV} D μ` is the existing finite
  Euler-product endpoint relation of `HeckeFamilyEndpoint`, used unchanged.
  It retains the actual attached spectral-system witness
  (`IsobaricData.HasSpectralSystem`), the equality `D.rank = n`, one finite
  exceptional set containing the system's exceptional places, unramifiedness
  of every actual character `μ i` outside that set, and equality of the
  attached Euler denominator polynomial with
  `∏ i, (1 - C ((μ i).finiteComponent v π) * X)` at every uniformizer `π`
  of every finite place `v` outside the set. It asserts nothing at
  infinite places.
- `v` is an actual complex infinite place of `F`, and `ds` is one list of
  `ComplexCharacterData`, the Library's presented continuous characters of
  `ℂˣ`.

The spectral presentation universe `uV` occurs in two places: the C2
premise and `HasHeckeFamily`. The two complex-place parameter predicates have
only the field universe `uF`.

## The two parameter predicates

Both predicates are those of `Langlands.Automorphic.IsobaricComplexPlaceParameter`,
used without change.

- `IsobaricData.HasComplexPlaceParameter D v ds` is the isobaric side. It is a
  complete enumeration `σ : Fin b → PositiveRankCuspidalClass F` of the
  constituents with `Finset.univ.val.map σ = D`, so that every constituent
  occurs with its multiplicity. Each `σ j` has a list `d j` satisfying the
  existing literal cuspidal standard-module embedding predicate
  `PositiveRankCuspidalClass.HasComplexPlaceParameter`. The list `ds` is a
  permutation of the concatenation of all blocks `d j`. The literal
  embedding predicate itself is not replaced by a permutation-invariant
  predicate; permutation closure is taken only after aggregation, as
  specified by that definition.
- `HeckeCharacter.FamilyHasComplexPlaceParameter μ v ds` is the Hecke side.
  It asks for data `d i` with `(μ i).HasComplexPlaceParameter v (d i)` for
  every `i`, and `ds` a permutation of `List.ofFn d`. Here
  `(μ i).HasComplexPlaceParameter v (d i)` is equality of actual
  characters on every unit `x` of the actual completion
  `InfiniteCompletion F v.1`:
  `(μ i).infiniteComponent v.1 x` equals `(d i).character` applied to the
  image of `x` under the selected completion coordinate
  `NumberField.InfinitePlace.Completion.extensionEmbedding v.1`. This is
  the coordinate of the Library's place actions and of
  `InfinityType.coordinate`. No infinity-type label replaces the character.

The iff concerns the same list `ds` on both sides.

- **Forward direction.** If the constituent data `D` have the parameter `ds`
  at `v`, then the actual Hecke characters `μ` have the same list `ds` at `v`.
- **Reverse direction.** If the actual Hecke characters `μ` have the
  parameter list `ds` at `v`, then `D` has the same list `ds` at `v`.

## Scope of the premises

No unitarity premise is made on `D` or on `μ`, and the characters are
arbitrary quasi-characters. Neither `IsobaricData.IsUnitary` nor
`HeckeCharacter.IsUnitary` occurs. There is no total-complexness premise on
`F`: other infinite places, real or complex, may exist. There are no
base-change, Galois, place-uniqueness or positive-rank premises. The empty
family `n = 0` and the rank-zero datum `D = 0` are included. There
`HasHeckeFamily` gives `D.rank = 0`, hence `D = 0`, and both parameter
predicates hold exactly for `ds = []`.

These premises are absent for two reasons. The C2 input is stated for
arbitrary mixed-rank actual cuspidal classes with genuinely attached
spectral systems, without unitarity. The Library's twist constructions accept
any actual Hecke quasi-character. No unitary-character decomposition is used,
and nothing asserts that central unitarity implies unitarizability.

## Proof obligations of the later proof

The later proof must establish both directions from the C2 premise and
`HasHeckeFamily`. The following are proof obligations. They are not
additional hypotheses of this target, and they are not fields of a new
definition.

1. **Recover the actual rank-one cuspidal constituents.** For each `μ i`,
   build an actual rank-one cuspidal class with a genuinely attached
   spectral system. The Library has the inputs for this.
   `ConstantFunctions.rankOneCuspidal` has the presentation
   `ConstantFunctions.rankOneSpectralPresentation`
   (`ConstantSpectralPresentation`).
   `CuspidalOperatorRealization.heckeDeterminantTwist`
   (`HeckeTwist.OperatorTwist`) twists it by any actual Hecke
   quasi-character. `HeckeTwist.CuspidalSpectralTwist` gives the genuinely
   attached twisted presentation and its scaled Euler-polynomial formula
   `heckeDeterminantTwist_eulerPolynomial`. Applied to the trivial rank-one
   spectrum, whose Euler polynomial is `1 - X`, that formula gives
   `1 - (μ i).finiteUniformizerValue v · X` at almost all `v`. The proof
   must show that these agree with the factors
   `1 - (μ i).finiteComponent v π · X` of `HasHeckeFamily` at
   unramified places. It must unpack the
   `IsobaricData.HasSpectralSystem` witness into an enumeration of `D` with
   attached constituent systems. Finally it must apply C2 to the two finite
   sums. C2 gives a bijection between the constituents of `D`, with
   multiplicity, and the rank-one twists of the `μ i`. In particular every
   constituent of `D` has rank one.
2. **Identify the complex-place parameters.** For an arbitrary actual
   quasi-character `χ`, the proof must show that the rank-one twisted class
   has the literal parameter `[d]` at `v` if and only if
   `χ.HasComplexPlaceParameter v d`. This means identifying the compact and
   Lie actions at `v` of the twisted line with the actual completion
   character `χ.infiniteComponent v.1`, read through `extensionEmbedding`,
   in both directions. The existing
   `OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist` in
   `AssociatedGammaAutomorphicTwist` does not give this. It assumes
   `χ.HasPrescribedInfinityComponent 1` and preserves a given parameter
   only in one direction. This remains genuine proof work.
3. **Combine.** The bijection of step 1 and the rank-one identification of
   step 2 must be combined with the permutation closures of the two
   predicates. Then the same list `ds` works on both sides, in both
   directions.

A proof may derive stronger information about the constituents internally,
such as the fact that they all have rank one. Such information is not
assumed in order to obtain the archimedean conclusion.

## Relation to other targets

- This target is not Arthur–Clozel III.5.1 and is not a base-change
  statement: no extension of `F` occurs. It is a separate branch premise.
  It does not enlarge the B7 target
  `Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceStatement`,
  which concerns parameter transport along actual
  weak base changes and weak induction.
- It has no regular-algebraicity conclusion. It leaves the separate
  totally-complex infinitesimal-character and regular-algebraicity bridge
  statement `Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement`
  unchanged.
- The supporting vocabulary (`HeckeFamilyEndpoint`,
  `IsobaricComplexPlaceParameter`) only defines the relations used here.
  It does not prove this comparison. Neither trace-formula work nor base
  change is used by the intended proof.
- The original Proposition 4.8 statements and the cohomological A2 fallback
  are unchanged.

## Provenance

Provenance is internal. The target composes two things to formulate the
finite-to-infinite comparison needed by the B6 endpoint. One is the
Library's C2 constituent-recovery target. The other is the Library's actual
rank-one Hecke twists, through the endpoint and parameter vocabulary above.

- Motivating source: registered `operator-external-inputs-plan-2026-11-16`,
  file
  `/home/taskhub/pilot/literature/Operator note - Formalizing the large external inputs of the local Langlands correspondence for GL_n (16 November 2026)/external-inputs-plan.tex`.
  Section 2.2, items B6 and B7 (source lines 197–199), states B6 with
  weak base changes ending in representations induced from Hecke characters
  `μ_1, …, μ_m`, and B7 for complex places. Section 4.8, “The remark and the
  Library's statements” (source lines 907–911), covers this target's use.
  The prime-branch paragraph replaces A2 by B6 in the prime branch with C2
  among its premises. The infinity-type paragraph observes that no premise of
  the branches relates archimedean components. The plan does not state the
  present comparison as a separate theorem. It is the step that connects the
  finite Euler endpoint of B6 to complex-place parameters.
- C2's source: registered `jacquet-shalika-1981-euler-ii`, H. Jacquet and
  J. A. Shalika, *On Euler Products and the Classification of Automorphic
  Forms II*, Amer. J. Math. **103** (1981), 777–815, file
  `/home/taskhub/central-library/Jacquet-Shalika--On Euler products and the classification of automorphic forms II--1981.pdf`.
  Theorem 4.4 and its multiplicity-recovery proof are on printed p.809
  (one-based PDF p.34), as already isolated in
  `CuspidalSpectralRigidityStatement`. That source supplies only the C2
  premise. The present vocabulary-level endpoint comparison is not
  attributed to Jacquet–Shalika verbatim, nor to Arthur–Clozel.

No errata note for either source was found in the audited Library.
