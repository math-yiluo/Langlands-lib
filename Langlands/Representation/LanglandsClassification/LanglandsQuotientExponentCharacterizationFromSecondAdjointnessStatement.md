# The exponent characterization of the Langlands quotient from second adjointness

Author: Worker 168, Task 5653 (`1df73c68-230c-4ced-8325-dc9c910df8d8`). Module
`Langlands.Representation.LanglandsClassification.LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement`,
namespace `Langlands.Aubert.General.RepresentedParabolic`, universe parameters `u, v`.

The module contains one **statement**, the `Prop`-valued definition
`LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement.{u, v}`.
The module does not assume or prove it.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:

- VII.4.2, the sentence after the proof of (i) (printed p.243 / PDF p.249). This is the
  conclusion, the published `LanglandsQuotientExponentCharacterizationStatement`; see
  `LanglandsQuotientExponentCharacterizationStatement.md`.
- VI.9.6, the first Theorem (VI.9.6.1) (printed p.201 / PDF p.207). This is the premise,
  the published `LeviSecondAdjointnessStatement`; see `LeviSecondAdjointnessStatement.md`.

## The statement

`LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement.{u, v}` is the
implication

```
LeviSecondAdjointnessStatement.{u, v} →
  LanglandsQuotientExponentCharacterizationStatement.{u, v}
```

The universe arguments are the same on both sides.

- **Premise.** `LeviSecondAdjointnessStatement.{u, v}` ranges over nonarchimedean local
  fields `k : Type u` (`Field`, `ValuativeRel`, topology, `IsNonarchimedeanLocalField`,
  `T2Space`) and connected reductive `G` over `k`. The rational points of `G` carry the
  canonical point topology and are assumed locally compact and a nonarchimedean group. It
  takes two actual rational parabolic triples, `P = MN` (`p`, `m`, `n`) and `P̄ = M N̄`
  (`pbar`, `mbar`, `nbar`), with the same Levi embedding `mbar ≫ pbar = m ≫ p` and with
  `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`, that is `P(F) ∩ P̄(F) = M(F)`.
  For each such pair it asserts `Nonempty` of a Mathlib adjunction
  `leviInductionFunctor.{u, max u v} p m n … ⊣ leviJacquetFunctor.{u, max u v} pbar mbar nbar …`
  between smooth representations of `M(F)` and of `G(F)` on carriers in `Type (max u v)`.
  In words, normalized induction `i_P^G` is left adjoint to normalized Jacquet restriction
  `r_{P̄}^G`.
- **Conclusion.** `LanglandsQuotientExponentCharacterizationStatement.{u, v}` ranges over
  the same fields and groups, and over the choices `(T, i, ν, D)` that define Langlands
  triplets. It takes a Langlands triplet `(P = MU, σ, ψ)` (`IsLanglandsTriplet`) with split
  component `a : A → M` and `σ` on a carrier in `Type v`, and a parabolic `P̄ = M Ū` with
  `lbar ≫ pbar = l ≫ p` and `P(F) ∩ P̄(F) = M(F)`. Let `I = i_P^G(σ ⊗ ψ)`. For every
  irreducible smooth representation `π` of `G(F)` on a carrier in `Type (max u v)` that is a
  subquotient of `I`, it asserts that `π` is an irreducible quotient of `I` if and only if
  some normalized exponent `χ` of `r_{P̄}^G(π)` along `A` has normalized real part equal to
  `leviUnramifiedRealPart l hl a ha ψ`, which is `ℜ(ψ)`.

The premise is used at the conclusion's universes. The conclusion's `I` and `π` live in
`Type (max u v)`, and the premise gives the adjunction on exactly that carrier universe.

## Provenance and why this premise

The statement is derived: it isolates the one input of Renard's argument that the
Library does not yet prove. Renard justifies the remark with "on voit d'après ce qui
précède", which points to the proof of (i), and that proof uses second adjointness in both
directions:

- (⇒) A surjection `I → π` gives, by Frobenius reciprocity on the opposite side
  (second adjointness), a nonzero map `σ ⊗ ψ → r_{P̄}^G(π)`. The split component acts on
  `σ ⊗ ψ` by a character of real part `ℜ(ψ)`, because `σ` is tempered.
- (⇐) The geometric lemma and the `PP̄`-regularity of VII.4.1 show that the exponent
  `ℜ(ψ)` can only come from the identity piece `σ ⊗ ψ` of `r_{P̄}^G(I)`. This yields a
  nonzero map `σ ⊗ ψ → r_{P̄}^G(π)`, and second adjointness turns it into a nonzero, hence
  surjective, map `I → π`.

The other inputs of this argument are already in the Library without premises: the
geometric lemma `representedGeometricLemma` and the piece filtration
`exists_pqRegularity_pieceFiltration`, the identity-piece identification
`oppositeIdentitySupport`, the real-part separation of the nonidentity pieces (the
argument of `langlandsTripletOppositePieceSeparation`, used by the proof of the VII.4.1
regularity Lemma), the exactness of the Jacquet functor, and the tempered split
character `normalizedTemperedTwistSplitCharacter`. So second adjointness is the only
premise. A theorem of this statement and the published proof of
`LeviSecondAdjointnessStatement` (Task 4834, `c0fa1878-6cee-4435-8484-2fc15ea04a17`) would
together prove the conclusion.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.LanglandsClassification.LanglandsQuotientExponentCharacterizationStatement` | the conclusion `LanglandsQuotientExponentCharacterizationStatement` |
| `Langlands.Representation.Exponents.LeviSecondAdjointnessStatement` | the premise `LeviSecondAdjointnessStatement` |
