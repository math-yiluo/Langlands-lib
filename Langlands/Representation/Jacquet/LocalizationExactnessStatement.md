# Exactness of character-localized coinvariants

Worker 8 authored this statement pair. The namespace is
`Langlands.Jacquet.Localization`; the aggregate is
`CharacterLocalizationExactnessStatement`. It is a proposition definition
combining compact detection of the actual character relations and exactness
of the actual induced quotient maps. Neither theorem is assumed or proved here.

## Objects, hypotheses and conclusions

The coefficient field is `ℂ`. The ambient group `G` has a topology, and
the three module carriers have independent universes `uV`, `uW`, and `uX`,
independent also of the group universe `uG`. The modules have no topology.
There are no finite-dimensionality, admissibility, irreducibility, or
finite-length assumptions.

For an actual subgroup `U : Subgroup G`,
`IsLimitOfCompactSubgroups U` means that every compact subset of `U`
is contained in a compact subgroup of `U`. Both occurrences of compactness
use the induced topology on `U`. This is the literal condition introduced
before BZ77 Proposition 1.9, not an assumption that `U` itself is compact.
No countable exhaustion or choice of an exhaustion is made.

`CompactCharacterRelationDetectionClause` says that a vector belongs to
the relation span for `U, θ` if and only if it belongs to the corresponding
span for one compact subgroup `K : Subgroup U`. The smaller span is exactly

`relations (ρ.comp U.subtype) K (θ.comp K.subtype)`.

Thus both spans are submodules of the same original carrier. The smaller
character is the actual restriction of `θ`, and the action is the actual
restricted action. This clause assumes the compact-subgroup containment
condition but neither smoothness nor local constancy of the character.
It does not need a topological group structure: finite subsets of a
topological space are compact.

`CharacterLocalizationExactnessClause` additionally requires that `G`
is a topological group and that the complex-valued function underlying
`θ : U →* ℂˣ` is locally constant. Fix a subgroup `M` normalizing `U`
and the literal condition `IsInvariant U M hMU θ` that conjugation by
each element of `M` preserves `θ`. The clause takes representations
`ρ, σ, τ` and actual ambient intertwiners `i : ρ → σ`, `p : σ → τ`.
It assumes injectivity of `i`, surjectivity of `p`, equality of the
image of `i` with the kernel of `p`, and smoothness of the middle
representation `σ`.

The conclusion gives all three short-exactness conditions for the
published maps `map U θ M hMU hθ i` and `map U θ M hMU hθ p`:
injectivity, equality of image and kernel, and surjectivity. These are
intertwiners of the actual descended `M`-representations, not arbitrary
maps between chosen quotient objects. On representatives the first map
sends the class of `v` to the class of `i v`; the second has the
corresponding formula for `p`. Smoothness of the two ends follows from
the injective/surjective transfer results, so only the middle is assumed
smooth.

The actions here are the published **unnormalized** `Localization.action`.
BZ77's inverse half-modulus changes these actions by a common scalar
character of `M`; it changes neither the quotient carrier nor either
linear map. The exactness conditions above therefore give the underlying
linear exactness needed by the normalized functor. Construction of the
Haar modulus and its normalized action, and a statement directly naming
that assembled normalized functor, remain separate obligations.

## Original source and derived scope

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977).

- Section 1.1, printed page 442 / PDF page 3, defines the locally
  profinite ambient groups used in the source.
- Sections 1.2 and 1.5, printed page 443 / PDF page 4, specify complex
  smooth representations and locally constant multiplicative characters.
- Section 1.8(b), printed page 444 / PDF page 5, defines the span of
  `ρ(u)v - θ(u)v`, the actual quotient, and the inverse-half-normalized
  subgroup action.
- The paragraph before Proposition 1.9 and Proposition 1.9(a), printed
  page 445 / PDF page 6, give exactly the compact-subgroup containment
  condition and exactness of localization under that condition.

All five original PDF pages 3–7 were read for this unit. Literature ID:
`bernstein-zelevinsky-1977-induced-i`. Original SHA256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Retained original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
No source errata entry for this ID is present in the admitted public notes.

This is a **derived** formulation of the localization part of Proposition
1.9(a). It retains the exact relation convention and the source's compact
containment hypothesis. It isolates the unnormalized action already
constructed in the Library. The extra ambient locally profinite,
Hausdorff, closed-subgroup, trivial-intersection and closed-product
hypotheses used by BZ77's common induction/localization setting are not
needed for this particular exactness assertion. No parabolic or
unipotent-group specialization replaces the general subgroup `U`.

The rationale for this stated generalization is finite averaging.
A vector in a relation span involves finitely many group elements, so
compact containment detects its relations in one compact subgroup.
Restriction to that subgroup and twisting by the inverse restricted
character preserve smoothness. Compactness and open vector stabilizers
make the finite averaging indices finite; those indices are invertible
over `ℂ`. This gives the injectivity part of exactness. Surjectivity and
middle exactness are algebraic quotient properties. No Haar integral on
an unspecified module topology is used, and no arbitrary-coefficient
exactness assertion is made. This paragraph explains the derived scope;
it is not an implemented Lean proof.

The first clause is the finite-span prerequisite isolated from this
argument. Unlike the exactness clause, it is algebraic once compact
containment is supplied, hence its deliberately weaker hypotheses.
The earlier untwisted `Langlands.SmoothCoinvariantExactnessStatement`
uses Mathlib's trivial-character quotient and a compact-open containment
hypothesis. It remains unchanged. This unit supplies the actual
character-localized maps and normalizing-subgroup actions needed for
general BZ77 localization.

## Dependencies and remaining proof work

The only project import is
`Langlands.Representation.Jacquet.Localization`, which supplies the
relation span, quotient, action, equivariant maps, their representative
formulas, and smoothness descent. All intrinsic construction laws are
proved there. No owner draft or unaccepted mathematical interface is
imported. Mathlib supplies complex coefficients and local constancy.

The compact-detection theorem and character-localization exactness
theorem remain separate proof obligations. This unit contains only
proposition definitions; it does not prove BZ77 Proposition 1.9(a).
The general induction, normalized adjunction/transitivity, character
compatibility, and general geometric-lemma families retain their own
construction and statement obligations.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
