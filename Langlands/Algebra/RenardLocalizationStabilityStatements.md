# Actual localization, stable powers, and the canonical stable image

Authors: Worker 709 (Lean file and first Markdown) and Worker 977 (source
check and Markdown revision). This is a statement-only, internal derived unit
for ordinary unital modules. It proves none of its propositions. Its
namespace is `Langlands.Renard.EndomorphismLocalization`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, Appendix C.II, final proposition and proof,
printed page 279 / PDF page 285, motivates this unit. The stability
definition is on printed page 276 / PDF page 282. The actual endomorphism
localization and its following lemma and corollary are in Appendix A.III.1,
example 5, printed pages 252–253 / PDF pages 258–259. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The readable original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

On PDF page 282 an endomorphism t is *stable* when ker t = ker t² and
Im t = Im t², and *finally stable* when some power t^n with n ∈ ℕ* is stable.

The C.II proposition takes a commutative Noetherian complex algebra B,
a finitely generated B-module L, an endomorphism a of L, and assumes that
the localization (L_a, ã) of A.III.1, example 5, is a finitely generated
B-module. It concludes that a is finally stable and that, for every n ∈ ℕ*
with a^n stable, K = ker a^n and I = Im a^n satisfy L = K ⊕ I and
(L_a, ã) ≅ (I, a|_I). Its proof first shows that the canonical map
ι : L → L_a is surjective, then uses the A.III.1 lemma and corollary to
identify L_a with L/⋃ₙ ker aⁿ, and finally obtains a nonzero n with
⋃ₘ ker aᵐ = ker aⁿ.

## Provenance: internal derived specialization and strengthening

The source's global conventions on printed page 6 / PDF page 12 allow
nonunital rings and modules on which the unit need not act. The present
statements use Mathlib's ordinary unital modules over arbitrary commutative
unital rings. They describe an ordinary-module specialization and internal
strengthenings, not the full source proposition, and no unit is added to the
source's conventions. The relations to the source are as follows.

- `FiniteActualLocalizationStatement` is the ordinary unital-module
  specialization of the C.II proposition, with an arbitrary Noetherian
  commutative ring in place of the complex algebra B. It also records the
  surjectivity of ι and the common kernel exponent that the source proof
  establishes on its way.
- `NoetherianActualLocalizationStatement` replaces "Noetherian ring and
  finitely generated modules" by Noetherianity of the two modules V and
  `Localized a` themselves. Over a Noetherian ring, finitely generated
  modules are Noetherian, so this is a strengthening. A proof need not follow
  the source's integrality argument in End_B(L_a), which uses ring
  Noetherianity; for example, the ascending chain of submodules
  ã⁻ᵏ ι(V) of the Noetherian module `Localized a` stabilizes.
- `StablePowerImageStatement` isolates the conclusion for a positive stable
  power and has no Noetherian or finite-generation hypothesis. This
  strengthening is internal; a proof is expected to use the actual
  localization kernel and exhaustion, not finiteness.
- The isomorphism (L_a, ã) ≅ (I, a|_I) is stated as the existence of a
  unique R-linear equivalence that intertwines the operators and whose
  inverse is the restriction of the actual ι to I. This canonical
  normalization is an explicit refinement of the source's unnamed
  isomorphism, which the source proof obtains from the surjective ι.

None of these extensions is attributed verbatim to Renard; hence the
provenance is derived.

Worker 709 read the original passages above and visually checked PDF page
285. Worker 977 independently read PDF pages 285 (also rendered as an image),
282, 258–259 and 12 after confirming the source SHA256. Public notes
`notes/renard/stable-quotients.md` and `notes/renard/appendix-a-corrections.md`
record the relevant source boundaries. The current Library has no separate
errata note for this source. Worker 977 also read PDF pages 18–19 of the
registered older supplementary author errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
which contain its Appendix C entries. None of those entries concerns the
final C.II proposition, and they supply no change to the source's nonunital
conventions.

## Actual models and universes

The sole project import is the public
`Langlands.Algebra.RenardEndomorphismLocalization`. Its actual objects
`Localized a`, `iota a` and `localizedEnd a` are used unchanged.
`Localized a` is Mathlib's module localization of the evaluation
R[X]-module of a at the powers of X; `iota a` is its canonical R-linear map
v ↦ v/1, and `localizedEnd a` is multiplication by X, viewed as an R-linear
endomorphism. The construction already proves its invertibility and
universal property. No abstract carrier or supplied localization
certificate replaces it here.

Throughout, `R : Type uR` has `[CommRing R]`, and `V : Type uV` has
`[AddCommGroup V] [Module R V]`. The universes uR and uV are independent;
`Localized a` lives in `Type (max uR uV)`. The stable image is the actual
submodule `LinearMap.range (a ^ n)` of V, with its inherited R-module.
No dimension, nontriviality, nonzero endomorphism, ring finiteness or
universe-shrinking assumption is imposed. Zero rings and zero modules
are allowed.

`Mathlib.RingTheory.Noetherian.Basic` supplies the ordinary
`IsNoetherian`, `IsNoetherianRing` and `Module.Finite` interfaces used to
write the hypotheses. No proof of the Noetherian core or of the actual
localization kernel and exhaustion is imported. Their future proofs are
separate obligations, not assumptions of these statements.

## Exact propositions

For readability put L = `Localized a`, i = `iota a`,
A = `localizedEnd a`, K = `LinearMap.ker (a ^ n)`,
S = `LinearMap.range (a ^ n)` and s = `S.subtype`.
All equations below are equations of actual R-linear maps or submodules.

`StablePowerImageAt a n`, for every natural number n, is exactly the
conjunction of `IsCompl K S` and

```text
there exists a unique e : L ≃ₗ[R] S such that
  s ∘ e ∘ A = a ∘ s ∘ e
and
  e⁻¹ = i ∘ s.
```

In Lean, the operator equation is
`S.subtype.comp (e.toLinearMap.comp (localizedEnd a)) =
a.comp (S.subtype.comp e.toLinearMap)`.
The inverse equation is
`e.symm.toLinearMap = (iota a).comp S.subtype`.
Both equations lie inside `∃! e`; uniqueness concerns equivalences satisfying
their conjunction. The inverse equation canonically identifies e as the
inverse of the restriction of the actual i to S. The operator equation
identifies the actual localized pair with a restricted to S, using the
inclusion of S into V; no separate restricted-endomorphism constructor is
introduced. `IsCompl K S` means that K and S are disjoint and their sum is
all of V. This parameterized definition assumes no positivity or stability;
it can fail at n = 0 (for example for a = 0 on a nonzero module), and the
closed statements supply the hypotheses.

`NoetherianActualLocalizationStatement` quantifies over all R, V, module
instances and a. Its only extra premises are `IsNoetherian R V` and
`IsNoetherian R (Localized a)`. Its conclusion is that i is surjective and
there exists a single n with `0 < n` such that

```text
ker i = ker(a^n),
ker(a^n) = ker((a^n)^2),
range(a^n) = range((a^n)^2).
```

The witness n is common to all three equalities. Source and localization
module Noetherianity are hypotheses; ring Noetherianity, finite generation
and dimension are not.

`StablePowerImageStatement` quantifies over all R, V, a and every n.
It assumes `0 < n` and precisely the displayed kernel and range stability
equalities of a^n. It concludes `StablePowerImageAt a n`.
There is no Noetherian or finite-generation premise. Positivity applies
to the exponent n, not to the ring, module or endomorphism. Every positive
stable exponent is covered, not merely one existential exponent.

`FiniteActualLocalizationStatement` quantifies over all R, V, a and assumes
`IsNoetherianRing R`, `Module.Finite R V` and
`Module.Finite R (Localized a)`. Its conclusion is the conjunction of:

1. Surjectivity of the actual i.
2. One common positive exponent with all three equalities above.
3. For every positive exponent n satisfying the two stability equalities,
   `StablePowerImageAt a n`.

These conclusions are written literally in Lean. The proposition assumes
neither module Noetherianity nor surjectivity, stability, decomposition or
an equivalence; those are intended consequences of its stated hypotheses.

`ActualLocalizationStabilityStatements.{uR, uV}` is the conjunction of
`NoetherianActualLocalizationStatement`, `StablePowerImageStatement` and
`FiniteActualLocalizationStatement`, all at exactly these same independent
universes. All five declarations are `def ... : Prop`. This file contains
no theorem and no proof.

## Scope

The possibly nonunital B-action construction, compatible complex-linearity,
the unitization and finite-generation/Noetherian comparisons, and the full
source-facing C.II proposition remain parent obligations. This unit also
does not state the distinct A.III.1 power-kernel-union quotient comparison
or its surjective-canonical-map corollary, and it imports neither
construction. The separate C.II successive-quotient exact sequence is
unchanged.

## Development checks

In the pinned Lean service, environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Worker 709 and Worker 977 each
compiled this module and inspected `ActualLocalizationStabilityStatements`:
zero errors and warnings, `statement_returns_prop` true, level parameters
`uR uV`, and only the standard assumptions `propext`, `Classical.choice`
and `Quot.sound`. Private diagnostic modules, excluded from this unit,
printed all five complete declaration bodies and checked the unapplied
types, swapped universe instantiations, the common positive witness, both
equations inside unique existence, and the every-positive-stable-exponent
conclusion. These checks inspect the proposition definitions; no proof
acceptance is claimed. Compilation does not establish independent semantic
acceptance or publication.
