# Square-integrability at a chosen unitary normalization

Author: Worker 17. Worker 175 supplied the focused interface and the proposed
central-character argument.

`Langlands.Classification.ChosenUnitarySquareIntegrability.{uF,uV} F T`
is a proposition definition. It states the normalization claim; it supplies
no proof of that claim.

## Exact statement and conventions

For every prime `p` with `[Fact p.Prime]`, every actual
`F : PadicField.{uF} p`, and every compatible `T : F.TopologicalData`,
the proposition quantifies over:

- a natural number `n` with `0 < n`;
- an actual `π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)`;
- the hypotheses `Representation.IsIrreducible π.representation` and
  `T.IsEssentiallySquareIntegrable π.representation`;
- every `d : UnitaryExponentData (T.determinantNorm n) π.representation`.

Its conclusion is exactly
`T.IsSquareIntegrable (realPowerTwist (T.determinantNorm n) (-d.exponent)
π.representation)`.
The field and carrier universe parameters are independent, and the carrier
universe is saturated at `max uF uV`. Smoothness uses `T.topology`.
No finite dimension, carrier topology, or Hilbert completion is assumed.
The coefficient field is the existing `ℂ`.

Write `ν = T.determinantNorm n = |det|_F`, with residue normalization
`|ϖ|_F = q^(-1)`. The actual action `realPowerTwist ν t ρ` is `ν^t ρ`.
The data `d` consist of a real exponent `a = d.exponent` and an invariant
positive definite Hermitian form on `ν^(-a)π`. The form is arbitrary.
Neither square-integrability of this twist nor equality with any other
exponent is a field of `d` or an additional hypothesis.

`T.IsEssentiallySquareIntegrable` means that some real `s` makes
`ν^(-s)π` square-integrable. `T.IsSquareIntegrable` quantifies over every
Borel Haar measure on the actual central quotient. For each measure it
requires the published admissibility predicate, a smooth unitary scalar
central character, and `MemLp … 2` for all descended absolute matrix
coefficients from smooth-dual functionals and representation vectors.
The imported admissibility convention tests all open subgroups.
Existence of a Haar measure on this quotient is already proved in
`Classification.Tempered`; the universal condition is not vacuous.

## Derived provenance and source boundaries

Henniart 2002, §2.8, printed p.596 (PDF p.10), describes the unique
decomposition of an irreducible essentially square-integrable representation
as `ν^α π_u`, with `α` real and `π_u` unitary and essentially
square-integrable. The twist convention is in §2.5, printed p.595
(PDF p.9). The present statement isolates the analytic square-integrability
claim at any supplied invariant-form exponent. Its central-character
justification below is an internal derived argument, not a verbatim
proposition in that passage.

Kudla 1994, §2.2, printed pp.372–374 (PDF pp.382–384), gives the analytic
tempered definition, the square-integrable block description, and the
equal-exponent grouping observation on printed p.373, following equations
(2.2.2)–(2.2.3). This explains the intended use in the first conjunct of
`Classification.SquareIntegrableEqualExponentGrouping`: the blocks of
`T.SquareIntegrableLanglandsDatum` have independently supplied
`unitaryExponent` data, so their chosen normalized twists must first be
shown square-integrable. Kudla does not state this particular
arbitrary-form normalization interface. Grouping, induction, and the
Langlands quotient theorem are not asserted by this pair.

The existing `Classification.EssentialSquareIntegrabilityExponentUniqueness`
states uniqueness among exponents whose negative twists are already
square-integrable. By itself it does not show that an exponent supplied
only with an invariant positive form is one of them. The present statement
supplies precisely that missing conclusion, without assuming the uniqueness
statement or identifying witness exponents by definition.

## Future proof obligation

The following is the proposed proof route, not an implemented Lean proof:

1. Extract `s` and square-integrability of `ρ_s = ν^(-s)π`. Use an existing
   Haar measure on the central quotient to extract its unitary scalar
   central character `c_s`. No application of Schur's lemma is needed to
   obtain scalar central action: it is part of this analytic witness.
2. Put `a = d.exponent`. The twist identity identifies the action
   `ρ_a = ν^(-a)π` with `ν^(s-a)ρ_s`. Its scalar central action is therefore
   `c_a(z) = ν(z)^(s-a)c_s(z)`.
3. Irreducibility gives a nonzero vector in the common carrier.
   Invariance of `d.form` and positive definiteness, applied to this vector,
   give `|c_a(z)|² b(v,v) = b(v,v)`, hence `|c_a(z)| = 1`.
   The required unit modulus is deduced from the supplied form.
4. Evaluate at the scalar uniformizer matrix `z = ϖ I_n`. The determinant
   norm is `|ϖ|_F^n`, and `|c_s(z)| = 1`; thus
   `|ϖ|_F^(n*(s-a)) = 1`. Since `0 < |ϖ|_F < 1` and `n > 0`,
   this forces `s = a`.
5. Substitute this equality into the original square-integrability witness.
   Its full admissibility, central-character and matrix-coefficient
   conditions for every Haar measure then give the requested conclusion.

Formal transport of the scalar action, the invariant-form computation,
the scalar determinant/uniformizer calculation and the real-power
injectivity argument remain proof obligations. No square-integrable
induction, regular exhaustion, or classification theorem is an input.

## Dependencies and retained originals

The direct imports are `Langlands.Representation.Category.Basic` and
`Langlands.Representation.Classification.Tempered`; the latter imports
`Classification.Essential`. They supply the existing representation model,
analytic predicates, actual twists and `UnitaryExponentData`.
`Classification.LanglandsData` and `TemperedBlockStatement` explain the
downstream use but are not imports or assumptions.
No published Lean/Markdown pair is changed.

The following registered originals were read directly and their hashes
verified on 2026-10-24:

- `henniart-2002-characterization`: Guy Henniart, *Une caractérisation de la
  correspondance de Langlands locale pour GL(n)*, Bull. Soc. Math. France
  130 (2002), pp.587–602; §§2.5 and 2.8, printed pp.595–596
  (PDF pp.9–10). SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `kudla-1994-local-langlands-nonarchimedean`: Stephen S. Kudla, *The local
  Langlands correspondence: the non-archimedean case*, Motives, Part 2,
  PSPM 55 (1994), pp.365–391; §2.2, printed pp.372–374
  (PDF pp.382–384 of the retained volume), with p.373 checked visually.
  SHA-256
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.

No source-specific errata directory was present in Library
`e4296643398fb6f96e73eb81e8e5d19a0d2650be` or the shared notes directory
when checked. The public classification source-boundary note was consulted;
its warnings distinguish unitary central character from an invariant
positive form and do not supply the missing normalization proof.
