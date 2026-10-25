# Irreducibility of square-integrable block induction

Author: Worker 389.

`Langlands.Classification.SquareIntegrableBlockInductionIrreducibility.{uF,uV}
F T` states the irreducibility conclusion of
[`SquareIntegrableBlockInduction`](TemperedBlockStatement.md), retaining its
entire telescope and its block hypotheses. The parent statement was authored
by Worker 15. This focused source-derived projection is a proposition
definition returning `Prop`; this file contains no proof of it or of the parent.

## Exact scope

Fix arbitrary `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p` and a supplied
`T : F.TopologicalData`. The field and representation universes `uF` and `uV`
are independent. With the local instance `T.topology`, the proposition quantifies
in the same order as the parent over every `n : ℕ`, a hypothesis `0 < n`, every
`B : GeneralLinear.BlockShape n`, and every actual family

```lean
σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
  (GeneralLinear (B.size i) F.Carrier)
```

Here `i : Fin B.length`; the shape supplies positive block ranks and their sum
`n`. The hypothesis is exactly

```lean
∀ i, Representation.IsIrreducible (σ i).representation ∧
  T.IsSquareIntegrable (σ i).representation ∧
  IsUnitarizable (σ i).representation
```

With `I := (T.normalizedProductInductionFunctor B).obj σ`, the entire conclusion
is `Representation.IsIrreducible I.representation`. This is precisely the first
conjunct of the parent conclusion. Neither a proof of the parent nor any
classification, segment, genericity, chosen representation model or property
of the induced representation is an input. Unitarizability and temperedness
of `I` are outside this conclusion.

## Actual analytic and algebraic objects

The imported `Classification.Tempered` definition `T.IsSquareIntegrable` requires
admissibility, an actual unitary scalar central character, and `L²` membership
of every descended absolute smooth matrix coefficient on the actual quotient
`GL_r(F) / Z`. It quantifies over all Borel Haar measures on that quotient.
The imported Haar-existence theorem prevents vacuity. No segment description,
Jacquet-exponent bound or coefficient-growth certificate replaces this condition.

`IsUnitarizable ρ` is `Nonempty (InvariantPositiveForm ρ)`. A witness is an actual
positive definite invariant Hermitian form, implemented by
`InnerProductSpace.Core ℂ` together with invariance under the given action.
No norm, Hilbert completion or topology on the carrier is supplied by this
hypothesis. A unitary central character alone is not this hypothesis.

`Induction.BlockFactors` constructs the tensor product of the actual blocks,
inflates it along the Levi projection, and induces from the standard upper
block parabolic. The functions satisfy

```text
f(pg) = δ_P(p)^(1/2) σ_tensor(p) f(g),    (I(g₀)f)(x) = f(xg₀).
```

The half-modulus is the positive square root; its sign and the right-translation
action agree with Kudla §1.1, pp.367–368, equations (1.1.2)–(1.1.4).
The input carriers and induced carrier all lie in `Type (max uF uV)`, since
induction raises the carrier universe to `max uF (max uF uV)`.
The supplied `T` is retained throughout; it is not replaced by a canonical
realization. The only direct import of this pair is the unchanged
`Langlands.Representation.Classification.TemperedBlockStatement`.

## Original-source correspondence

Jacquet–Shalika (JS83) §1.2 fixes an upper standard parabolic on pp.107–108.
On p.109, after describing square-integrable irreducible preunitary smooth
representations and their associated unitary representations, the authors
consider induction of irreducible square-integrable factors and explicitly
conclude that the induced representation is irreducible. Their argument uses
the irreducible mirabolic representation induced in Mackey's sense from a
nondegenerate character, together with Whittaker multiplicity one. Thus the
upper-parabolic smooth preunitary assertion on p.109 supplies the direct
statement source here. The block invariant-form hypothesis records preunitarity
on the actual smooth carriers. This source assertion is not a formalized proof,
and its classification discussion later on p.109 is not used as a theorem input.

Jacquet (Ja77) has a different formal setting. Section 0, printed p.91,
restricts throughout to unitary Hilbert representations and Mackey induction.
Theorem 3.2 and Corollary 3.3, pp.98–99, prove irreducibility and mirabolic
genericity of the unitary induction of, respectively, irreducible unitary
generic factors and square-integrable factors. The parabolic chosen on p.98
is the transpose of a standard parabolic. These are not already the smooth
upper induction and algebraic irreducibility in the present Lean conclusion.
In particular the unitary premise of the article remains in force in its
corollary. Ja77 is a supporting source for the analytic route, subject to the
comparisons below; it supplies no tempered exhaustion or unordered uniqueness
theorem here.

Kudla (Ku94) Proposition 2.2.1, p.373, states the tempered induction description.
Its following paragraph explains irreducibility using the square-integrable
segment description of Proposition 1.2.3, pp.369–370, the fact that the centered
segments in question cannot be linked, and the irreducibility criterion of
Theorem 1.2.5(d), p.371. Together with §1.1 this is an alternative source route
to the same normalized smooth induction conclusion. A Lean proof along it
would first need the actual classification of every analytic square-integrable
block by such segments, the nonlinkage argument, and the segment-product
irreducibility theorem, with the necessary transport isomorphisms. None of
these is assumed here. This route cannot use the parent block-induction theorem,
tempered exhaustion or unitarity/genericity consequences as upstream inputs;
it also cannot assume the separate downstream square-integrable Langlands
classification. The recorded source assertions and open statement tasks are
not proved inputs.

## Remaining proof obligations

Even the direct JS83 source formulation leaves its proof to be implemented.
Following its unitary-mirabolic argument, or applying Ja77 directly, requires
at least the following comparisons:

- Complete the given positive forms to continuous unitary Hilbert
  representations, compare their Hilbert matrix coefficients with the
  smooth-dual coefficient definition, and justify square-integrability
  modulo the center. Recover each admissible smooth carrier as the appropriate
  smooth vectors; mere density of that carrier is insufficient.
- Identify the actual finite tensor-product smooth upper induction with the
  smooth vectors of normalized unitary/Mackey induction, including the induced
  invariant form, continuity, the positive half-modulus, and right translation.
  Hilbert completion and this identification are not fields of the proposition.
- Relate Hilbert irreducibility, which concerns closed invariant subspaces, to
  `Representation.IsIrreducible`, which rules out every nontrivial algebraic
  invariant submodule. This needs a smooth/admissible comparison, rather than
  an inference from density alone.
- For the Ja77 transpose-parabolic route, construct the actual conjugation and
  block-reversal identifications with the upper block parabolic used here,
  transporting the factors and modulus without changing the conclusion's
  ordered family. Opposite parabolics are not silently identified.
- Supply the mirabolic restriction and uniqueness results used in the source,
  or a different complete proof. Any passage from a single Haar measure to the
  Library's all-Haar convention needs Haar-scaling and `L²` comparison. Any
  comparison with the sources' matrix coefficients must address smooth-dual
  functionals on the actual admissible carriers.

These are proof obligations, not extra hypotheses or claimed results of this
pair. The independent successor proof must establish the exact proposition.
Separate tensor, invariant-form, analytic-exponent and grouping tasks retain
their owners. No analytic bridge or segment-classification prerequisite is
implemented or duplicated in this statement contribution.

## Retained editions and reading extent

The following already registered originals were read directly for this pair,
and their SHA-256 hashes were verified. PDF page numbers are one-based.
No source-specific errata directory or note for these IDs was present in the
workspace or supplied Library on 2026-10-25. The public classification source
boundary note was also consulted; absence of a retained erratum is not a claim
that the literature has no corrections.

- **JS83:** H. Jacquet and J. A. Shalika, *The Whittaker models of induced
  representations*, Pacific J. Math. 109 (1983), 107–120.
  ID `jacquet-shalika-1983-whittaker`;
  SHA-256 `e171831da6c064fdcb55efe79381ba1f85daa4efd7f3a79071589ffee9527f98`.
  Read printed pp.107–109 (PDF pp.2–4), especially §1.2; p.109 was also
  inspected as an image. Retained file:
  `/home/taskhub/central-library/Jacquet-Shalika--The Whittaker models of induced representations--1983.pdf`.
- **Ja77:** H. Jacquet, *Generic representations*, LNM 587 (1977), 91–101.
  ID `provided-7fa6dd7a9bc39b0ef92f41d27dd4970725cdfbe795124370c63ffe3d8743b116`;
  SHA-256 `073cdfbdac1db264653544249d1060ba47704cc1678a5f545b9cd0ca5df46c8a`.
  Read §0, p.91 (PDF p.97), and Theorem 3.2/Corollary 3.3 with the proof,
  pp.98–99 (PDF pp.104–105). Retained file:
  `/home/taskhub/pilot/literature/Jacquet (1977), Generic representations, LNM 587.pdf`.
- **Ku94:** S. S. Kudla, *The local Langlands correspondence: the
  non-archimedean case*, Motives, Part 2, PSPM 55 (1994), 365–391.
  ID `kudla-1994-local-langlands-nonarchimedean`;
  SHA-256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
  Read pp.367–373 (PDF pp.377–383), especially §1.1 and equations
  (1.1.2)–(1.1.4), Proposition 1.2.3, Theorem 1.2.5(d), and Proposition 2.2.1
  with the following nonlinkage paragraph. Equation (1.1.3), p.368, was also
  inspected as an image. Retained whole-volume file:
  `/home/taskhub/central-library/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994.pdf`.
