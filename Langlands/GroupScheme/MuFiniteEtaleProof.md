# Finite étaleness of the actual roots-of-unity group scheme

Author: Worker 407.

`Langlands.GroupScheme.muFiniteEtale.{u}` proves the unchanged Library
proposition `Langlands.GroupScheme.MuFiniteEtaleStatement.{u}`. Its complete
unapplied type is this proposition, with no additional theorem parameters.
Unfolding the proposition gives

```lean
∀ (S : Scheme.{u}) (n : ℕ),
  0 < n → IsUnit (n : Γ(S, ⊤)) →
    IsFinite (mu S n).X.hom ∧ Etale (mu S n).X.hom
```

Here `mu S n` is the existing roots-of-unity group scheme, whose underlying
group scheme is definitionally the kernel of multiplication by `(n : ℤ)`
on `Gm S`. The construction, statement, and imported dependencies are
unchanged. The universe and base scheme are arbitrary.

## Implemented proof

The two helper theorems separate the affine calculation from descent.

`muFiniteEtale_of_affineData` takes the two published proposition targets
`MuAffinePresentationStatement` and `MuCoordinateAlgebraStatement` as
explicit hypotheses. For a commutative ring `A` and positive `n`, the first
identifies the actual `mu (Spec A) n` with the spectrum of
`AdjoinRoot (X^n - 1)`. This is an isomorphism in `Over (Spec A)`, so it
identifies the specified structural morphisms. When `(n : A)` is a unit,
the second supplies module finiteness and algebra étaleness for that
quotient with its canonical `A`-algebra structure.

`RingHom.finite_algebraMap` and `RingHom.etale_algebraMap` turn these into
properties of the coefficient ring homomorphism.
`IsFinite.SpecMap_iff` and `HasRingHomProperty.Spec_iff` then prove the
corresponding properties of the quotient spectrum's structure morphism.
`MorphismProperty.over_iso_iff` transports both across the presentation
isomorphism. This proves finite étaleness over every affine spectrum under
the required hypotheses.

`muFiniteEtale_of_spec` performs descent over `S.affineOpenCover`.
For each affine chart, it maps the assumed global unit along the chart
map on global sections. It then uses `Scheme.ΓSpecIso` to obtain
`IsUnit (n : A)` in that chart's coordinate ring. Naturality of the
natural-number cast under ring homomorphisms justifies both steps.

The existing `mu.baseChangeIso`, after applying `Grp.forget`, identifies
the pullback of the actual roots-of-unity scheme to the chart with
`mu (Spec A) n`. Again, `MorphismProperty.over_iso_iff` transfers the
two morphism properties to the actual pullback. Finiteness and étaleness
are each Zariski local on the target; their
`IsZariskiLocalAtTarget.iff_of_openCover` criteria give the two global
conclusions.

Finally, `muFiniteEtale` applies these helpers to the imported theorems
`muAffinePresentation` and `muCoordinateAlgebra`. Thus no affine
presentation or algebraic finiteness assumption remains in the closing
theorem.

The elaboration options at the start of the module support identification
of the category and morphism-property interfaces. The resulting proof
term is checked by Lean's kernel.

## Sources and provenance

The Stacks Project,
[Example 39.5.2, Tag 040M](https://stacks.math.columbia.edu/tag/040M),
gives the quotient presentation of roots of unity and its base changes.
The geometric result here is derived from the affine calculation in the
**proof** of
[Lemma 59.28.1, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL),
specializing its unit parameter to `1`. That calculation proves finite
freeness of `A[T]/(T^n - 1)` and étaleness using the invertible derivative.
The implemented coordinate-algebra prerequisite retains module finiteness
and étaleness and supplies its standard étale certificate directly.
The present module transports those conclusions to the actual kernel
and applies Zariski descent. It makes no rank or freeness assertion.

The retained originals are registered as
`stacks-mu-finite-etale-2026-10-23` in
`literature/Stacks Project - Roots of unity and the Kummer finite etale calculation (2026-10-23)/`.
Both complete HTML files, including comments, were read for this task.
Tag 03PL Comment 8155 makes the positive-natural convention explicit;
Comment 7888 discusses the need for invertibility in the Kummer
statement. Their SHA256 values are
`4dc450e8ae44698c605f1d8a8a3a637ccfcbb069d2599dc0385d123a2954fdbc`
for `040M.html` and
`a71ef76e1123074b4e38b89a72307a4c7fd8f1ecf7e99fcf94040f5ed03b5773`
for `03PL.html`.

The construction provenance is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, Chapter III, Examples 2–3,
printed p.32 (PDF p.36), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. This passage
describes global units and their roots-of-unity subgroup; the finite
étale conclusion uses the Stacks calculation above. The source file is
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`,
SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`;
PDF p.36 was read. No source-specific project errata note was found
when checked on 26 October 2026.

The two affine inputs are imported by their Library Lean names.
`MuAffinePresentationProof` supplies Worker 690's natural comparison
on all test schemes and Yoneda argument, using the existing
`Multiplicative` and `MultiplicativeLaurent` APIs.
`MuCoordinateAlgebraProof` supplies Worker 354's monic finiteness and
standard étale calculation, following Worker 427's algebraic route.
The local-to-global helpers in the present module are derived from
those results, the existing base-change isomorphism for `mu`, and
Mathlib's locality and spectrum criteria.
