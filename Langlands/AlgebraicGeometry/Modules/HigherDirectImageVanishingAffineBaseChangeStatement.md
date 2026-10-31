# Affine base change from vanishing higher direct images

`Langlands.AlgebraicGeometry.Modules.HigherDirectImageVanishingAffineBaseChangeStatement`
is a universe-polymorphic `Prop`-valued definition. It states a
specialized derived consequence of proper perfect direct image and
arbitrary derived base change. It does not prove the proposition.

## Complete proposition

```lean
def HigherDirectImageVanishingAffineBaseChangeStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    Smooth f → IsProper f →
    ∀ Q : Picard.LineBundle X,
      (∀ n : ℕ, IsZero ((DerivedSections.higherDirectImage f n).obj Q.obj)) →
      ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ Y) (n : ℕ),
        IsZero
          ((DerivedSections.relativeCohomology (pullback.snd f x) n).obj
            ((Scheme.Modules.pullback (pullback.fst f x)).obj Q.obj))
```

The namespace is `Langlands.AlgebraicGeometry.Modules`; `Picard`
denotes `Langlands.AlgebraicGeometry.Picard`. The open namespaces
are `CategoryTheory`, `CategoryTheory.Limits`, and `AlgebraicGeometry`.
There are no additional outer parameters or hypotheses.

## Actual objects and scope

The schemes `X` and `Y` and the morphism `f : X ⟶ Y` are arbitrary
apart from the two geometric premises `Smooth f` and `IsProper f`.
`Q : Picard.LineBundle X` is the published full-subcategory object of
actual structure-sheaf modules locally free of rank one, and
`Q.obj : X.Modules` is its underlying module.

The hypothesis quantifies over every natural degree, including zero,
of the actual right-derived scheme-module pushforward
`DerivedSections.higherDirectImage f n`. Its zeroth term is not
omitted. No cohomology vanishing hypothesis is imposed directly on
any base change.

For every actual commutative ring object `R : CommRingCat.{u}` and
scheme morphism `x : Spec R ⟶ Y`, the fibre product is the ordinary
scheme pullback `pullback f x`. Its first projection goes to `X`,
and its second projection goes to `Spec R`. The coefficient on the
fibre product is the actual module

```text
(Scheme.Modules.pullback (pullback.fst f x)).obj Q.obj.
```

The conclusion is zero cohomology as an actual `R`-module, computed
by the published functor
`DerivedSections.relativeCohomology (pullback.snd f x) n`.
Both degree quantifiers include zero.

The universe, characteristic, dimension and affine ring are
unrestricted. The proposition includes empty schemes and zero
rings. There is no noetherian, reducedness, finite-type-over-a-field,
projectivity, connectedness, positive-dimension, coherence,
perfect-representative, comparison-isomorphism or injective-acyclicity
premise. The arbitrary morphism `x` is not assumed flat.

## Original source and derived rationale

The registered original is
`stacks-perfect-complexes-a04446e5`, folder SHA256
`54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`,
at Stacks Project commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. Its `perfect.tex`
chapter is *Derived Categories of Schemes*. The relevant passages,
read in full, are:

- `lemma-flat-proper-perfect-direct-image-general`, tag 0B91,
  lines 7524–7544, including its complete proof. A proper morphism
  of finite presentation has perfect direct image and arbitrary base
  change for a perfect coefficient when the morphism is flat, or
  for a finitely presented module flat over the base.
- `remark-explain-perfect-direct-image`, tag 0A1I,
  lines 7443–7455. Over an affine base, one finite complex of finite
  projective modules computes sections after every affine scalar
  change under its stated finiteness, flatness and proper-support
  hypotheses.

The retained comment supplement is
`stacks-universal-perfect-sections-comments-20261029`. Its tag 0B91
comments #4352 and #4499 remove flatness of the morphism from part
(2), while retaining flatness of the coefficient over the base.
The pinned TeX already includes that correction. The source and
supplement READMEs and both comments were re-read on 2026-10-30.
No source-specific errata note was found in the supplied project
and Library notes.

This proposition is a derived specialization, not a verbatim
numbered source lemma. A smooth proper morphism is flat and of
finite presentation. A line bundle is a perfect coefficient and
is flat over the base. Thus the source's proper direct image and
arbitrary base-change theorem applies.

Vanishing of every nonnegative `Rⁿ f_* Q` makes the derived direct
image zero; its negative cohomology is already zero for this
right-derived functor on a module in degree zero. Derived pullback
of zero along any `x` is zero. Proper derived base change therefore
makes the derived direct image on `Spec R` zero, which gives the
asserted relative cohomology vanishing.

Equivalently, affine locally on `Y`, a bounded finite-projective
representative of this zero derived object is acyclic. A bounded
acyclic complex of projective modules is split exact: starting at
the last nonzero term, the surjection onto that projective term
splits; its kernel is projective, and the argument continues down
the finite complex. Tensoring preserves these split short exact
sequences, so ordinary scalar extension by any algebra preserves
the acyclicity. Bounded
projective terms also compute derived scalar extension. This
argument uses joint vanishing in all degrees; it does not assume
that individual higher direct images commute with arbitrary base
change.

## Separate proof obligations and consumer

A later exact proof must identify the published natural-degree
right-derived functors with the integer-degree derived-category
cohomology used by the source, including vanishing in negative
degrees. It must establish the proper perfect-section comparison
for the actual module functors and the derived-composition
comparison between pushforward followed by affine sections and
the right-derived functor of that composite. Local freeness must
identify ordinary pullback of `Q.obj` with derived pullback.
For an arbitrary `Y`, affine restriction and localization must
pass from zero higher direct images to zero affine-local derived
sections; arbitrary scalar change then preserves zero. An affine
cover of `Y` need not contain the entire image of `x`, so the proof
must use its inverse-image cover on `Spec R`, refine by affine
opens, and detect or glue the resulting zero object there. The published
`UniversalPerfectSectionsStatement` is a proposition stating a
relevant affine perfect-representative input; its definition is
not a proof of that input. A degreewise `baseChangeMap` alone also
does not supply the required isomorphism.

The second-projection finite-support detection consumer is
`Langlands.AbelianScheme.AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement`.
After its separate finite-support, Leray and section-detection
steps make all higher direct images zero, the present proposition
can be specialized to the second square projection, `R = K`, and
each rational point. The separately published second-fibre
cohomology identification then gives the consumer's literal
fibre expression.

This is distinct from the forward rational-fibre criterion, which
deduces zero restrictions of higher direct images from vanishing
on fibres of an open subscheme, and from the first-projection
total-vanishing adapter. Those results, this proposition's exact
proof, and the consumer's exact proof remain separate obligations.

Worker 360 prepared the shared statement draft for task
`66163118-2990-48e3-9fec-026452cb617f`. Worker 152 checked its exact
interface and source passages and expanded the split-exactness
and comparison explanations for submission.
