# Normal stalks of integral smooth schemes over arbitrary fields

Author: Worker 57.

`Langlands.AlgebraicGeometry.SmoothIntegralNormalStalksStatement.{u}` is the
following proposition:

```lean
∀ (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
  (p : X ⟶ Spec (CommRingCat.of K)),
  Smooth p → ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)
```

All notions are Mathlib's existing notions. The conclusion says that the
actual local ring of the structure sheaf at each point is integrally closed
in its fraction field. The hypothesis `IsIntegral X` already makes these
stalks domains. The universe `u` is arbitrary.

The field may have any characteristic and need not be perfect or algebraically
closed. There is no properness, separation or quasi-compactness hypothesis.
Integrality is an explicit restriction on this target, even though the
original normality theorem cited below applies to all smooth schemes.

This target will supply normality for the actual integral connected-component
schemes in the Harris application over the original number field. It introduces
no alternative scheme or normality predicate, and supplies no proof or
Harris representability witness.

## Original sources and derived provenance

The original [Stacks Project Tag 056T](https://stacks.math.columbia.edu/tag/056T),
Lemma 33.25.4 and its proof, show that a scheme smooth over any field is normal
(and prove the stronger geometric normality assertion).
The retained `056T.html` belongs to registered source
`stacks-global-functions-field-and-fibre-criterion-2026-10-23`, content SHA256
`c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`.

[Tag 033I](https://stacks.math.columbia.edu/tag/033I), Definition 28.7.1,
defines normality of a scheme by normal-domain local rings.
[Tag 0309](https://stacks.math.columbia.edu/tag/0309), Definition 10.37.1,
defines normality of a domain by integral closedness in its fraction field.
The retained `033I.html` and `0309.html` belong to registered source
`stacks-normal-scheme-domain-stalk-definitions-2026-10-25`, content SHA256
`4b962e26e7516ff782a6f7b146df1c0c9972c10ecdbf685912db247b39209e79`.

Applying these original statements and definitions to the integral smooth
scheme gives the displayed stalk assertion. This is a derived specialization,
not a verbatim translation. The three retained tagged pages and their comment
sections were read directly; none has a correction affecting this assertion.
No source-specific project errata file was found. The Lean module only defines
the proposition. Its exact proof remains a separate publication obligation.
