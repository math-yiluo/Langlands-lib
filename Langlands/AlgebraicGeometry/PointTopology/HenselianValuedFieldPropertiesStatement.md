# Henselian valued fields: the assertions of Conrad's printed p.14

Author: Worker 105.

Statement module for the facts on henselian valued fields that Conrad recalls on printed p.14 of
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), registered source
`conrad-2011-weil-grothendieck-adelic-points`, before Lemma 5.3. Throughout, a valued field is
a nontrivially normed field `K`, and `IsHenselianValuedField K` is the Library's definition:
the absolute value extends uniquely to every algebraic extension field. The completion `k̂` is
Mathlib's `UniformSpace.Completion K`. In the decomposition statement it is instead the
completion `(NormedField.toAbsoluteValue K).Completion` of `K` at its absolute value; this is the
same completion through `WithAbs`, but presented so that Mathlib's completions of extensions
(`AbsoluteValue.Completion`, `AbsoluteValue.LiesOver`, `algebraOfLiesOver`) apply.

## The assertions

Conrad's text, printed p.14: "a valued field is a field k equipped with a nontrivial absolute
value, and it is henselian if this absolute value uniquely extends to every algebraic extension.
A characterization of the henselian property is that k is separably algebraically closed in k̂.
[...] By [Ber, 2.4.3], in the non-archimedean case k is henselian if and only if its valuation
ring is henselian. In general if k′/k is a finite separable extension field of a valued field k
then the nonzero finite reduced k̂-algebra k′⊗k k̂ is the direct product of the completions of k′
at the finitely many valuations extending the one on k. Thus, if k is henselian then k′⊗k k̂ is a
field of degree [k′:k] over k̂, so the archimedean henselian fields are precisely the
algebraically closed subfields of C and the real closed subfields of R (equipped with the induced
valuation). If k is henselian then the functor k′ ↝ k′⊗k k̂ is an equivalence between the
category of finite étale k-algebras and the category of finite étale k̂-algebras".

- `HenselianIffSeparablyClosedStatement`: for every `K`, `IsHenselianValuedField K` holds exactly
  when `separableClosure K (UniformSpace.Completion K) = ⊥`. The forward direction is the
  published `HenselianSeparablyClosedInCompletionStatement`.
- `HenselianIffValuationRingHenselianStatement`: for a non-archimedean `K`
  (`IsUltrametricDist K`) and its valuation ring `O`, given as the subring with
  `x ∈ O ↔ ‖x‖ ≤ 1`, `K` is henselian exactly when `O` is a henselian local ring.
- `TensorCompletionProductStatement`: let `L` be a finite separable extension of `K`. The
  absolute values `w` on `L` lying over the absolute value of `K` (`w.LiesOver`, that is, `w`
  restricts to the norm of `K`) form a finite type. Moreover `K̂ ⊗[K] L` is isomorphic, as a
  `K̂`-algebra, to the product of the completions `w.Completion`, each a `K̂`-algebra through
  `algebraOfLiesOver`. Valuations "extending the one on k" are taken as absolute values
  restricting exactly to the given one; each class of extensions contains exactly one.
- `HenselianTensorCompletionFieldStatement`: for henselian `K` and finite separable `L`,
  `K̂ ⊗[K] L` is a field and has dimension `[L : K]` over `K̂`.
- `ArchimedeanHenselianStatement`: an archimedean `K` (`¬ IsUltrametricDist K`) is henselian
  exactly when there are a ring map `σ : K → ℂ` and `0 < s ≤ 1` with `‖x‖ = ‖σ x‖ ^ s`, and
  either `K` is algebraically closed (`IsAlgClosed K`) or `σ` takes real values and `K` is real
  closed (`IsRealClosed K`). The "induced valuation" is taken up to equivalence, as a power
  `s ≤ 1` of the restriction of the usual absolute value, since a field's absolute value is
  determined only up to such a power by its topology.
- `HenselianFiniteEtaleEquivalenceStatement`: for henselian `K`, base change `A ↦ K̂ ⊗[K] A` is
  bijective on algebra maps between finite étale `K`-algebras (full faithfulness). Every finite
  étale `K̂`-algebra is isomorphic to `K̂ ⊗[K] A` for a finite étale `K`-algebra `A` (essential
  surjectivity). Together these say the functor is an equivalence of categories.
- `HenselianValuedFieldPropertiesStatement`: the conjunction of the six.

All finite extensions, algebras and absolute-value types live in the universe `u` of `K`.

## Qualifications

- The equivalence of categories is stated by its two defining properties, full faithfulness
  and essential surjectivity on objects, without building the categories.
- The archimedean description fixes the meaning of "subfield of ℂ (resp. ℝ) with the induced
  valuation" as an embedding inducing the norm up to a power `s ≤ 1`.
