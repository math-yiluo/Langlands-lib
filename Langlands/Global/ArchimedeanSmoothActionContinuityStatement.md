# Joint continuity of the actual smooth right action

`Langlands.Global.ArchimedeanGL.SmoothRightActionContinuityStatement`
is a proposition defining a continuity obligation. This module does not
prove it. Its parameters are every `K : Type u` with `[Field K] [NumberField K]`
and every natural rank `n`, including zero.

## Exact assertion

Let `G` be `Matrix.GeneralLinearGroup (Fin n)
(NumberField.InfiniteAdeleRing K)`, with its existing topology. Let `S` be
the published `DerivativeSmoothFunctions K n`, equipped with its topology of
uniform convergence on compact sets of every genuine enveloping derivative.
Write `e = DerivativeSmoothFunctions.toSmooth K n` for its canonical complex
linear equivalence to `SmoothFunctions K n`.

The statement asserts continuity of the map from the product `G × S` to `S`

```text
(g, f) ↦ e.symm (smoothRightAction K n g (e f)).
```

The underlying function of its value at `(g,f)` is exactly
`x ↦ (e f).val (x * g)`, by the published `smoothRightAction_apply`.
Thus the chosen convention is `R(g)f(x) = f(xg)`, with no inverse in the
right translation. Both the smoothness of each translated function and the
algebraic representation law are already supplied by `smoothRightAction`.
The assertion uses that precise action; it introduces no replacement action
or additional continuity premise.

Continuity is joint in the group element and the smooth function. In
particular, it is stronger than continuity only of each fixed translation or
only of each orbit map. Both occurrences of `S` carry the derivative topology,
and the source carries the product topology. The equivalence `e` is used only
to transport the algebraic action. The statement does not assume that `e` is a
homeomorphism to the original smooth carrier's pointwise subtype topology.

Using the published derivative-coordinate convergence characterization, the
assertion means that simultaneous convergence `gᵢ → g` and `fᵢ → f` implies
uniform convergence on every compact subset of every enveloping derivative of
`R(gᵢ)fᵢ` to the corresponding derivative of `R(g)f`. This interpretation
applies to arbitrary filters, not merely sequences.

## Provenance and intended use

This is an internal continuity statement against the existing concrete
definitions. Harish-Chandra, *Discrete series for semisimple Lie groups II:
Explicit determination of the characters* (1966), §5, printed page 12 /
one-based PDF page 11, supplies the derivative compact-set topology motivating
the published carrier. Sections 7–8, especially Theorem 1 on printed pages
18–19, motivate its later use for closed translation modules and smooth
approximation. The original is registered as
`harish-chandra-1966-discrete-series-ii`, SHA256
`3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`.
These passages were read in the parent source audit; no applicable project
erratum was found. Printed pages 11 and 12 are reversed in the retained PDF.

The current formulation applies to the project's actual completion-based
group, without a connectedness restriction. It is an internal prerequisite,
not a verbatim assertion that the source's entire reductive-group theorem
has already been specialized to this group. Its intended proof uses the
finite-dimensional smooth group structure and compact control of translated
derivatives. Fixed-operator continuity from `ArchimedeanSmoothTopology`
alone is not a proof of joint group-action continuity.

This module supplies no differentiability of orbit maps into `S`, completeness,
integration in locally convex spaces, smooth approximate identity,
reproducing kernel, or automorphic differential-growth theorem. Those remain
separate obligations. Its final Lean example checks only the full parameter
shape of the proposition.
