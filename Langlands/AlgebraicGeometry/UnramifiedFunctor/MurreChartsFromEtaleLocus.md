# Murre's charts from Lemma 2 (statement)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsFromEtaleLocus` defines one
`Prop`:

```
def MurreChartsFromEtaleLocusStatement : Prop :=
  MurreEtaleLocusOpenStatement.{u, v} → MurreNoetherianChartsStatement.{u, v}
```

Both sides are published statements:

* `MurreEtaleLocusOpenStatement` (module `MurreEtaleLocusOpen`): Murre's Lemma 2 over the
  spectrum of a noetherian ring `R`. Under the hypotheses of the inductive step of Murre's
  proof of Proposition 2 (the conditions `MurreConditions`, representability of the base change
  to every `Spec 𝒪_{Spec R, s}` and to every `Spec (R/I)` with `I ≠ 0`), the set of points
  where an element `ξ ∈ F(U)` is infinitesimally étale is open, for `U` locally of finite type,
  quasi-compact, separated and formally unramified over `Spec R`.
* `MurreNoetherianChartsStatement` (module `MurreLocalToGlobalSteps`): under the same
  hypotheses, there is a family of elements `ξᵢ ∈ F(Uᵢ)`, indexed by a `u`-small type, with each
  `Uᵢ` locally of finite type and formally unramified over `Spec R` and each `ξᵢ : Uᵢ → F` a
  monomorphism that is infinitesimally étale at every point, such that every point of `F` with
  values in a field factors through some `ξᵢ`.

The statement says that the second follows from the first. Universe parameters are those of
both statements: `u` for schemes and rings, `v` for the values of `F`.

## Provenance

The implication is the part of the proof of Proposition 2 in J. P. Murre, *Representation of
unramified functors. Applications (according to unpublished results of A. Grothendieck)*,
Séminaire Bourbaki exp. 294 (registered as `murre-1965-bourbaki-294-unramified-functors`),
printed pp.252–253 (PDF pp.11–12), that comes after Lemma 2 and before the final application
of Lemma 3. It is a derived intermediate statement of this project: Murre does not state it
separately. It is proved in module `MurreCharts` as
`Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts.murreChartsFromEtaleLocus`.
