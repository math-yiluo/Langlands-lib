# Quotient maps of scheme solutions along fppf covers

This module extends the published `SchemeSolution` interface (module
`Langlands.GroupScheme.Descent.SchemeSolution`) from surjective étale maps to
surjective flat maps locally of finite presentation (fppf maps). All schemes
lie in an arbitrary universe `u`. Let `p : S ⟶ B` be a scheme map, `G` an
actual group scheme over `S`, `D : Datum p G` a Čech datum, and
`s : SchemeSolution D` a supplied underlying quotient: an object
`s.obj : Over B`, a map `s.proj : G.X.left ⟶ s.obj.left`, a pullback square and
the relation equation.

- `proj_locallyOfFinitePresentation`: if `p` is locally of finite
  presentation, then so is `s.proj`. Being locally of finite presentation is
  stable under base change, and `s.proj` is a base change of `p`.
- Under `[Flat p] [LocallyOfFinitePresentation p] [Surjective p]` the map
  `s.proj` is flat, locally of finite presentation and surjective. These are
  the published instances `proj_flat` and `proj_surjective` together with the
  instance above. Mathlib's instance for surjective flat maps locally of finite
  presentation then makes `s.proj` an effective epimorphism.
- `fppfDesc f hf` factors every scheme map `f : G.X.left ⟶ T` that is
  invariant under the relation (`D.source ≫ f = D.target ≫ f`) through
  `s.proj`. It is `EffectiveEpi.desc`. The compatibility hypothesis needed
  there is the published `comp_eq_of_proj_eq`, which uses that
  `D.source, D.target` is the full kernel pair of `s.proj`.
- `fppfDesc_fac` gives `s.proj ≫ s.fppfDesc f hf = f`. `fppfDesc_unique`
  gives uniqueness, by cancelling the epimorphism `s.proj`.

No quasi-compactness, affineness or separation hypothesis is used. Provenance
is internal: these are the étale arguments of `SchemeSolution` with Mathlib's
fppf effective-epimorphism instance (`Mathlib.AlgebraicGeometry.Sites.Fpqc`)
used in place of the étale one. There is no literature assertion.
