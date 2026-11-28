# Finite Levi restriction of the actual archimedean enveloping centres

Module `Langlands.Automorphic.GroupSchemeLeviCenterRestrictionProof`, namespace
`Langlands.Automorphic.GroupSchemeFunctions`.

## The theorem

`parabolicLeviCenterRestriction` proves `ParabolicLeviCenterRestrictionStatement.{u}` (module
`Langlands.Automorphic.GroupSchemeLeviCenterRestriction`) for an arbitrary universe. Take a
connected reductive affine group `G` over a number field `F`, a parabolic subgroup
`q : Q ⟶ G` with a geometric unipotent radical `iV : V ⟶ Q` and an affine rational
Levi `l : M ⟶ Q` with `IsIso (subgroupMultiplication l iV)`. Choose the smooth
atlases of `G` and `M`, the `AdelicDifferentialCommutator` hypotheses for their
enveloping actions, and an archimedean point `a`.
Then some finite complex algebra map `p` from the enveloping centre of `G(F_∞)` to that of
`M(F_∞)` satisfies the following. For every plot-smooth function `f` on `G(F_∞)` that is
invariant on the left under the radical points, restricting `z · f` to the Levi after right
translation by `a`, `m ↦ (z · f)(l(m) a)`, gives `p(z)` applied to the restriction of `f`.
The actions are the actual right differential actions on both point groups.

## The proof

The proof is the following application.

```
parabolicLeviCenterRestrictionReduction
  Langlands.Algebra.ParabolicCenterProjection.parabolicCenterProjectionFinite
  parabolicLeviTangentGrading
```

- `parabolicLeviCenterRestrictionReduction` (module
  `Langlands.Automorphic.GroupSchemeLeviCenterRestrictionReduction`) proves the target from two
  inputs. The first is the finiteness statement
  `Langlands.Algebra.ParabolicCenterProjection.ParabolicCenterProjectionFiniteStatement` at the
  universes `u, u`. The second is the archimedean tangent grading
  `ParabolicLeviTangentGradingStatement`. Its Markdown describes the argument: the Levi
  projection of the centre modulo the right ideal of positive eigenvectors, and why that ideal
  acts by zero on radical-invariant functions restricted to the Levi.
- `Langlands.Algebra.ParabolicCenterProjection.parabolicCenterProjectionFinite` (module
  `Langlands.Algebra.ParabolicCenterProjectionFiniteProof`) proves the finiteness statement.
- `parabolicLeviTangentGrading` (module `Langlands.Automorphic.GroupSchemeParabolicTangentProof`)
  proves the tangent grading statement.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Sources

The differential transfer is used in Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series* (1995), I.2.17, printed pp. 37–38 (PDF pp. 20–21), registered as
`moeglin-waldspurger-1995-growth-and-constant-terms`. The underlying projection of the centre
and its finiteness are in Harish-Chandra, *Automorphic Forms on Semisimple Lie Groups* (LNM 62,
1968), Chapter I, §6, printed p. 19 (PDF p. 29), registered as
`provided-d0ff4732ff6b5d8ecf8562752577df639622e8aad2899ef307bc320213b534af`. The statement's
Markdown explains how its unnormalized restriction, with right actions, corresponds to the
modulus-twisted convention of the sources.
