# Positive rational proportionality on compact open sets

`Langlands.HarmonicAnalysis.Distribution.HomogeneousIndicatorProportionalityStatement.{uG, uX}`
is an unproved proposition. The module defines this proposition as a `Prop`;
it supplies no proof of it.

## Statement and exact scope

For every `G : Type uG` with instances
`[Group G] [TopologicalSpace G] [NonarchimedeanGroup G]`
`[LocallyCompactSpace G] [SigmaCompactSpace G]`, and every `X : Type uX`
with instances
`[TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]`
`[MulAction G X] [ContinuousSMul G X] [MulAction.IsPretransitive G X]`,
let `D : Distribution X` satisfy
`∀ g : G, pushforward (Homeomorph.smul g) D = D`.

For any `U V : Set X`, any proofs `hU : IsClopen U`, `hcU : IsCompact U`,
`hV : IsClopen V`, and `hcV : IsCompact V`, if both `U` and `V` are
nonempty, then there exists `q : ℚ` such that `0 < q` and

```lean
D (Langlands.Hecke.TestFunction.characteristic hU hcU) =
  (q : ℂ) * D (Langlands.Hecke.TestFunction.characteristic hV hcV)
```

Here `NonarchimedeanGroup G` includes the topological group structure and
asserts that every neighbourhood of the identity contains an open subgroup.
`ContinuousSMul G X` means joint continuity of the action, and
`MulAction.IsPretransitive G X` means that any point can be carried to any
other by an element of `G`. Since `X` is Hausdorff, a compact open subset is
clopen, so compact clopen sets express the intended compact open sets.

The universes `uG` and `uX` are independent. The proposition does not assume
`Nonempty X` or choose an orbit base point. If `X` is empty, the nonemptiness
hypotheses on `U` and `V` cannot hold. The distribution may be zero, and the
conclusion does not require either displayed value to be nonzero or specify
a unique rational factor. There are no assumptions of a Haar measure,
unimodularity, or total disconnectedness, and no further action properties.

## Imported objects and conventions

The proposition uses the existing
`Langlands.HarmonicAnalysis.Distribution X`, namely
`Module.Dual ℂ (SchwartzBruhat X)`. Thus `D` is any complex linear functional
on the actual locally constant, compactly supported complex functions on
`X`, with no continuity condition on the functional.

For a homeomorphism `e`, the existing `pushforward e` is defined by
`(e_* D)(f) = D(f ∘ e)`. Consequently the invariance hypothesis says
`D(f ∘ (g •)) = D(f)` for every `g : G` and every test function `f`.
The existing `Langlands.Hecke.TestFunction.characteristic hU hcU` is the
actual test function equal to `1 : ℂ` on `U` and zero outside `U`.
The rational factor is positive in `ℚ` and is then cast to `ℂ` in the
equality. The statement imposes no order or positivity on complex values.

## Provenance

The original motivation is Bernstein and Zelevinsky, *Representations of
the group GL(n,F), where F is a non-Archimedean local field (survey)* (1976),
Example 6.12, printed/PDF p.56. The registered source is
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The example uses a positive invariant distribution on an orbit to control
the scalar by which an additional symmetry acts, under its stated
hypotheses on the orbit and the one-dimensional stalks.

The present positive rational comparison is an internal derived
strengthening of the indicator comparison in the published proof plan in
`Langlands/HarmonicAnalysis/Distribution/HomogeneousVanishingStatement.md`.
It is a separate target for the compact open orbit partition argument
described there. It is not a verbatim theorem of Bernstein–Zelevinsky and
does not identify invariant algebraic distributions with measures. The
separate proof remains to be supplied; no partition or proportionality
result is proved in this module.
