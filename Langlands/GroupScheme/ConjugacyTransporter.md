# The conjugacy transporter from a section to a point of a group scheme

Worker 1296.

This helper module studies the scheme of elements conjugating a section `x` of
a group scheme `G` to a point `w`, and shows that it is a translate of the
centralizer of `x` once one conjugating point is given. It is internal
infrastructure for the proof of
`Langlands.GroupScheme.RegularConjugateFiniteGaloisStatement`. The base `S` is
an arbitrary scheme in universe `u`; all objects live in `Over S`.

## A pullback-pasting lemma

`isPullback_pullback_comp`: in any category with pullbacks, for
`q : W' ⟶ W`, `w : W ⟶ Y` and `o : X ⟶ Y`, the pullback of `q ≫ w` and `o` is
the pullback of `q` and the projection `pullback w o ⟶ W`. So base change of the
transporter along `q` is again a transporter. The proof is the two-square
pasting lemma `IsPullback.of_right`.

## The transporter

- `conjugationOrbitMap G x : G.X ⟶ G.X` is the orbit map `h ↦ h x h⁻¹`,
  written with the point group law of the identity point `𝟙 G.X`.
- `comp_conj` and `comp_conjugationOrbitMap`: restricting a conjugate
  `a * x * a⁻¹` along a morphism of tests `f` gives the conjugate of
  `f ≫ a`; and `h ≫ conjugationOrbitMap G x = h * x * h⁻¹` for any point `h`.

For a point `w : W ⟶ G.X`, the transporter from `x` to `w` is the pullback
`pullback w (conjugationOrbitMap G x)` in `Over S`. Its points on a test `V`
are pairs `(v, h)` of a point `v : V ⟶ W` and a point `h` of `G` with
`h * x * h⁻¹ = v ≫ w`.

## The transporter is a translate of the centralizer

Fix a closed representative `i : T ⟶ G` of the all-test centralizer of `x`
(`hi : (G.pointCentralizer x).IsRepresentedBy i`) and one point
`g : W ⟶ G.X` with `g * x * g⁻¹ = w` (`hg`).

- `transporter_mem`: on the transporter, `(fst ≫ g)⁻¹ * snd` centralizes `x`.
  Both `fst ≫ g` and `snd` conjugate `x` to the same point, by
  `pullback.condition` and `hg`.
- `transporterToCentralizer` is the point of `T` corresponding to it under
  `hi.pointsEquiv`, and `transporterToCentralizer_comp` records its image in
  `G`.
- `transporterOfCentralizer : W ⊗ T.X ⟶ pullback w (conjugationOrbitMap G x)`
  sends `(v, t)` to `(v, (v ≫ g) * i(t))`. A point of `T` centralizes `x`,
  so `(v ≫ g) * i(t)` still conjugates `x` to `v ≫ w`.
- `transporterIso hi g hg : pullback w (conjugationOrbitMap G x) ≅ W ⊗ T.X`
  has these two maps as its components. The two composites are identities by
  the universal properties of the pullback and the product. The second also
  cancels the monomorphism `i.hom.hom`.
- `transporterIso_hom_fst`: the isomorphism lies over `W`, that is, followed by
  the first projection it is the transporter's projection `pullback.fst`.

## Smoothness

`smooth_transporter_fst_left`: if `T.X.hom` is smooth, the projection from the
transporter to `W` is smooth on underlying schemes. By `transporterIso_hom_fst`
it is an isomorphism followed by the first projection `W ⊗ T.X ⟶ W`. That
projection is the base change of `T.X.hom` along `W.hom`, so it is smooth, and
isomorphisms are smooth.
