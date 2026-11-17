# Smoothness of a flat group spreads from one residue fibre

This helper module supports the proof of `Langlands.GroupScheme.TorusFibreSpreadingStatement`
(Conrad, *Reductive group schemes* (2014), Corollary 3.1.8). Conrad's argument starts by
noting that a flat, locally finitely presented group whose fibre at `s` is a torus is smooth
over a neighbourhood of `s`. The lemmas below prove that step. They are internal: they serve
that proof and are not themselves statements from the literature.

## Declarations

All declarations are in the namespace `Langlands.GroupScheme`. The three auxiliary lemmas
are in the sub-namespace `FibreSpreadingSmoothness`.

- `FibreSpreadingSmoothness.smooth_fiber_comp_openImmersion`: if `j : P ⟶ X` is an open
  immersion and the fibre `f.fiberToSpecResidueField y` of `f : X ⟶ Y` is smooth, then the
  fibre of `j ≫ f` at `y` is smooth.
- `FibreSpreadingSmoothness.smooth_fiber_of_isPullback`: in a pullback square
  `IsPullback fst snd f g`, if the fibre of `f` at `g w` is smooth, then the fibre of `snd`
  at `w` is smooth.
- `FibreSpreadingSmoothness.mem_smoothLocus_of_smooth_fiber`: let `f : X ⟶ Y` be flat and
  locally of finite presentation. If the fibre of `f` at `f x` is smooth over `κ(f x)`, then
  `x` lies in `f.smoothLocus`, so the stalk map at `x` is formally smooth. This is the
  scheme form of Stacks 00TF in the case where the whole fibre is smooth.
- `exists_smooth_nhd_of_smooth_residueFiber`: let `G` be a group scheme over `S` with
  `G.X.hom` flat and locally of finite presentation, and let `s : S`. If the residue fibre
  `RelativeIdentityComponent.residueFiber G s` is smooth over `Spec κ(s)`, then some open
  `U : S.Opens` contains `s` and satisfies `Smooth ((GroupScheme.baseChange U.ι).obj G).X.hom`.

## Proofs

**Open source restriction.** The fibre of `j ≫ f` at `y` is isomorphic, through
`pullbackRightPullbackFstIso`, to the base change of `j` followed by the fibre of `f`. The
first map is an open immersion and the second is smooth, so the composite is smooth.

**Base change.** Mathlib's `isPullback_fiberToSpecResidueField_of_isPullback` shows that the
fibre of `snd` at `w` is a pullback of the fibre of `f` at `g w`. Smoothness is stable under
base change (`MorphismProperty.of_isPullback`).

**Pointwise criterion.** Pick an affine open `U ∋ f x` and an affine open `V ∋ x` with
`V ≤ f⁻¹ U`. Let `y` be the prime of `Γ(Y, U)` corresponding to `f x`.

1. The chart `Spec Γ(X, V) ⟶ Spec Γ(Y, U)` is `Spec.map (f.appLE U V _)`. It factors as an
   open immersion `l` into `pullback f hU.fromSpec`, followed by `pullback.snd`.
2. By the two lemmas above, its fibre at `y` is smooth.
3. `Spec.fiberToSpecResidueFieldIso` identifies that fibre with
   `Spec (κ(y) ⊗ Γ(X, V)) ⟶ Spec κ(y)`. So `κ(y) ⊗ Γ(X, V)` is formally smooth over `κ(y)`.
4. The ring map `Γ(Y, U) → Γ(X, V)` is flat and of finite presentation
   (`Flat.flat_appLE`, `finitePresentation_appLE`). Mathlib's
   `Algebra.IsSmoothAt.of_formallySmooth_fiber` therefore makes `Γ(X, V)` smooth over
   `Γ(Y, U)` at the prime of `x`.
5. `formallySmooth_stalkMap_iff` turns this back into `x ∈ f.smoothLocus`.

**Spreading.** Let `e = η[G.X].left : S ⟶ G` be the identity section and `W` the smooth locus
of `G.X.hom`, an open subset of `G`. Then `W.ι ≫ G.X.hom` is smooth
(`preimage_smoothLocus_eq`, `smoothLocus_eq_top_iff`). Take `U = e⁻¹ W`.

- **`s ∈ U`.** `G.X.hom (e s) = s`, and the fibre of `G.X.hom` at `s` is the given residue
  fibre. The pointwise criterion therefore puts `e s` in `W`.
- **Every fibre over `U` is smooth.** For `t ∈ U`, the scheme
  `C = pullback W.ι (pullback.fst G.X.hom (S.fromSpecResidueField t))` is an open subscheme of
  the residue fibre `G_t`. It is smooth over `κ(t)` as a base change of `W.ι ≫ G.X.hom`. It is
  nonempty, because it contains a point above `e t`; `Scheme.Pullback.exists_preimage_pullback`
  supplies that point. The Library lemma `smooth_of_nonempty_smooth_open_chart` then shows that
  the field group `G_t` is smooth; its proof translates the chart by group points.
- **Conclusion.** The fibres of `G_U → U` are base changes of the fibres of `G` at points of
  `U`, so they are smooth. `G_U → U` is flat and locally of finite presentation, so Mathlib's
  `Smooth.of_smooth_fiberToSpecResidueField` makes it smooth.
