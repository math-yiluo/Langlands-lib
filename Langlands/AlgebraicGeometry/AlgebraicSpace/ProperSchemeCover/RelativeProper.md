# Represented properness of the weak Chow cover

For weak Chow data `D : ChowData X` (module `Construction`), this module proves that
the cover `φ : h_U → X` is relatively proper (`relative_isProper_φ`): for every scheme
`T` over `S` and every `g : h_T → X`, the projection `U ×_X T ⟶ T` is a proper morphism
of schemes. In the language of Stacks 089I, `U → X` is representable by proper morphisms.

## Results

- `isPullback_congr_right`: a pullback square stays one after rewriting its right edge
  by an equal morphism. This is a small categorical helper.
- `isSeparated_snd`: `U ×_X T ⟶ T` is separated and locally of finite type. It factors as
  the closed immersion `U ×_X T ⟶ U ×_S T` (`isClosedImmersion_spacePullbackLift`, which
  uses that `X` is separated) followed by the projection `U ×_S T ⟶ T`. That projection
  is a base change of the separated, finite type `U → S`.
- `descent_snd`: the projection `W ×_X T ⟶ T` is surjective, flat and quasi-compact.
  It is étale and surjective as a base change of the chart (`etale_spacePullbackSnd`,
  `surjective_spacePullbackSnd`). It is quasi-compact as the closed immersion
  `W ×_X T ⟶ W ×_S T` followed by the projection to `T`, which is a base change of the
  quasi-compact `W → S`.
- `universallyClosed_snd`: `v : V = U ×_X T ⟶ T` is universally closed. Put
  `T' = W ×_X T` with projections `f : T' ⟶ T` and `f' : T' ⟶ W`, and
  `V' = U ×_X T'`, the space pullback of `φ` along `h_f ≫ g`. Two squares of schemes
  over `S` are pullbacks:
  - `V' ⟶ V` over `f : T' ⟶ T`. In presheaves, the square for `V'` over `X` is the
    pasting of this square with the square for `V` (`IsPullback.of_right`).
  - `V' ⟶ Q = U ×_X W` over `f' : T' ⟶ W`. The same argument applies, using
    `h_f ≫ g = h_{f'} ≫ π` (`spacePullback_w`).

  Both squares come from `schemeYoneda S` and are pulled back to `Over S`
  (`IsPullback.of_map_of_faithful`), then mapped to schemes by `Over.forget S`. By the
  second square, `V' ⟶ T'` is a base change of the proper `q₂ : Q ⟶ W` (`isProper_q₂`,
  module `Closedness`), so it is universally closed. By the first square, `V' ⟶ T'` is
  the base change of `v` along `f`. Universal closedness descends along surjective,
  flat, quasi-compact morphisms (Mathlib's fpqc descent,
  `MorphismProperty.of_isPullback_of_descendsAlong`). Hence `v` is universally closed.
- `relative_isProper_φ`: by `MorphismProperty.relative_of_snd`, applied to the
  representability of morphisms from schemes into `X`, it is enough to show that every
  `U ×_X T ⟶ T` is proper. This is the combination of the two previous results.
