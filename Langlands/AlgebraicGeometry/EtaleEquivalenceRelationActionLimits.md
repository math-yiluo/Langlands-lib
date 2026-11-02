# Target base change limits for action descent

Author: Worker 706.

This internal helper uses the over-category pullback functor and Mathlib's
proved finite-presentation factorization theorem. Its intended application is
the action descent step in Stacks Project Proposition 70.8.1, Tag 07SU,
registered as `stacks-noetherian-approximation-2026-11-01`. It does not assert
existence of an approximation system.

In `Action.TargetLimit`, `D` is a diagram of schemes over `S`, represented by
the natural transformation `t`, and `q : T → S` is fixed. `diagram` has
terms `D_i ×[S] T`. `comparison` projects to `T`; `projection` projects
to `D`. For a cone `c` with structural map `p : c.pt → S`, whose legs
commute with `t`, `cone` is its base change along `q`.
`isLimitCone` proves that this cone is limiting when `c` is limiting and
the indexing category is cofiltered: the pullback functor is a right
adjoint and the forgetful functor from an over category preserves connected
limits.

For any supplied square exhibiting `X` as the pullback of `p` and `q`,
`coneOfPullback` replaces the canonical pullback point by `X` using its
canonical isomorphism. The two projection formulas identify its legs with
the given map to `c.pt` followed by the original cone legs, and the given
map to `T`, respectively. `isLimitConeOfPullback` transports the preceding
limit proof through this isomorphism.

If `S`, `T` and all terms of `D` are affine, the terms of `diagram` are
affine and its transition maps are affine. `exists_map_at_level` then
factors a supplied map `a : X → Q`, over `S`, through a level of this
base changed diagram, provided `Q → S` is locally of finite presentation.
It applies `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
to the constructed limiting cone. Affineness supplies quasi-compactness,
quasi-separatedness and affine transition maps. The conclusion retains
both the factorization equality and its structural equation over `S`.

The action specialization fixes a cartesian relation morphism `h : E → F`
and an object pullback square `P → Q` over `E.U → F.U`. The object diagram
`D` has a supplied cone with point `E.U`, legs `v`, structure maps `t`
to `F.U`, and the compatibility equations `v_i ≫ t_i = f`.
`arrowCone` applies the preceding construction with fixed factor
`F.R ×[F.U] Q` and structural map given by its arrow target. The already
proved target square for action domains, flipped to put `E.U` first,
identifies this cone's point with the actual domain `E.R ×[E.U] P`.
`arrowCone_π_fst` identifies each leg's varying-object projection with
the upper arrow target followed by `v_i`. `arrowCone_π_snd` identifies
its fixed-domain projection with `arrowMap h`. `isLimitArrowCone`
proves that this is a limit when the supplied object cone is a limit.

For an actual action `A` on `P`, `exists_target_factor_at_level`
assumes that `F.U`, the fixed lower action domain, and all terms of `D`
are affine, and that `q : Q → F.U` is locally of finite presentation.
It applies the general factorization theorem to `A.map ≫ k`.
The action's target equation and the supplied object pullback equation
show that this composite lies over the outer arrow target. The result
is a factor from `D_i ×[F.U] (F.R ×[F.U] Q)` to `Q`, together with its
base equation and its equality with `A.map ≫ k` after the limit leg.
The source of this factor still includes the varying object `D_i`.

Finally, `targetFactorMap` works with one supplied cartesian relation
level and one supplied object pullback. It takes a map from that target
base change to `Q`, satisfying the structural equation returned above.
The canonical flipped target-domain isomorphism first identifies the
level's actual action domain with the base change. The object pullback
then lifts the factor and the upper arrow target to a prospective map
into the upper object `P`. `targetFactorMap_comparison` and
`targetFactorMap_over` give its two projection equations. No unit or
associativity law for this prospective map is asserted here; their
eventual descent uses the separate ActionDescent interface.
