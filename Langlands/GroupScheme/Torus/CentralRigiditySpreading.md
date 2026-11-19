# Spreading the equality of two homomorphisms from `Spec 𝒪_{S,s}`

Worker 738.

These are internal helper lemmas for the proof of
`MultiplicativeTypeCentralRigidityStatement`. They implement the first step of the proof
of case a) of SGA 3, Exposé IX, Théorème 5.1, in the registered Gille–Polo 2009 recomposed
edition (`sga3-expose-ix-gille-polo-2009`), p.48 (PDF page 18). That step replaces `u` and
`v` by their kernel `K = Ker(u, v)`, the inverse image of the diagonal of `G` under
`(u, v) : H → G ×_S G`. It notes that `K → H` is of finite presentation and reduces the
theorem to the local scheme `Spec 𝒪_{S,s}` using EGA IV₃ 8.8.2.4. In this module the
spreading step is the published statement
`Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreadingStatement`
(EGA IV₃ 8.8.2 (i)). It enters `exists_open_baseChange_eq` as an explicit hypothesis. The
module proves no part of that statement.

All declarations are in the namespace `Langlands.GroupScheme.CentralRigiditySpreading`.
Throughout, `H` and `G` are group schemes over a scheme `S`. For a homomorphism `w : H ⟶ G`,
`w.hom.hom.left : H.X.left ⟶ G.X.left` is the underlying morphism of schemes.

## Base change of homomorphisms

For `f : T ⟶ S`, `(GroupScheme.baseChange f).map w` has underlying morphism
`H ×_S T ⟶ G ×_S T` induced by `w`. The lemmas `baseChange_map_left_fst` and
`baseChange_map_left_snd` state that it commutes with the first projections (to `H` and
`G`, via `w`) and with the second projections to `T`. Both are `pullback.lift_fst` and
`pullback.lift_snd`.

`baseChange_map_eq_iff f u v` states that the base changes of `u` and `v` along `f` are
equal if and only if `pullback.fst ≫ u = pullback.fst ≫ v` as morphisms `H ×_S T ⟶ G`.
The forward direction rewrites with `baseChange_map_left_fst`. For the converse, two
homomorphisms of group schemes are equal when their underlying morphisms of schemes are
equal. Those morphisms land in a pullback, so it is enough to compare both projections,
which the two previous lemmas do.

## The kernel of a pair of homomorphisms

- `eqLift u v : H.X.left ⟶ G.X.left ×_S G.X.left` is the morphism `(u, v)`.
- `eqIncl u v` is the first projection of the pullback of the diagonal
  `pullback.diagonal G.X.hom` along `eqLift u v`. This is the inclusion `K ⟶ H` of
  the kernel of SGA 3.
- `isImmersion_eqIncl` (an instance): `eqIncl u v` is an immersion. The diagonal of a
  morphism of schemes is an immersion (Mathlib), and immersions are stable under base
  change.
- `locallyOfFinitePresentation_eqIncl`: if `H.X.left` is locally noetherian, then
  `eqIncl u v` is locally of finite presentation. An immersion is locally of finite type,
  and over a locally noetherian source "locally of finite type" and "locally of finite
  presentation" coincide (Mathlib's
  `LocallyOfFinitePresentation.iff_locallyOfFiniteType`). This is the finiteness used by
  SGA 3 (the source cites EGA I 6.3.5).
- `exists_factor_iff u v t`: a morphism `t : T ⟶ H.X.left` factors through `eqIncl u v`
  if and only if `t ≫ u = t ≫ v`. If `t = y ≫ eqIncl u v`, the pullback square and the
  two projections of the diagonal give the equality. Conversely, if `t ≫ u = t ≫ v`, then
  `t` lifts to the pullback, with second component `t ≫ u` into `G`. The lift is
  compatible with the diagonal by `pullback.hom_ext`.

## Spreading

`exists_open_baseChange_eq hP4 u v s hqc hqs hK h` takes:

- `hP4 : SpecStalkFactorizationSpreadingStatement`;
- a point `s : S`;
- `QuasiCompact H.X.hom` and `QuasiSeparated H.X.hom`;
- `LocallyOfFinitePresentation (eqIncl u v)`;
- the equality of the base changes of `u` and `v` along `S.fromSpecStalk s`.

It concludes that there is an open `U : S.Opens` with `s ∈ U` such that the base changes
of `u` and `v` along `U.ι` are equal.

Proof: by `baseChange_map_eq_iff` and `exists_factor_iff`, the hypothesis says that the
projection `H ×_S Spec 𝒪_{S,s} ⟶ H` factors through `eqIncl u v`. The spreading statement,
applied to `p = H.X.hom` and `k = eqIncl u v`, gives an open `U ∋ s` over which the
projection `H ×_S U ⟶ H` factors through `eqIncl u v`. The same two lemmas turn this back
into equality of the base changes along `U.ι`.

This module adds no axioms.
