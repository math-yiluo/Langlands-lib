# Etale-local orbits for fppf quotients by smooth group actions

Module `Langlands.AlgebraicGeometry.Picard.QuotientActionLocality`, namespace
`Langlands.AlgebraicGeometry.Picard.QuotientActionLocality`.

This is an internal, derived helper for the proof of
`Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement`. It isolates the
torsor argument that turns fppf-local statements about a presheaf with a group action
into etale-local ones. Everything is formulated on the full slice `Over S` of an arbitrary
scheme `S : Scheme.{u}`, with presheaves valued in `Type (u + 1)`, the slice fppf topology
`fppfTopology S = Scheme.fppfTopology.over S` and the slice etale topology
`Scheme.etaleTopology.over S`. No test scheme is excluded.

## The structure `QuotientAction S`

A `QuotientAction S` consists of

- presheaves `P E : (Over S)ᵒᵖ ⥤ Type (u + 1)` and a natural transformation `π : P ⟶ E`;
- group schemes `H Q : GroupScheme S` and a homomorphism `q : H ⟶ Q`;
- an action `act h x` of every point `h : T ⟶ H.X` on every section `x : P(T)`, with
  `act 1 x = x`, `act (h * h') x = act h (act h' x)` and naturality
  `P.map a (act h x) = act (a ≫ h) (P.map a x)`;
- invariance `π (act h x) = π x`;
- the stabilizer condition `act h x = x ↔ h ≫ q = 1` for every section `x`: the kernel
  of `q` is exactly the stabilizer of every section;
- fppf-local transitivity on fibres (`locally_orbit`): if `π x = π y`, some fppf
  covering sieve of `T` consists of maps `g` along which `P.map g x = act h (P.map g y)`
  for some point `h` of `H`.

The intended example has `P` the presheaf of classes of line bundles rigidified along a
finite subscheme, `E` the fppf Picard sheaf, `H` the units of the subscheme, and `Q` the
quotient of `H` by the global units.

## The `Q`-valued difference

`IsDelta x y d` says that `d : T ⟶ Q.X` is the difference of `x` and `y`: whenever
`P.map g x = act h (P.map g y)`, then `g ≫ d = h ≫ q`. Because the slice fppf topology
is subcanonical (`yoneda_isSheaf`), local values glue:

- `exists_isDelta`: if `π x = π y`, a difference exists. The local values `h ≫ q` on the
  covering sieve of `locally_orbit` form a compatible family, by the stabilizer condition
  (`comp_q_eq_of_act_eq`), and the amalgamation is the difference.
- `IsDelta.unique`, `IsDelta.comp` (pullback), `IsDelta.comp'`, `isDelta_self`,
  `isDelta_act_self`, `isDelta_self_act`, `IsDelta.act`
  (`δ(act h x, act h' y) = q(h) δ(x, y) q(h')⁻¹`) and `IsDelta.mul`
  (`δ(x, z) = δ(x, y) δ(y, z)`).
- `IsDelta.eq_of_one`: if `P` is fppf separated, a trivial difference forces `x = y`.

## Etale-local transitivity

`etale_locally_orbit` assumes that `P` is fppf separated and that the underlying scheme
map of `q` is smooth and surjective. If `π x = π y`, then some etale covering sieve of `T`
consists of maps along which `x` is a translate of `y`. The proof base-changes `q` along
the difference `δ(x, y) : T ⟶ Q.X`. The resulting smooth surjection to `T.left` has a
section after one etale surjection, by the published
`smoothSurjectiveEtaleLocalSections`; this section is a point `h` of `H` with
`q(h) = δ(x, y)`, so the difference of `x` and `act h y` is trivial. The published
`generate_singleton_mem_etaleTopology` makes the single etale surjection a cover.

## A separation criterion

`isSeparated_fppf_of_zariski_of_affine` proves that a presheaf `P` on `Over S` with values in
`Type (u + 1)` is separated for the slice fppf topology as soon as it is separated for the
slice Zariski topology and for every single morphism
`Over.homMk (Spec.map φ) : Over.mk (Spec.map φ ≫ s) ⟶ Over.mk s` with `Spec.map φ` flat and
surjective. For sections `x y` over `T`, the subpresheaf `agreement P x y` of the points of `T`
consists of the maps `g` with `P.map g x = P.map g y`. The two hypotheses, together with
subcanonicity of the slice Zariski and fpqc topologies
(`generate_singleton_mem_fpqcTopology` makes a single affine flat surjection an fpqc cover),
show that it satisfies the hypotheses of the published criterion
`OverFppfSheaf.isSheaf_fppfTopology_over`. If `x` and `y` agree on an fppf covering sieve,
the inclusions of that sieve form a compatible family of the agreement sheaf; its
amalgamation is a point of `T` which equals the identity by subcanonicity, so `x = y`.

## Etale-local surjectivity

The final theorem `isLocallySurjective_etale` concerns, besides the data of `D`, a presheaf
`F` and a natural transformation `toE : F ⟶ E`. It assumes:

- `P` and `E` are separated for the slice fppf topology;
- descent data in `P` descend to `F` along fppf affine morphisms (`hdesc`): for every
  `m : U ⟶ V` whose underlying scheme map is affine, flat, surjective and locally of finite
  presentation, and every `p : P(U)` whose two pullbacks agree on every pair of maps with equal
  composite with `m`, some `y : F(V)` satisfies `E.map m (toE y) = π p`;
- `π` is locally surjective for the slice fppf topology;
- `Q` is smooth and affine over `S`, and the scheme map of `q` is flat, surjective,
  locally of finite presentation and affine.

It concludes that `toE` is locally surjective for the slice etale topology. In the intended
application `F` is the presheaf of ordinary line-bundle classes and `toE` is the unit of fppf
sheafification; only the class of a descended line bundle is needed, not a descended
rigidification. The proof has three steps.

1. `exists_affine_chart` uses the published `LocallyQuasiFiniteDescent.exists_affineChart`
   to find, through any point `t` of `T`, a member of a given fppf covering sieve of the form
   `r ≫ incl`, where `incl : W ⟶ T` is a basic open of an affine open containing `t`, `W`
   and `U` are affine, and `r : U ⟶ W` is flat, surjective and locally of finite
   presentation. Surjectivity onto the basic open uses openness of flat morphisms locally
   of finite presentation.
2. `exists_etale_lift` treats such a chart, a section `sW` of `E` over `W` and a lift
   `p : P(U)` of its restriction. The two pullbacks of `p` to any test with equal images in
   `W` have a difference; reading these differences in the base change of `Q` to `W.left`
   (`baseChangePointsEquiv`) gives an actual `Cocycle` (`cocycle`, `cocycle_spec`). The
   published `CocycleTorsor` construction produces a torsor over `W.left` which is smooth
   and surjective (`CocycleTorsor.smooth_hom`, `CocycleTorsor.surjective_hom`); it has a
   section after an etale surjection `e : V ⟶ W`. Over `U ×_W V` the torsor difference
   between the section and the torsor point (`torsorDiff`) is a point `f` of `Q` which
   trivializes the pulled-back cocycle. After the further flat base change along `q`, `f`
   lifts to a point `k` of `H`. Translating the pulled-back `p` by `k⁻¹` gives a section
   whose two pullbacks agree; `hdesc` gives `y : F(V)` whose image agrees with it after the
   fppf affine base change, and separatedness of `E` gives `toE y = E.map e sW`.
3. `etale_mem_of_points` shows that a sieve containing, through every point, an etale
   member is an etale covering sieve.

## Provenance

Internal. The classical background is that a torsor under a smooth affine group scheme is
representable by a smooth affine scheme and therefore has sections etale locally. In this
Library that background is supplied by the published theorems used above
(`CocycleTorsor`, `smoothSurjectiveEtaleLocalSections`); no external source is cited by this
module. The formulation through the stabilizer condition and the `Q`-valued difference is
internal to this project. The implemented proof uses only those published Library results
and Mathlib's sheaf, descent and morphism-property API. This module proves no statement
about line bundles or Picard functors.
