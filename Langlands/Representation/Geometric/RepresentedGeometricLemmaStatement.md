# The geometric lemma for represented parabolics (Renard VI.5.1)

Lean module: `Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

## Source

Renard, *Représentations des groupes réductifs p-adiques* (2026 version), VI.5.1
"Le lemme géométrique": the theorem on printed p.161 (PDF p.167), and its more precise
reformulation with the functors `Φ_Z` on printed p.162 (PDF p.168). The proof starts
on PDF p.168 and continues over the following pages. The representative set `W_{Q,P}` comes from V.4.7 (PDF pp.127–128).

Renard's reformulation reads as follows. Let `P = MN` and `Q = LU` be parabolic subgroups
and `X = P\G`. Then `Q` has finitely many orbits `Z_1, …, Z_k` on `X`, numbered so that
each `Z_1 ∪ … ∪ Z_j` is open. For an orbit `Z`, pick a point `Pz ∈ Z` with
`z ∈ W_{Q,P}` and put `ι = Int(z)`, `M' = M ∩ ι(L)`, `L' = L ∩ ι⁻¹(M)`,
`N' = M ∩ ι(U)` and `U' = L ∩ ι⁻¹(N)`. Then `P' = M'N'` is a parabolic subgroup of `M`,
`Q' = L'U'` is a parabolic subgroup of `L`, and `M' = ι(L')`. Put
`Φ_Z = i^L_{Q'} ∘ ι ∘ r^M_{P'}`, where `ι` is the forgetful functor along
`ι : L' → M'`. Then the functor `F = r^G_Q ∘ i^G_P : M(M) → M(L)` has a filtration by
subfunctors `0 = F_0 ⊂ F_1 ⊂ … ⊂ F_k = F` with `F_i / F_{i-1} ≃ Φ_{Z_i}`. Here `i` and
`r` are Renard's normalized induction and normalized Jacquet functors.

## Declarations

- `leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ` is the
  composite `F = r^G_Q ∘ i^G_P`. It is `leviInductionFunctor` along `(P, M, N)`, then
  `leviJacquetFunctor` along `(Q, L, U)`, then `SmoothRep.toRep`. It goes from
  `SmoothRep.{0, u, v} ℂ M(F)` to `Rep.{max u v} ℂ L(F)`. The induction functor raises
  the carrier universe to `max u v` and the Jacquet functor keeps it. The final
  `SmoothRep.toRep` is there because `IsGluedFrom` is stated for functors valued in
  `Rep`.

- `GeometricLemmaIntersectionDatum … z` bundles the intersection data for one
  representative `z ∈ G(F)`. It contains:
  - group schemes `P', M', N'` with maps `p' : P' ⟶ M`, `l' : M' ⟶ P'` and `r' : N' ⟶ P'`,
    the proofs that `p'` is parabolic, that `l'` is a rational Levi subgroup and that `r'`
    is the geometric unipotent radical, and `IsIso (subgroupMultiplication l' r')`. In
    other words, `(P', M', N')` is a represented parabolic of `M` of exactly the kind used
    by `leviJacquetFunctor`.
  - the same data `Q', L', U'` with `q' : Q' ⟶ L`, `lQ'` and `rQ'`, a represented
    parabolic of `L`.
  - six equalities of subgroup functors of `G` (`SubgroupFunctor.range`). Writing
    `ι = Int(z)` for `G.innerIso z`, which acts by `x ↦ z x z⁻¹` on points, they say
    `P' = M ∩ ι(Q)`, `M' = M ∩ ι(L)`, `N' = M ∩ ι(U)`, `Q' = L ∩ ι⁻¹(P)`,
    `L' = L ∩ ι⁻¹(M)` and `U' = L ∩ ι⁻¹(N)`, all as subgroup functors of `G`.
    `ι⁻¹` is written as `G.innerIso z⁻¹`. These are Renard's definitions, together with
    `P' = M ∩ ι(Q)` and `Q' = L ∩ ι⁻¹(P)` from Remark 1.
  - an isomorphism `φ : L' ≅ M'` of group schemes, together with `φ_comp`: `φ` followed
    by the inclusion `M' → G` equals the inclusion `L' → G` followed by `ι`. So `φ` is
    Renard's `ι : L' → M'`, and Renard's `M' = ι(L')` is part of this data.
  - an isomorphism of topological groups `e : L'(F) ≃ₜ* M'(F)` for the Levi point
    topologies (`leviPointTopology`), with `e_apply`: `e` is the map of `φ` on rational
    points.
  - a commutative group scheme `torus` with a map `t : torus.toGrp ⟶ M'`, and
    `isMaximalSplitTorus`: `t` followed by the inclusion `M' → G` is a maximal split
    torus of `G` (`IsMaximalSplitTorus`, from
    `Langlands.GroupScheme.Rational.SplitTorus`). So `M' = M ∩ ι(L)` contains a maximal
    split torus of `G`.

  The structure only bundles data. It says nothing about representations.

- `GeometricLemmaIntersectionDatum.pieceFunctor D` is `Φ_Z = i^L_{Q'} ∘ ι ∘ r^M_{P'}`. It
  is `leviJacquetFunctor` along `(P', M', N')`, then `SmoothRep.pullbackFunctor D.e`
  (restriction along `e : L'(F) ≃ M'(F)`, Renard's forgetful functor `ι`), then
  `leviInductionFunctor` along `(Q', L', U')`, then `SmoothRep.toRep`. It has the same
  source and target categories as `leviJacquetInductionFunctor`.

- `RepresentedGeometricLemmaStatement : Prop` quantifies over every nonarchimedean
  local field `k`, every connected reductive `G` over `k` whose point group is locally
  compact and nonarchimedean (as in `LeviInductionNormalizedTemperedStatement`), and
  every two represented parabolics `(P, M, N)` and `(Q, L, U)` of `G`. It asserts that
  there exist
  - a number `m` and an equivalence `c : Fin m ≃ DoubleCoset.Quotient P(F) Q(F)`, so
    the actual double coset space `P(F) \ G(F) / Q(F)` is finite with `m` elements;
  - representatives `z : Fin m → G(F)` with `DoubleCoset.mk P(F) Q(F) (z i) = c i`;
  - intersection data `D i : GeometricLemmaIntersectionDatum … (z i)` for each `i`;

  such that `IsGluedFrom (leviJacquetInductionFunctor …) (fun i => (D i).pieceFunctor)`.
  That is, for some permutation of `Fin m` there is a natural finite filtration of `F`
  by actual subfunctors whose successive quotients are naturally isomorphic to the
  pieces in the permuted order (`Langlands.Representation.Filtration.Definitions`).

## Relation to the source

- **Arbitrary parabolics.** Renard's theorem is already stated for arbitrary parabolic
  subgroups `P = MN` and `Q = LU`. V.4.7 begins "On suppose maintenant que `P` et `Q`
  sont des sous-groupes paraboliques quelconques". What depends on standard parabolics is
  his choice of representatives. VI.5 fixes a minimal parabolic `P_∅ = M_∅N_∅`. V.4.6
  builds the set `W_{L,M}` for standard `P` and `Q`, and V.4.7 conjugates `P`, `Q` to
  standard `P_1 = g·P`, `Q_1 = h·Q` with `M_1 = g·M` and `L_1 = h·L`, and sets
  `W_{Q,P} = g⁻¹ W_{Q_1,P_1} h`. The Lean statement has no `P_∅`, no standard
  parabolics and no `W_{Q,P}`. It quantifies over all represented parabolics `(P, M, N)`
  and `(Q, L, U)` with exactly the hypotheses of `leviInductionFunctor` and
  `leviJacquetFunctor`. It assumes no standardness and no supplied minimal parabolic.
- **Existential representatives.** Renard uses the specific representatives
  `z ∈ W_{Q,P}`. Here the representatives `z i` are only asserted to exist, together with
  the properties of `W_{Q,P}` that VI.5.1 uses. Renard's Remark 1 says that `W_{Q,P}` is
  a set of representatives of `P\G/Q`, and the `Q`-orbit of `Pz` in `X = P\G` is
  `P\PzQ`. In the Lean statement, the equivalence `c` and the condition
  `DoubleCoset.mk (z i) = c i` say that the `z i` meet every double coset exactly once,
  so the pieces are indexed by all the orbits `Z_i`. The intersection data `D i` record
  the remaining properties from V.4.7, as conclusions:
  - `M ∩ z·Q` is a parabolic of `M` with Levi `M ∩ z·L` and radical `M ∩ z·U`;
  - `z⁻¹·P ∩ L` is a parabolic of `L` with Levi `z⁻¹·M ∩ L` and radical `z⁻¹·N ∩ L`.

  V.4.7 also proves four product decompositions, such as
  `P ∩ z·Q = (P ∩ z·L)(P ∩ z·U)`. Renard's proof uses such decompositions (for example
  `P̂ ∩ U = (M̂ ∩ U)(N̂ ∩ U)` on PDF p.172), but they are not part of this statement.
- **Maximal split torus.** The fields `torus`, `t` and `isMaximalSplitTorus` say that
  `M ∩ z·L` contains a maximal split torus of `G`. Renard does not state this, but it
  holds for his representatives. In V.4.7 one has `z = g⁻¹wh`, where `w` represents an
  element of `W_G = N_G(A_∅)/M_∅` and so normalizes `A_∅`. Hence
  `M ∩ z·L = g⁻¹·(M_1 ∩ w·L_1)` contains `g⁻¹·A_∅`, since the standard Levi subgroups
  `M_1` and `L_1` contain `M_∅ ⊇ A_∅`. This is a further conclusion and makes the
  statement stronger. It was added at the request of Worker 1585, whose proof of
  VII.2.2 needs the torus to obtain split components of `L'` and `M'`.
- **Filtration order.** Renard numbers the orbits so that the unions
  `Y_j = Z_1 ∪ … ∪ Z_j` are open, and the filtration then has the pieces in that order.
  The Lean statement does not keep this numbering. `IsGluedFrom` asserts a filtration
  for some permutation of the enumeration `c`, and does not say which one.
- **Scheme-level identities.** Renard's `M ∩ ι(L)` and so on are intersections of
  algebraic subgroups. The equalities here are equalities of subgroup functors of `G`,
  that is, on points with values in every `k`-algebra, not just on `F`-points.
- **Coefficients and target category.** Renard's `M(M)` and `M(L)` are categories of
  smooth complex representations. Here the source is `SmoothRep ℂ M(F)`. The composite
  and the pieces are followed by `SmoothRep.toRep` and valued in all complex
  representations of `L(F)`, because `IsGluedFrom` is stated for functors valued in
  `Rep`. The filtration subfunctors are therefore subrepresentations in `Rep`. (Every
  subrepresentation of a smooth representation is smooth, but the statement does not use
  this.)
- **Normalization.** Both sides use the normalized functors
  `leviInductionFunctor` (normalized parabolic induction) and `leviJacquetFunctor`
  (normalized Jacquet functor), as in Renard. There is no modulus twist on the pieces.
- **Universes.** The group universe is `u` (that of `k`), and the source representations
  have carriers in `Type v`. The composite and every piece are valued in
  `Rep.{max u v} ℂ L(F)`, because each contains one induction functor.
- **Hypotheses on `G(F)`.** The instances `LocallyCompactSpace` and
  `NonarchimedeanGroup` on `G(F)` with the point topology are binders, exactly as in
  `LeviInductionNormalizedTemperedStatement`. For Renard, `G` is the locally compact,
  totally disconnected group of `F`-points, so these properties are part of his setting.
  The Lean statement takes them as hypotheses.

## Provenance

The statement is derived from Renard VI.5.1. The design choices — enumerating the
representatives through `Fin m ≃ DoubleCoset.Quotient`, making every intersection datum
(schemes, maps, parabolic/Levi/radical proofs and the conjugation compatibility of the
same `z`) a conclusion, and valuing both composites in the same `Rep` category — follow
advice from Worker 14. Worker 1585 wrote the Lean statement for the VII.2.2 proof task
`f83123b9-ff38-4210-9ad7-4f119a13d1ac`, which needs the filtration form of the lemma for
arbitrary represented parabolics, and asked for the maximal split torus fields. Worker 837
checked the statement against Renard and the Library definitions, added those fields, and
wrote the comparison with the source above.
