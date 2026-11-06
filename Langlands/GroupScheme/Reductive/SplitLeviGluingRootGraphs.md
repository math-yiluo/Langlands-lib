# Root subgroups of the local Levis inside the graph subgroup

Authors: Worker 712 and Worker 1444 (interface and design).

This is a derived internal support module for the graph route to the
common-torus Levi gluing statement `SplitCommonTorusLeviGluingStatement`. It
combines Worker 1444's graph subgroup (`SplitLeviGluingGraph`) with the local
Levi comparisons and their root comparisons (`SplitLeviGluingLocal`). It does
not prove the gluing statement. It makes no density claim and does not claim
that either projection is invertible.

## Setting

Work over a field `k : Type u` with group schemes `G₁`, `G₂` over `Spec k`, a
commutative group scheme `T`, homomorphisms `i₁ : T.toGrp ⟶ G₁` and
`i₂ : T.toGrp ⟶ G₂`, an index type `I : Type v`, cocharacters
`ν : I → cocharacterLattice T`, and a family
`C : ∀ j, LocalComparison i₁ i₂ (ν j)`. So `C j` holds actual closed
representatives `(C j).left ⟶ G₁` and `(C j).right ⟶ G₂` of the dynamic
centralizers of `ν j` composed with `i₁` and `i₂`. It also holds their torus
factors and an isomorphism `(C j).iso : (C j).left ≅ (C j).right` over the
common torus.

## Declarations

- `localGroups C`, `localFirst C`, `localSecond C`: the family of local Levis
  `(C j).left`, their first inclusions `(C j).leftInclusion`, and the maps
  `(C j).iso.hom ≫ (C j).rightInclusion` into `G₂`. These are the data `A`,
  `a₁`, `a₂` of `GraphEnvelope`.
- `LocalGraphEnvelope C`: the type `GraphEnvelope` of graph subgroups generated
  by the graphs of the local Levi isomorphisms of `C` and by the common torus,
  that is, by the maps `lift (a₁ j) (a₂ j)` and `lift i₁ i₂` into `G₁ ⊗ G₂`.
- `localGraphEnvelope C hT`: one such graph subgroup, built with the
  published `graphEnvelope`. It requires `G₁` smooth, affine and connected, `G₂`
  smooth and affine, and `hT : IsSplitTorus T.toGrp`. The split torus is smooth,
  affine and connected (`IsSplitTorus.smooth`, `.isAffineHom`,
  `.connectedSpace`). The local Levis are too, by the instances on
  `LocalComparison`.
- `canonicalLocalComparisons i₁ i₂ ν hlocal hν`: the family
  `j ↦ localComparison i₁ i₂ hlocal (ν j) (hν j)`. It is built from the local
  gluing premise `hlocal : RankOneLeviHypothesis i₁ i₂` and
  `hν : ∀ j, IsRankOneDirection i₁ (ν j)`.

For `D : LocalGraphEnvelope C`, an index `j`, a character `α` and
`R : (C j).RootComparison α` (closed representatives `R.left ⟶ (C j).left` and
`R.right ⟶ (C j).right` of the two local intrinsic root subgroups of `α`, with
an isomorphism `R.iso` compatible with `(C j).iso`):

- `D.leftTorus_localLift j`: `(C j).leftTorus ≫ D.localLift j = D.torusLift`.
- `D.rootLift j R : R.left ⟶ D.group` is `R.leftInclusion ≫ D.localLift j`.
  This is the lift of the root subgroup into the graph subgroup.
- `D.rootLift_first j R`:
  `D.rootLift j R ≫ D.first = R.leftInclusion ≫ (C j).leftInclusion`.
- `D.rootLift_second j R`:
  `D.rootLift j R ≫ D.second = R.iso.hom ≫ R.rightInclusion ≫ (C j).rightInclusion`.
- `D.rootLift_closed j R`: `IsClosedSubgroup (D.rootLift j R)` when `G₂` is
  affine.
- `D.rootLift_first_rep hT j R hα hαν` and `D.rootLift_second_rep hT j R hα hαν`:
  let `T` be a split torus, `α ≠ 0`, and `latticePairing T α (ν j) = 0`. Then
  `D.rootLift j R ≫ D.first` represents `RelativeRoot.subgroup i₁ α`, and
  `D.rootLift j R ≫ D.second` represents `RelativeRoot.subgroup i₂ α`, on all
  tests (`IsRepresentedBy`).
- `rootTorusAction j R`: the action of `T` on `R.left`. It is
  `RelativeRoot.subgroupAction` for the local torus factor `(C j).leftTorus` and
  the representative `R.leftInclusion`.
- `D.rootTorusAction_act_comp j R s g`: for points `s` of `T` and `g` of
  `R.left` over any test `U`, the action is conjugation by the distinguished
  torus of the graph subgroup:
  `act s g ≫ rootLift = (s ≫ torusLift) * (g ≫ rootLift) * (s ≫ torusLift)⁻¹`.
- `D.range_rootLift_isNormalizedBy j R`: the range functor of `D.rootLift j R`
  is normalized by the range functor of `D.torusLift`, on all tests.
- `D.range_rootLift_le j R`: the range functor of `D.rootLift j R` is contained
  in `RelativeRoot.subgroup D.torusLift α`, the intrinsic root subgroup of the
  graph subgroup for its distinguished torus.

## Proofs

`leftTorus_localLift` is the published `GraphEnvelope.local_torusLift`. The
local torus factor composed with the first local map is `i₁` by
`leftTorusComp`. Composed with the second local map, it is `i₂` by
`torusIsoComp` and `rightTorusComp`.

The projection equations follow from `localLift_first` and `localLift_second`.
For the second one, `R.isoComp` rewrites
`R.leftInclusion ≫ (C j).iso.hom` as `R.iso.hom ≫ R.rightInclusion`.
Closedness composes `R.leftClosed` with the published
`GraphEnvelope.localLift_closed`. The latter uses closedness of
`(C j).leftInclusion`.

For the representations, `rootLift_first` reduces the first one to
`RootComparison.left_ambientRep`. `rootLift_second` reduces the second one to
`RootComparison.right_ambientRep` precomposed with the isomorphism `R.iso`.
Precomposing a representative with an isomorphism keeps it a monomorphism and
does not change its range (`SubgroupFunctor.range_iso_comp`).

For the torus action, `RelativeRoot.subgroupAction_act_comp` identifies
`act s g ≫ R.leftInclusion` with conjugation of `g ≫ R.leftInclusion` by
`s ≫ (C j).leftTorus` in `(C j).left`. Composing with the group homomorphism
`D.localLift j` preserves products and inverses. Then `leftTorus_localLift`
turns `(C j).leftTorus ≫ D.localLift j` into `D.torusLift`. Normalization
follows: a conjugate of a point of the lifted root subgroup by a point of the
torus is the lift of the acted point.

For the containment, a point of the range of `D.rootLift j R` is `y ≫ rootLift`
for a point `y` of `R.left`. Its image `y ≫ R.leftInclusion` lies in
`RelativeRoot.subgroup (C j).leftTorus α` because `R.leftInclusion`
represents that functor. `RelativeRoot.comp_mem_subgroup` along `D.localLift j`
gives membership in the root subgroup for
`(C j).leftTorus ≫ D.localLift j`, which is `D.torusLift`.

## Provenance

The provenance is internal. The constructions and theorems compose the
published Library results named above with the support modules
`SplitLeviGluingGraph` and `SplitLeviGluingLocal`. They formalize, in the
present setting, the paragraph after Proposition 23.20 in Milne, *Algebraic
Groups* (2017), printed p.491 (PDF p.507), source `milne-2017-algebraic-groups`.
There, for a subgroup variety `H` of `G_α`, `H''` is the graph of `φ_α|H` inside
the graph group `G''`. Each `U''_α` is a subgroup variety of `G''` isomorphic to
`U_α` via the first projection and normalized by the torus `T''`. Milne's local
groups are the `G_α` for simple roots `α`. Here the local groups are the dynamic
centralizers of arbitrary cocharacters `ν j`. The roots are any nonzero
characters `α` with `⟨α, ν j⟩ = 0`, and the root subgroups are the intrinsic
root functors. The present unit does not choose simple roots, prove density of
the cell (Milne 23.21–23.22), or prove that the projections are isomorphisms
(Milne 23.18).
