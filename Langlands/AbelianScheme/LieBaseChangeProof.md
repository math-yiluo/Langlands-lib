# Canonical Lie base change for abelian schemes: proof

Lean module: `Langlands.AbelianScheme.LieBaseChangeProof`.

## Main result

`Langlands.AbelianScheme.lieBaseChange (S : AlgebraicGeometry.Scheme.{u}) :
LieBaseChangeStatement S` proves the published proposition
`Langlands.AbelianScheme.LieBaseChangeStatement S` for every scheme `S` in an
arbitrary universe `u`. The theorem has no hypotheses besides `S`.

The proposition says the following. Let `T` be a scheme, `b : T ⟶ S` a
morphism and `A` an abelian scheme over `S`. Then:

1. the canonical cotangent comparison
   `GroupScheme.cotangentBaseChangeMap b A.toGrp` is an isomorphism; and
2. there is an isomorphism
   `ell : (pullback b).obj A.Lie ≅ ((baseChange b).obj A).Lie` with
   `ell.hom ≫ dualMap (cotangentBaseChangeMap b A.toGrp) =
   dualPullbackComparison b (cotangentAtIdentity A.toGrp)`.

So the Lie module of the base change is identified with the pullback of the
Lie module through the actual canonical comparison maps. These maps are not
replaced by abstract data. The proof adds no flatness hypothesis on `b` and no
global relative dimension. The only geometric input about `A` is the
smoothness of `A.X.hom` stored in the abelian-scheme structure (`A.smooth`).

## Inputs from the Library

- `Langlands.GroupScheme.cotangentBaseChangeIsIso` (module
  `Langlands.AbelianScheme.CotangentBaseChangeProof`) proves
  `GroupScheme.CotangentBaseChangeIsIsoStatement S`: the cotangent comparison
  is invertible for every base change of every group scheme over `S`.
- `Langlands.Scheme.smoothDifferentialsFiniteLocalBasisRank` (module
  `Langlands.AlgebraicGeometry.SmoothDifferentialsFiniteLocalBasisRank`) proves
  `SmoothDifferentialsFiniteLocalBasisRankStatement`. In particular, the
  relative differentials of a smooth morphism have local generating data that
  is locally free and of finite type.
- `Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank` (module
  `Langlands.AlgebraicGeometry.PullbackFiniteLocalBasisRankProof`) transports
  such data along the pullback of module sheaves along any morphism.

The helper module `Langlands.AlgebraicGeometry.ModuleDualPullbackLocalFree`
is submitted together with this proof and has its own Markdown file. It proves
`Langlands.Scheme.Modules.isIso_dualPullbackComparison_of_localGeneratorsData`:
for every morphism `f` and every module sheaf with locally free finite-type
local generating data, the canonical comparison `dualPullbackComparison f M`
is an isomorphism.

## Proof

The file contains three theorems.

`lieBaseChange_of S hc hd` derives the target from two hypotheses:
`hc : GroupScheme.CotangentBaseChangeIsIsoStatement S` and
`hd : Langlands.Scheme.SmoothDifferentialsFiniteLocalBasisRankStatement.{u}`.
Fix `T`, `b` and `A`.

- The first conjunct is `hc T b A.toGrp`.
- For the second conjunct, `hd` applied to the smooth structure morphism
  `A.X.hom` and `A.smooth` gives locally free finite-type local generating data
  for its relative differentials. `pullbackFiniteLocalBasisRank` pulls this
  data back along the identity section `GroupScheme.identitySection A.toGrp`.
  The result is such data for `GroupScheme.cotangentAtIdentity A.toGrp`, which
  is by definition this pullback of the relative differentials. The helper
  theorem then shows that
  `dualPullbackComparison b (cotangentAtIdentity A.toGrp)` is an isomorphism.
- Take `ell` to be this comparison isomorphism followed by the inverse of
  `dualMap (cotangentBaseChangeMap b A.toGrp)`. That dual map is invertible
  because the cotangent map is. The source of `ell` is `(pullback b).obj A.Lie`,
  since `A.Lie` is the dual of the cotangent module at the identity. Its target
  is the dual of the cotangent module of the base change, which is
  `((baseChange b).obj A).Lie`.
- The required equation follows from associativity, `IsIso.inv_hom_id` and
  `Category.comp_id`: composing `ell.hom` with the dual map returns the
  comparison.

`lieBaseChange_of_cotangent S hc` supplies `hd` from
`smoothDifferentialsFiniteLocalBasisRank`.

`lieBaseChange S` supplies `hc` from `GroupScheme.cotangentBaseChangeIsIso S`.
This is the unconditional final theorem.

## Relation to the literature

Both maps in the statement are the canonical Library constructions. The
cotangent comparison comes from base change of relative differentials (Stacks
Project Lemma 29.33.10, tag 01V0), as formalized in the imported cotangent
proof. The duality step is the standard fact that pulling back commutes with
taking duals of finite locally free modules. The helper module's Markdown
explains how its Lean proof establishes this fact for an arbitrary morphism.
