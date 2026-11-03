# Structural properties of the actual standard family of rational points

Implementation and documentation: Worker 785 (task
`7d46c4f8-9da1-4872-9784-df53d7c630cf`, Jacquet–Cartan data on general
reductive rational points). This is the concrete side of the planned assembly
of a `Langlands.JacquetCartanDatum` on `G(F)` from the standard parabolic
subgroups. It supplies, for the published actual standard family
[`Aubert.General.RationalPointFamily`](RationalPointFamily.md), the Levi,
unipotent, closedness, top-endpoint and unipotent-descent facts such an assembly
needs. The datum itself, the Iwasawa and Cartan decompositions and wall
contraction are not treated here.

Part of the module is unconditional. The rest is **conditional** on the two
published Prop targets `GroupScheme.StandardCocharacterStatement`
(`Langlands/GroupScheme/Rational/StandardCocharacterStatement.lean`) and
`GroupScheme.StandardParabolicOrderStatement`
(`Langlands/GroupScheme/Rational/StandardParabolicOrderStatement.lean`). These
enter as the explicit hypotheses `hstd` and `hord`, and nothing here proves them.

## Setting

`k` is a field, `T` a commutative group scheme and `G` a group scheme over
`Spec k`, `i : T.toGrp ⟶ G` and `ν : cocharacterLattice T`. The index type is
the published `SimpleRoot i ν` (a type in the universe of `k`). For
`I : Finset (SimpleRoot i ν)` the published `parabolic i ν I`, `levi i ν I` and
`unipotent i ν I` are the identity-test rational points of
`standardParabolic/standardLevi/standardUnipotent i ν (rootSet i ν I)`. Each is
the intersection, over all standard cocharacters `ζ` of `rootSet i ν I`, of the
rational points of the dynamic subgroup `Dynamic.parabolic/centralizer/unipotent`
of `groupHom ζ ≫ i`. As in the published family, every declaration takes the
instance argument `[IsAffineHom G.X.hom]`. The topology on
`RationalPoint k G.X` is the published pinned `rationalPointTopology k G.X`,
bound by `letI` inside the closedness statements. This is the topology
`RationalPointsJacquetCartanDatumStatement` uses.

## Declarations

Namespace `Langlands.Aubert.General.RationalPointFamily`.

### Unconditional facts

* `mem_levi_iff`, `mem_unipotent_iff`: `g ∈ levi i ν I` (resp.
  `unipotent i ν I`) iff `g` lies in the rational points of
  `Dynamic.centralizer` (resp. `Dynamic.unipotent`) of `groupHom ζ ≫ i` for every
  standard cocharacter `ζ` of `rootSet i ν I`. These are the published
  `mem_standardLevi` and `mem_standardUnipotent`.
* `coe_levi`, `coe_unipotent`: the same facts as equalities of the underlying
  sets with the corresponding double intersections.
* `levi_le_normalizer I`: `levi i ν I ≤ Subgroup.normalizer (unipotent i ν I)`.
  Proof: let `m ∈ levi i ν I` and fix a standard cocharacter `ζ`. Then `m` lies
  in the dynamic centralizer of `groupHom ζ ≫ i`, hence in its dynamic parabolic
  (`Dynamic.centralizer_le_parabolic`). The published
  `dynamic_parabolic_le_normalizer` (`Aubert/General/DynamicParabolic`) says that
  this parabolic normalizes the dynamic unipotent subgroup. Conjugation by `m`
  therefore preserves membership in each dynamic unipotent subgroup of the
  intersection, so it preserves `unipotent i ν I`.
* The imported `unipotent_univ_eq_bot [Fintype (SimpleRoot i ν)]` from
  [RationalEndpoint](RationalEndpoint.md):
  `unipotent i ν Finset.univ = ⊥`. Proof: `rootSet_univ` identifies the root set
  with `simpleRelativeRoots i ν`. Then apply the published
  `standardUnipotent_simple_eq_bot` (`GroupScheme/Rational/EndpointReductions`).
* `unipotent_eq_bot_of_forall_mem (hI : ∀ a, a ∈ I)`:
  `unipotent i ν I = ⊥` for an index containing every simple root. The finset
  `I` gives a `Fintype` instance in which `I = Finset.univ`, and
  `unipotent_univ_eq_bot` applies.
* `wallUnipotent I α := unipotent i ν (I.erase α) ⊓ levi i ν I` (needs
  `[DecidableEq (SimpleRoot i ν)]`), the *wall subgroup* of the standard Levi
  `M_I` at the simple root `α`: the points of `N_{I \ {α}}` that lie in `M_I`.
  `wallUnipotent_le_levi` is `wallUnipotent i ν I α ≤ levi i ν I`. For `α ∈ I`
  it models the unipotent radical of the maximal standard parabolic of `M_I`
  attached to `I \ {α}`. Nothing here proves that identification: the Lean
  definition is the intersection only.
* `isClosed_levi I`, `isClosed_unipotent I`, for `[TopologicalSpace k]
  [T2Space k] [IsAffine G.X.left]`: `levi i ν I` and `unipotent i ν I` are closed
  in `rationalPointTopology k G.X`. Proof: by `coe_levi`/`coe_unipotent` each is
  an intersection of the rational points of dynamic centralizers/unipotent
  subgroups. Each of these is closed by the published
  `isClosed_rationalPoint_subgroup` (`AlgebraicGeometry/PointTopology/RepresentedSubgroup`).
  Its representability and closed-subgroup inputs are
  `Dynamic.Affine.isRepresentedBy_centralizerHom` /
  `isClosedSubgroup_centralizerHom` (resp. `isRepresentedBy_unipotentHom` /
  `isClosedSubgroup_unipotentHom`) from `GroupScheme/Dynamic/AffineRepresentability`.
* `isClosed_levi_of_isNonarchimedeanLocalField`,
  `isClosed_unipotent_of_isNonarchimedeanLocalField`: the same for a
  nonarchimedean local field `F` with `[IsAffine G.X.left]`. The Hausdorff
  hypothesis on `F` is the published
  `Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F`.
* `finite_simpleRoot hG hi ν`: for `hG : IsConnectedReductive G` and
  `hi : IsMaximalSplitTorus i`, `SimpleRoot i ν` is finite. Smoothness of `G`
  comes from `hG.smooth`. The published `simpleRelativeRootFintypeOfIsSplitTorus`
  (`GroupScheme/Rational/RootSupportFiniteness`), applied to the split torus
  `hi.isSplitSubtorus.1`, gives a `Fintype` instance.
* `exists_unipotent_eq_bot hG hi ν`: some `I : Finset (SimpleRoot i ν)` contains
  every simple root and has `unipotent i ν I = ⊥`. Proof: `Finset.univ` for the
  `Fintype` instance from `finite_simpleRoot`, then `unipotent_univ_eq_bot`.
* `exists_maximalSplitTorus_genericCocharacter hG`: a connected reductive `G`
  has `T`, `i : T.toGrp ⟶ G` and `ν` with `IsMaximalSplitTorus i` and
  `IsGenericCocharacter i ν`. The published theorem `cocharacterMaximalSplitTorus`,
  applied to the trivial cocharacter, gives a maximal split torus. The published
  `IsSplitTorus.exists_genericCocharacter` gives a generic cocharacter of it.

### Conditional facts

This section fixes `hG : IsConnectedReductive G`, `hi : IsMaximalSplitTorus i`
and `hν : IsGenericCocharacter i ν`. Each lemma also takes `hord`, `hstd` or
both, as stated.

* `parabolic_mono hG hi hν hord (hJI : J ⊆ I)`:
  `parabolic i ν J ≤ parabolic i ν I`.
* `levi_mono hG hi hν hord hJI`: `levi i ν J ≤ levi i ν I`.
* `unipotent_anti hG hi hν hord hJI`: `unipotent i ν I ≤ unipotent i ν J`.

  These three apply `hord` to `rootSet i ν J ⊆ rootSet i ν I`. The root sets
  lie in the simple roots by `rootSet_subset`, and the inclusion is
  `rootSet_subset_iff`. The proofs take the forward implication of the parabolic
  equivalence and the Levi and unipotent inclusions, evaluated at the identity
  test object.
* `exists_mul_of_mem_parabolic hG hi hν hstd I (hp : p ∈ parabolic i ν I)`:
  `∃ m ∈ levi i ν I, ∃ n ∈ unipotent i ν I, p = m * n`. The published
  `isSemidirectDecomposition hstd hG i hi ν hν I` (module
  [`Aubert.General.StandardFamily`](StandardFamily.md)) makes `levi` and
  `unipotent` complementary subgroups of `parabolic`. The decomposition of `p` is
  read off from `IsComplement'.existsUnique`.
* `exists_mul_of_mem_unipotent hG hi hν hstd hord (hJI : J ⊆ I)
  (hn : n ∈ unipotent i ν J)`:
  `∃ u ∈ unipotent i ν J ⊓ levi i ν I, ∃ n' ∈ unipotent i ν I, n = u * n'`.
  Proof: `n` lies in `parabolic i ν J ≤ parabolic i ν I` (`unipotent_le_parabolic`,
  `parabolic_mono`). Write `n = m * n'` with `m ∈ levi i ν I` and
  `n' ∈ unipotent i ν I` (`exists_mul_of_mem_parabolic`). Then
  `n' ∈ unipotent i ν J` by `unipotent_anti`, so `m = n * n'⁻¹` lies in
  `unipotent i ν J` too.
* `exists_mul_of_mem_unipotent_erase hG hi hν hstd hord I α
  (hn : n ∈ unipotent i ν (I.erase α))`:
  `∃ u ∈ wallUnipotent i ν I α, ∃ n' ∈ unipotent i ν I, n = u * n'`, the case
  `J = I.erase α` of the previous lemma.

## Intended use

Each fact used in the assembly comes in the form the assembly needs, with
indices `Finset (SimpleRoot i ν)`:

| assembly input | supplied by |
| --- | --- |
| parabolics increase | `parabolic_mono` (needs `hord`) |
| `P_I = M_I N_I` | `exists_mul_of_mem_parabolic` (needs `hstd`) |
| `M_I` normalizes `N_I` | `levi_le_normalizer` |
| `M_I` closed | `isClosed_levi_of_isNonarchimedeanLocalField` |
| top index with `N = ⊥` | `exists_unipotent_eq_bot` / `unipotent_eq_bot_of_forall_mem` |
| descent `N_J ⊆ (N_J ∩ M_I) N_I` | `exists_mul_of_mem_unipotent` (needs `hstd`, `hord`) |

The universe and topology agree with the target, as noted under Setting.

## Provenance

Internal. The family, the standard cocharacter and order statements, the
semidirect decomposition and the dynamic-subgroup facts used here are all
published Library results, imported by Lean name. This module only combines
them. The decompositions are the Lean forms of the standard facts
`P_I = M_I ⋉ N_I` and, for `J ⊆ I`, `N_J = (N_J ∩ M_I) N_I`. The second follows
from the first and the order statement, by the argument given above.
