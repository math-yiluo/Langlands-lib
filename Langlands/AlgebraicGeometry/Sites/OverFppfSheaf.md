# A Zariski-plus-affine criterion for fppf sheaves on a slice of schemes

Module `Langlands.AlgebraicGeometry.Sites.OverFppfSheaf`, namespace
`Langlands.AlgebraicGeometry.OverFppfSheaf`.

Fix a scheme `S` and a presheaf of types `G : (Over S)ᵒᵖ ⥤ Type w`. The topologies on
`Over S` used here are the ones induced from topologies on all schemes,
`J.over S` (Mathlib `GrothendieckTopology.over`), in particular
`Scheme.zariskiTopology.over S` and `Scheme.fppfTopology.over S`.

## Main result

`isSheaf_fppfTopology_over G hzar haff : Presieve.IsSheaf (Scheme.fppfTopology.over S) G`
holds under two hypotheses:

- `hzar : Presieve.IsSheaf (Scheme.zariskiTopology.over S) G` (Zariski sheaf on `Over S`);
- `haff`: for every ring map `φ : R ⟶ R'` such that `Spec.map φ` is flat and surjective,
  and every `s : Spec R ⟶ S`, the presheaf `G` satisfies the sheaf condition for the
  single-arrow presieve on the morphism
  `Over.homMk (Spec.map φ) : Over.mk (Spec.map φ ≫ s) ⟶ Over.mk s` of `Over S`.

This is the slice version of the standard criterion (Stacks Project, Tag 022H; Mathlib's
`isSheaf_type_propQCTopology_iff`) that a presheaf on schemes is an fpqc sheaf as soon as it
is a Zariski sheaf and satisfies the sheaf condition for faithfully flat morphisms of
affine schemes. Internally, the proof establishes the fpqc sheaf property of the extension
`ext G` below and passes to the coarser fppf topology; only the fppf statement is exported.

## Construction: the extension of `G` to all schemes

`ext G : Scheme.{u}ᵒᵖ ⥤ Type (max u w)` sends a scheme `V` to
`Pt G V = Σ s : V ⟶ S, G.obj (op (Over.mk s))`, the pairs of a structure morphism to `S`
and a section of `G` over the resulting object of `Over S`; a morphism `g : W ⟶ V` sends
`⟨s, x⟩` to `⟨g ≫ s, G.map (Over.homMk g).op x⟩`. Its sections over `V` are therefore the
sections of the "pushforward along `Over S ⥤ Scheme`" of `G`, glued with the representable
presheaf of `S`.

Supporting lemmas: `map_congr_left`, `map_apply_congr_left`, `map_map_apply`
(values of `G` along morphisms of `Over S` depend only on underlying morphisms of schemes),
`tr` and `tr_rfl` (transport along an equality of structure morphisms), `sigma_eq_iff`
(equality of points of `Pt G V`), `map_eq_map_of_eq`, `ext_map_mk`,
`ext_map_mk_eq_mk_iff`, `ext_map_mk_eq_map_mk_iff`, `map_homMk_id_apply`.

## Transfer between `Over S` and all schemes

For any Grothendieck topology `J` on schemes with `[J.Subcanonical]`:

- `isSheaf_over_of_isSheaf_ext J`: if `ext G` is a `J`-sheaf, then `G` is a `J.over S`-sheaf.
  A compatible family of `G` on a covering sieve `R` of `Y : Over S` gives the compatible
  family `extFamily G x` of `ext G` on the underlying sieve `Sieve.overEquiv Y R`
  (`extFamily_compatible`); its amalgamation `⟨s, y⟩` has `s = Y.hom` because the
  representable presheaf of `S` is separated (subcanonicity), and after transport it is an
  amalgamation of `x` (`extFamily_isAmalgamation_iff`). Uniqueness also comes from
  `extFamily_isAmalgamation_iff`.
- `isSheaf_ext_of_isSheaf_over J`: if `G` is a `J.over S`-sheaf, then `ext G` is a
  `J`-sheaf. The first components of a compatible family of `ext G` on a covering sieve of
  `V` glue to `s₀ : V ⟶ S` (subcanonicity); the second components then form a compatible
  family `overFamily G x s₀ hs` of `G` on the covering sieve
  `(Sieve.overEquiv (Over.mk s₀)).symm R` (`overFamily_compatible`), whose amalgamations
  correspond exactly to amalgamations of `x` with first component `s₀`
  (`isAmalgamation_mk_of_overFamily`, `overFamily_isAmalgamation_of_mk`).

## Single affine coverings

`isSheafFor_singleton_ext p hS hG`: for `p : W ⟶ V`, if the representable presheaf of `S`
satisfies the sheaf condition for `{p}` and `G` satisfies it for every lift
`Over.homMk p : Over.mk (p ≫ s) ⟶ Over.mk s` (`s : V ⟶ S`), then `ext G` satisfies the sheaf
condition for `{p}`.

## Proof of the main result

`ext G` is an fpqc sheaf, hence `G` is an fppf sheaf on `Over S` by
`isSheaf_over_of_isSheaf_ext` with `J = Scheme.fppfTopology` and Mathlib's
`Presieve.isSheaf_of_le` with `Scheme.fppfTopology_le_fpqcTopology`. Since
`Scheme.fpqcTopology_eq_propQCTopology`, Mathlib's `isSheaf_type_propQCTopology_iff` reduces
the fpqc sheaf property of `ext G` to

- the Zariski sheaf property, from `hzar` by `isSheaf_ext_of_isSheaf_over` with
  `J = Scheme.zariskiTopology`;
- the sheaf property for `{Spec.map φ}` with `Spec.map φ` flat and surjective, from
  `isSheafFor_singleton_ext`: the representable presheaf of `S` satisfies it because
  `Spec.map φ` is a regular, hence effective, epimorphism
  (`isRegularEpi_of_flat_of_surjective_of_isAffine`,
  `Presieve.IsSheafFor.singleton_of_isRepresentable_of_effectiveEpi`), and the condition for
  `G` is `haff`.

The final theorem sets `backward.isDefEq.respectTransparency.types false`, as Mathlib's own
use of `isSheaf_type_propQCTopology_iff` in `Mathlib.AlgebraicGeometry.Sites.Fpqc` does.

## Provenance

Internal reduction written for the proof of
`Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonStatement`, where `G` is the
presheaf of isomorphism classes of rigidified line bundles. The mathematical input is the
fpqc criterion of Stacks Tag 022H as formalized in Mathlib; the transfer between `Over S` and
all schemes is the standard fact that sheaves on a slice of a subcanonical site correspond to
sheaves over the representable sheaf `S`.
