# Abelian-scheme structure from local abelian charts and a section: proof

Proof and Markdown: Worker 1178. The target statement was designed by
Workers 344 and 1109 and formalized by Worker 1043.

`Langlands.AbelianScheme.abelianSchemeStructureOfOpenCover` proves
`Langlands.AbelianScheme.AbelianSchemeStructureOfOpenCoverStatement.{u}`,
from the module `Langlands.AbelianScheme.AbelianSchemeStructureOfOpenCoverStatement`:

```lean
∀ (S : Scheme.{u}) (P : Over S) (s : 𝟙_ (Over S) ⟶ P)
  (𝒰 : S.OpenCover.{u}),
  (∀ i, ∃ B : AbelianScheme (𝒰.X i),
    Nonempty ((Over.pullback (𝒰.f i)).obj P ≅ B.X)) →
    ∃ (B : AbelianScheme S) (e : P ≅ B.X), s ≫ e.hom = η[B.X]
```

The proof uses no hypothesis beyond the statement's. The universe `u`, the
base `S`, the object `P`, the section `s` and the open cover `𝒰` are
arbitrary. In particular `S` need not be quasi-separated, and the cover need
not be finite or affine. The constructed `B` has underlying object exactly
`P`, and `e` is `Iso.refl P`. The proof does not preserve the local group
laws of the hypothesis, and it proves no uniqueness.

## Dependencies

The module imports the statement module and
`Langlands.AbelianScheme.PointedMorphismRigidityProof`. The proof uses the
published theorem `Langlands.AbelianScheme.pointedMorphismRigidity`, which
proves `PointedMorphismRigidity` over an arbitrary base. It also uses the
Library bundle `AbelianScheme` and its base change `AbelianScheme.baseChange`
from `Langlands.AbelianScheme.Basic`. From Mathlib it uses:

- scheme gluing of morphisms: `Scheme.Cover.glueMorphisms`,
  `Scheme.Cover.ι_glueMorphisms` and `Scheme.Cover.hom_ext`;
- the pullback cover `𝒰.pullback₁`;
- group objects from representable presheaves: `CommGrpObj.ofRepresentableBy`;
- translations `GrpObj.mulRight`, and the facts that monoidal functors and
  group-object homomorphisms preserve the pointwise group laws on Hom sets;
- target-locality of smoothness, properness and geometric connectedness:
  `IsZariskiLocalAtTarget.of_openCover`.

No existing Library file is changed. The auxiliary declarations live in the
namespace `Langlands.AbelianScheme.OpenCoverStructure`.

## Charts

Throughout, a point of `P` over a scheme morphism `t ≫ g` means a scheme
morphism `a : Z ⟶ P.left` with `a ≫ P.hom = t ≫ g`.

`ptLift P g t a ha` turns such a point into the morphism
`Over.mk t ⟶ (Over.pullback g).obj P` given by `pullback.lift a t ha`.

`Chart P s V g`, for an arbitrary scheme morphism `g : V ⟶ S`, consists of

- an abelian scheme `A : AbelianScheme V`,
- an isomorphism `ψ : (Over.pullback g).obj P ≅ A.X` in `Over V`,
- the condition `pointed`: for every `t : Z ⟶ V`, the point
  `t ≫ g ≫ s.left` of `P` is sent by `ψ` to the unit, that is,
  `ptLift P g t (t ≫ g ≫ s.left) _ ≫ ψ.hom = 1` in the group
  `Over.mk t ⟶ A.X`.

For a chart `c`, `c.loc t a ha := ptLift P g t a ha ≫ c.ψ.hom` is a point of
`A` over `t`. `c.glob x := (x ≫ c.ψ.inv).left ≫ pullback.fst P.hom g`
converts a point of `A` back. `glob_loc` and `loc_glob` show that these are
inverse bijections, and `glob_w` shows that `c.glob x` lies over `t ≫ g`.
The chart operations are

- `c.mul t a b ha hb := c.glob (c.loc t a ha * c.loc t b hb)`,
- `c.inv t a ha := c.glob (c.loc t a ha)⁻¹`,

where the operations on the right are the pointwise group laws of the group
object `A.X`. `loc_mul`, `loc_inv` and `loc_one` (the last is `pointed`)
say that `c.loc` carries `c.mul`, `c.inv` and the point `t ≫ g ≫ s.left`
to the product, the inverse and the unit. `loc_inj` says that `c.loc` is
injective. `comp_mul` and `comp_inv` prove naturality under precomposition
with any `φ : Z' ⟶ Z`, from `loc_comp`, `glob_comp` and Mathlib's
`MonObj.comp_mul` and `GrpObj.comp_inv`.

## Same-base agreement: rigidity

`isMonHom_trans` proves that for two charts `c₁ c₂ : Chart P s V g` the
isomorphism `c₁.ψ.inv ≫ c₂.ψ.hom : c₁.A.X ⟶ c₂.A.X` is a monoid
homomorphism. It applies `pointedMorphismRigidity` with source `c₁.A`, which
is smooth, proper and geometrically connected (`AbelianScheme.isAbelian`).
The target `c₂.A` is locally of finite presentation (from smoothness), and
quasi-compact and quasi-separated (from properness). The unit condition
`η ≫ c₁.ψ.inv ≫ c₂.ψ.hom = η` is the `pointed` condition of both charts at
`t = 𝟙 V`. Consequently (`mul_eq`, `inv_eq`) the two charts give the same
`mul` and `inv`. `mul_eq_of_eq` and `inv_eq_of_eq` state this for charts over
two equal morphisms `g₁ = g₂`.

## Restriction of charts

For `h : V' ⟶ V`, `c.restrict h : Chart P s V' (h ≫ g)` has abelian scheme
`(AbelianScheme.baseChange h).obj c.A`. Its isomorphism `restrictψ` is the
canonical identification `restrictIso` of `(Over.pullback (h ≫ g)).obj P`
with `(Over.pullback h).obj ((Over.pullback g).obj P)`, built from Mathlib's
`pullbackLeftPullbackSndIso`, followed by `(Over.pullback h).mapIso c.ψ`.
`ptLift_restrictIso` computes it on points. As a result, `restrict_loc`
shows that the restricted chart's local point is `c.rmap h (c.loc (t ≫ h) a _)`,
where `rmap h x := unitPt h t ≫ (Over.pullback h).map x` and `unitPt` is the
morphism given by `pullback.lift (𝟙 Z) t`. Since `Over.pullback h` is
monoidal, `rmap` preserves products and inverses (`rmap_mul`, `rmap_inv`,
from `Functor.map_mul` and `Functor.map_inv'`), and it sends the unit to the
unit. This gives the restricted chart's `pointed` condition. It also gives
`restrict_mul` and `restrict_inv`: the restricted chart's operations at `t`
are the original chart's operations at `t ≫ h`.

## Cross-chart agreement

`mul_eq_mul` and `inv_eq_inv` treat charts `c₁` over `g₁ : V₁ ⟶ S` and `c₂`
over `g₂ : V₂ ⟶ S`, and points over `t₁ ≫ g₁ = t₂ ≫ g₂`. Both charts are
restricted to `pullback g₁ g₂`, along `pullback.fst` and `pullback.snd`, and
evaluated at `pullback.lift t₁ t₂ _`. The two restricted charts lie over
`pullback.fst g₁ g₂ ≫ g₁ = pullback.snd g₁ g₂ ≫ g₂` (`pullback.condition`).
Same-base agreement then shows that `c₁` and `c₂` give the same products and
inverses. No compatibility of the original local data is used.

## Gluing over the cover

Fix one chart `c i : Chart P s (𝒰.X i) (𝒰.f i)` for each index. For
`T : Over S`, the open cover `𝒰.pullback₁ T.hom` of `T.left` has members
`pullback T.hom (𝒰.f i)`. On member `i`, a point `x : T ⟶ P` gives the point
`pullback.fst T.hom (𝒰.f i) ≫ x.left` of `P` over
`pullback.snd T.hom (𝒰.f i) ≫ 𝒰.f i` (`pt_w`).

- `gmulLeft c x y` glues the morphisms `(c i).mul` of these points with
  `Scheme.Cover.glueMorphisms`. On a pairwise overlap the two restrictions
  agree, by naturality (`comp_mul`) and cross-chart agreement
  (`overlap_w` supplies the equality of base morphisms). `ginvLeft c x`
  glues `(c i).inv` in the same way.
- `gmul c x y` and `ginv c x` are these morphisms viewed in `Over S`.
  `comp_gmul_left` and `comp_ginv_left` compute
  `z ≫ (gmul c x y).left` for any `z` whose composite with `T.hom` factors
  through `𝒰.f i`. `hom_ext'` reduces equality of two morphisms `T ⟶ P`
  to equality on every member of the cover.
- The unit is `toUnit T ≫ s`.

`loc_gmul`, `loc_ginv` and `loc_gone` show that, on each member,
`(c i).loc` carries `gmul`, `ginv` and `toUnit T ≫ s` to the product,
inverse and unit of the commutative group `Over.mk _ ⟶ (c i).A.X`. By
`loc_inj` and `hom_ext'`, associativity, commutativity, the unit laws and
the left inverse law follow from the corresponding laws in these groups
(`gmul_assoc`, `gmul_comm`, `gone_mul`, `gmul_one`, `ginv_mul`). These laws
define `homGroup c T : CommGroup (T ⟶ P)`. `comp_gmul` and `comp_ginv`
prove naturality in `T`, using `comp_gmul_left` and `comp_ginv_left`.

`pointsFunctor c : (Over S)ᵒᵖ ⥤ CommGrpCat` sends `T` to `T ⟶ P` with this
group structure and acts by precomposition. `pointsRep c` shows that `P`
represents its underlying presheaf of sets, with the identity bijection.

## Recentred charts from the hypothesis

`sec P s g : 𝟙_ (Over V) ⟶ (Over.pullback g).obj P` is the restriction of
`s`, given by `pullback.lift (g ≫ s.left) (𝟙 V)`. `ptLift_eq` shows that
the point `t ≫ g ≫ s.left` equals `toUnit (Over.mk t) ≫ sec P s g`. Let
`e : (Over.pullback g).obj P ≅ A.X` be an arbitrary isomorphism and put
`q := sec P s g ≫ e.hom`. Then `Chart.ofIso P s A e` takes
`ψ := e ≪≫ GrpObj.mulRight q⁻¹`, so `ψ` composes `e` with translation by
`q⁻¹`. By `comp_mulRight_inv`, `q ≫ (GrpObj.mulRight q⁻¹).hom = η`, which
gives the `pointed` condition. This recentring changes the group law
transported to the restriction of `P`, which the statement allows.

## Assembly

In `abelianSchemeStructureOfOpenCover`, `choose` extracts from the
hypothesis an abelian scheme `B i` and a nonempty set of isomorphisms
`e i : Nonempty (... ≅ (B i).X)` for each index. The charts are
`c i := Chart.ofIso P s (B i) (e i).some`. Then

- `CommGrpObj.ofRepresentableBy P (pointsFunctor c) (pointsRep c)` is a
  group-object structure on `P`, with `IsCommMonObj`;
- `Smooth P.hom` follows from `IsZariskiLocalAtTarget.of_openCover 𝒰`.
  Here `𝒰.pullbackHom P.hom i` is `((Over.pullback (𝒰.f i)).obj P).hom`,
  which is `(e i).some.hom.left ≫ (B i).X.hom` (`smooth_hom_of_iso`). The
  instance `IsZariskiLocalAtTarget @Smooth` is supplied explicitly as
  `HasRingHomProperty.instIsZariskiLocalAtTarget _`;
- `IsProper P.hom` and `GeometricallyConnected P.hom` follow in the same way
  through `prop_hom_of_iso`. For geometric connectedness the proof uses the
  equivalent form `geometrically (ConnectedSpace ·)` from
  `geometricallyConnected_iff`, which Mathlib proves Zariski-local at the
  target.

The resulting `AbelianScheme S` has underlying object `P`, and
`e := Iso.refl P`. The unit of the represented group object is
`toUnit (𝟙_ (Over S)) ≫ s`, the unit of `homGroup` at the terminal object.
Since `toUnit (𝟙_ _) = 𝟙`, this gives `s ≫ e.hom = η[B.X]`.

## Provenance

This is an internal derived proof of an internal derived statement. No
external source is cited. The route follows the proof leads recorded in the
statement Markdown and in the task context: recentring, rigidity on
overlaps, gluing and target-locality of the geometric conditions. Two
details of the implementation differ from those leads. The group law is
glued on Hom-sets and turned into a group object with
`CommGrpObj.ofRepresentableBy`, instead of gluing the multiplication
morphism on `P ×_S P` and checking diagrams. The comparison on overlaps also
goes through base change of the abelian schemes to `pullback g₁ g₂`.
