# Proof: split and quasi-split special fibres over a henselian DVR

Worker 365.

`Langlands.GroupScheme.henselianDiscreteSpecialFibreSplit` proves the unchanged
published proposition
[`HenselianDiscreteSpecialFibreSplitStatement`](HenselianDiscreteSpecialFibreSplitStatement.md)`.{u}`
in every universe `u`. That proposition transcribes Brian Conrad, *Reductive group
schemes* (2014), Exercise 5.5.3(ii), p.182. Its exact formulation and provenance are in
the statement's paired Markdown. The proof adds no hypothesis and does not weaken the
conclusion. It uses only published Library theorems.

The module has two lemmas, one for each half of the statement, and one helper. Both
lemmas are more general than the statement needs. They assume only that `R` is a
henselian local ring (`HenselianLocalRing R`), not a discrete valuation ring or a
domain. They conclude for the fibre `(GroupScheme.baseChange b).obj G` at an arbitrary
field point `b : Spec K ⟶ Spec R`, not only the generic fibre. The main theorem applies
them with `b = Spec.algebraMap R K`. The discrete valuation ring and `IsFractionRing R K`
hypotheses of the statement are not used.

## Declarations

- `IsReductive.exists_split_maximalTorus_fieldPoint_of_specialFibre`: for a
  reductive `G` over a henselian local ring `R`, suppose the special fibre `G₀` (base
  change along `Spec.algebraMap R (IsLocalRing.ResidueField R)`) has a commutative
  `T` and `i : T ⟶ G₀` with `IsSplitTorus T` and `IsMaximalTorus i`. Then for every
  field `K` and every `b : Spec K ⟶ Spec R` there are a commutative `T'` over `K` and
  `i' : T' ⟶ G_b` with `IsSplitTorus T'` and `IsMaximalTorus i'`.
- `isGeometricBorelSubgroup_residueFibre_of_fieldPoint`: for a base scheme `S`, an
  ambient `G` with `IsAffineHom G.X.hom`, a closed subgroup `i : B ⟶ G` and a field
  point `b : Spec k ⟶ S`, if the base change of `i` along `b` is a geometric Borel
  (`IsGeometricBorelSubgroup`), then so is the residue fibre
  `RelativeLevi.residueFiberHom i s` at `s = b(closed point)`.
- `IsReductive.isQuasiSplit_fieldPoint_of_specialFibre`: for a reductive `G` over a
  henselian local ring `R`, if `IsQuasiSplit G₀`, then `IsQuasiSplit G_b` for every
  field point `b : Spec K ⟶ Spec R`.
- `henselianDiscreteSpecialFibreSplit : HenselianDiscreteSpecialFibreSplitStatement.{u}`.

## The Lean proof

### Split half

Write `κ` for the residue field and `c = Spec.algebraMap R κ`. From `IsSplitTorus T`
take a finite `I` and an isomorphism `e : T ≅ splitTorus κ I`. Let `H` be the split
torus `splitTorus.commGroupScheme (Spec R) I` over `R`. The isomorphism
`e₀ = splitTorus.baseChangeIso c I ≪≫ e.symm` identifies the special fibre of `H` with
`T`. Then `i₀ = e₀.hom ≫ i` is a closed subgroup (`IsClosedSubgroup.iso_comp`).

1. `exists_closed_splitHom_lift` (from
   [`Torus.HenselianSplitSubgroupLifting`](../Torus/HenselianSplitSubgroupLifting.md))
   uses the henselian property and surjectivity of `R → κ`. It gives a closed subgroup
   `j : H ⟶ G` whose base change along `c` is exactly `i₀`.
2. `IsMaximalTorus.iso_comp` transports maximality of `i` to `i₀`, so the base change
   of `j` along `c` is a maximal torus.
3. `isMaximalTorus_residueFibre_of_fieldPoint` passes this to the residue fibre at
   `c(closed point of κ)`. `IsLocalRing.comap_closedPoint` identifies that point with
   the closed point of `Spec R`.
4. `IsReductive.isMaximalTorus_fieldPoint_of_closedFibre` (from
   [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md)) shows that a closed
   split torus maximal on the closed fibre is maximal on every field-valued fibre. In
   particular `(GroupScheme.baseChange b).map j` is a maximal torus. Its source
   `(CommGroupScheme.baseChange b).obj H` is split by `IsSplitTorus.baseChange`.

### Quasi-split half

From `IsQuasiSplit G₀` take a geometric Borel `i₀ : B₀ ⟶ G₀`.

1. `parabolicDynamic` (field theorem: a closed subgroup of a connected reductive group
   is parabolic iff it is a dynamic parabolic `P(χ)`) gives a cocharacter `χ₀` of `G₀`
   with `SubgroupFunctor.range i₀ = Dynamic.parabolic χ₀`.
2. `HomScheme.exists_cocharacter_baseChange_eq` lifts `χ₀` exactly. It gives a
   cocharacter `χ` of `G` with `Dynamic.baseChangeCocharacter c χ = χ₀`.
3. `dynamicBaseRepresentability` gives a closed subgroup `p : P ⟶ G` representing
   `Dynamic.parabolic χ`, and also representatives of the unipotent and centralizer
   functors. `dynamicRelativeLevi` then shows that `p` is a relative parabolic subgroup
   (`IsRelativeParabolicSubgroup p`).
4. Representability base-changes along `c`. By `Dynamic.parabolic_baseChange` and
   step 2, the base change of `p` along `c` represents `Dynamic.parabolic χ₀`. That is
   the range of `i₀`. `IsGeometricBorelSubgroup.isRelativeBorelSubgroup` makes `i₀` a
   relative Borel over `Spec κ`, and `IsRelativeBorelSubgroup.of_range_eq` transfers
   this to the base change of `p`. `IsRelativeBorelSubgroup.fieldPoint` at the identity
   of `Spec κ`, followed by `isGeometricBorelSubgroup_of_baseChange_comp`, shows that
   the base change of `p` along `c` is a geometric Borel.
5. The helper lemma moves this to the residue fibre of `p` at `c(closed point)`, which
   is the closed point of `Spec R`. The helper factors `b` through the residue field at
   its image point (`fieldPointResidueMap_factorization`). It then descends along that
   field extension with `IsGeometricBorelSubgroup.of_baseChange` and
   `isGeometricBorelSubgroup_baseChange_comp`.
6. `relativeBorelLocusClopen` shows that the set of points where the residue fibre of
   `p` is a geometric Borel is open and closed. It contains the closed point. Every
   point of `Spec R` specializes to the closed point (`IsLocalRing.specializes_closedPoint`),
   so the open set is everything. Hence `p` is a relative Borel subgroup over `Spec R`.
7. `IsRelativeBorelSubgroup.fieldPoint` makes the base change of `p` along `b` a
   geometric Borel. `IsReductive.isConnectedReductive_baseChange` makes `G_b` connected
   reductive. Together these give `IsQuasiSplit G_b`.

### Main theorem

After introducing the data and the two `let`-bound fibres, the main theorem applies the
quasi-split lemma and the split lemma with `b = Spec.algebraMap R K`.

## Relation to the source

Conrad leaves the exercise to the reader. The hint is to lift a Borel subgroup or a
split maximal torus of the special fibre using the smooth schemes `Bor_{𝒢/R}` or
`Tor_{𝒢/R}` and the henselian property, then pass to the generic fibre. The Lean proof
follows this outline but does not use the scheme of Borel subgroups. In the Library,
`RelativeBorelSchemeStatement` is not yet proved. Instead, the Borel subgroup is lifted
as a dynamic parabolic of a lifted cocharacter. The split torus is lifted through the
Library's henselian lifting of homomorphisms from split tori.

Source: Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014, Exercise 5.5.3(ii), p.182. It is registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`. This module adds no
new definition or statement beyond the lemmas listed above.
