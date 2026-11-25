# Represented solvable radicals under isomorphisms and field extensions

This helper module proves seven theorems about the Library predicate
`IsSolvableRadical r` (from `Langlands.GroupScheme.Rational.LeviSubgroup`). They
are the solvable-radical counterparts of published lemmas for `IsUnipotentRadical`
in `Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport`,
`Langlands.GroupScheme.Rational.UnipotentRadicalProperties` and
`Langlands.GroupScheme.Rational.UnipotentRadicalGalois`, and their proofs follow
those lemmas. The module supports the proof in
`Langlands.GroupScheme.Rational.SeparableSolvableRadicalProof`.

Recall that `IsSolvableRadical r`, for `r : R ⟶ G` between group schemes over
`Spec k` with `k` a field, has six fields: `r` is a closed subgroup
(`isClosedSubgroup`); `R` is smooth (`smooth`), connected (`connectedSpace`) and
solvable (`isSolvableGroupScheme`, the Library's `IsSolvableGroupScheme`); the image
subgroup functor `SubgroupFunctor.range r` is normal (`isNormal`); and every closed
subgroup `j : H ⟶ G` with `H` smooth, connected and solvable and normal image has
image contained in that of `r` (`greatest`).

Below, `bc f` abbreviates `GroupScheme.baseChange f`, and for a field map
`k → K` the morphism `Spec K ⟶ Spec k` is
`Spec.map (CommRingCat.ofHom (algebraMap k K))` (also written `algebraBaseMap k K`,
an abbreviation from `Langlands.GroupScheme.Torus.LatticeGalois`).

## Transport through isomorphisms

- `IsSolvableRadical.comp_iso`: if `IsSolvableRadical r` and `e : G ≅ G'`, then
  `IsSolvableRadical (r ≫ e.hom)`.

  Proof: closedness by `IsClosedSubgroup.comp_iso`; smoothness, connectedness and
  solvability concern `R` only and are unchanged. The image of `r ≫ e.hom` is the
  preimage under `e.inv` of the image of `r` (`SubgroupFunctor.range_comp_iso`), so
  it is normal by `IsNormal.comap`. For greatestness, a test subgroup `j : H ⟶ G'`
  gives `j ≫ e.inv : H ⟶ G`, which is closed and has normal image (again by
  `range_comp_iso` and `IsNormal.comap`); `hr.greatest` bounds its image by that of
  `r`, and `SubgroupFunctor.range_comp_mono` with `e.hom` transfers the bound back
  to `G'` after cancelling `e.inv ≫ e.hom`.

- `IsSolvableRadical.precomp_iso`: if `IsSolvableRadical r` and `e : R' ≅ R`, then
  `IsSolvableRadical (e.hom ≫ r)`.

  Proof: `e.hom ≫ r` and `r` have the same image
  (`SubgroupFunctor.range_iso_precomp`), so normality and greatestness are those of
  `r`. Closedness is `(IsClosedSubgroup.of_iso e).comp`; smoothness of `R'` follows
  from that of `R` because the underlying scheme map of `e` is an isomorphism
  over the base; connectedness transfers through the homeomorphism
  `Scheme.homeoOfIso`; solvability by `IsSolvableGroupScheme.of_iso`.

## Isomorphisms of ground fields

- `IsSolvableRadical.baseChange_ringEquiv`: for a ring isomorphism `f : k ≃+* K`
  and `[IsAffineHom G.X.hom]`, the base change of a solvable radical `r` along
  `b := Spec.map (CommRingCat.ofHom f.toRingHom)` is a solvable radical.

  Proof: let `a` be the spectrum map of `f.symm`, so `a ≫ b = 𝟙` and `a`, `b` are
  isomorphisms (`isIso_SpecMap_iff`). Closedness by `IsClosedSubgroup.baseChange`;
  smoothness from the pullback instance; connectedness by
  `RadicalFieldTransport.connectedSpace_map`; solvability by
  `IsSolvableGroupScheme.baseChange_of_bijective`; normality from
  `SubgroupFunctor.range_baseChangeHom` and `IsNormal.baseChange`. For greatestness,
  a test subgroup `j` over `K` is pulled back along `a` and moved into `G` with
  `baseChangeSectionIso b a ha G`; there it is a valid test subgroup (solvability
  again by `baseChange_of_bijective` for `f.symm`), so `hr.greatest` bounds its
  image, and `RadicalFieldTransport.range_le_of_section` turns this bound into the
  required bound over `K`.

## Galois transport

Here `k → K` is a field extension, `G` is a `k`-group with `[IsAffineHom G.X.hom]`,
and `r : R ⟶ (bc (algebraBaseMap k K)).obj G` is a subgroup of `G_K`. For
`σ : K ≃ₐ[k] K`, `radicalGaloisHom r σ` (from
`Langlands.GroupScheme.Rational.UnipotentRadicalGalois`, defined for any
inclusion) is the Galois translate of `r`: the base change of `r` along the
automorphism `galoisBaseMap k K σ` of `Spec K`, composed with the canonical
identification `descentBaseChangeIso` of the translated `G_K` with `G_K`.

- `IsSolvableRadical.galoisTransport`: if `IsSolvableRadical r`, then
  `IsSolvableRadical (radicalGaloisHom r σ)`. Proof: `baseChange_ringEquiv` for
  `σ.toRingEquiv`, then `comp_iso` with that identification.
- `IsSolvableRadical.range_galoisTransport`: in the same situation,
  `SubgroupFunctor.range (radicalGaloisHom r σ) = SubgroupFunctor.range r`. Proof:
  both are solvable radicals of `G_K`, so they have the same image
  (`IsSolvableRadical.range_eq`, from
  `Langlands.GroupScheme.Rational.SolvableRadicalComparison`).

## Reflection along a field extension

Here `k → K` is any field extension, `G` is a `k`-group with
`[IsAffineHom G.X.hom]`, `r : R ⟶ G`, and `b` is the induced `Spec K ⟶ Spec k`,
which is surjective, flat and quasi-compact (`fieldExtension_fpqc`).

- `IsSolvableRadical.greatest_of_baseChange`: if `(bc b).map r` is a solvable
  radical and `r` is a closed subgroup, then the image of every `k`-test subgroup
  `j : H ⟶ G` (closed, `H` smooth, connected, solvable, normal image) is contained
  in the image of `r`.

  Proof: by `SubgroupFunctor.le_range_of_baseChange_le` it suffices to compare the
  base-changed images, which are the images of the base-changed maps
  (`SubgroupFunctor.range_baseChangeHom`). The base change of `j` is a valid test
  subgroup over `K`: closed (`IsClosedSubgroup.baseChange`), smooth (pullback
  instance), connected (`connectedSpace_baseChange_of_smooth_affine`), solvable
  (`solvableFieldExtensionStatement`, the published proof that solvability of a
  smooth affine group is preserved by any base field extension) and with normal
  image (`IsNormal.baseChange`). So the greatestness of `(bc b).map r` applies.

- `IsSolvableRadical.of_baseChange`: if `(bc b).map r` is a solvable radical and
  `r` is a closed subgroup, then `IsSolvableRadical r`.

  Proof: smoothness and connectedness of `R` reflect by `smooth_of_baseChange` and
  `connectedSpace_of_baseChange`; solvability by
  `IsSolvableGroupScheme.of_baseChange` (from
  `Langlands.GroupScheme.Absolute.GeometricBorelBaseChange`; it uses that `R_K` is
  smooth and affine over `K`); normality by
  `SubgroupFunctor.isNormal_range_of_baseChange`; greatestness by
  `greatest_of_baseChange`.

## Published inputs used

| Lean name | Module |
| --- | --- |
| `IsSolvableRadical` | `Langlands.GroupScheme.Rational.LeviSubgroup` |
| `IsSolvableRadical.range_eq` | `Langlands.GroupScheme.Rational.SolvableRadicalComparison` |
| `IsClosedSubgroup.comp_iso`, `IsClosedSubgroup.comp` | `Langlands.GroupScheme.Rational.SplitRankTransport` |
| `IsClosedSubgroup.of_iso` | `Langlands.GroupScheme.Rational.SplitTorus` |
| `SubgroupFunctor.range_comp_iso` | `Langlands.GroupScheme.Rational.SplitUnipotentTransport` |
| `SubgroupFunctor.range_comp_mono` | `Langlands.GroupScheme.Rational.ParabolicAmbientTransport` |
| `SubgroupFunctor.IsNormal.comap` | `Langlands.GroupScheme.Dynamic.Functoriality` |
| `SubgroupFunctor.range_iso_precomp`, `smooth_of_baseChange`, `connectedSpace_of_baseChange`, `SubgroupFunctor.isNormal_range_of_baseChange` | `Langlands.GroupScheme.Rational.UnipotentRadicalProperties` |
| `RadicalFieldTransport.connectedSpace_map`, `RadicalFieldTransport.range_le_of_section`, `radicalGaloisHom` | `Langlands.GroupScheme.Rational.UnipotentRadicalGalois` |
| `IsSolvableGroupScheme.of_iso` | `Langlands.GroupScheme.Absolute.BorelTransport` |
| `IsSolvableGroupScheme.baseChange_of_bijective` | `Langlands.GroupScheme.Absolute.SolvableBijectiveBaseChange` |
| `IsSolvableGroupScheme.of_baseChange` | `Langlands.GroupScheme.Absolute.GeometricBorelBaseChange` |
| `solvableFieldExtensionStatement` | `Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof` |
| `IsClosedSubgroup.baseChange`, `SubgroupFunctor.range_baseChangeHom`, `SubgroupFunctor.IsNormal.baseChange` | `Langlands.GroupScheme.SubgroupBaseChange` |
| `SubgroupFunctor.le_range_of_baseChange_le` | `Langlands.GroupScheme.SubgroupFunctor.FpqcDescent` |
| `baseChangeSectionIso` | `Langlands.GroupScheme.Torus.SplitDescent` |
| `algebraBaseMap`, `galoisBaseMap`, `galoisBaseMap_over` | `Langlands.GroupScheme.Torus.LatticeGalois` |
| `descentBaseChangeIso` | `Langlands.GroupScheme.CocharacterTransport` |
| `fieldExtension_fpqc` | `Langlands.GroupScheme.BaseChangeReflection` |
| `connectedSpace_baseChange_of_smooth_affine` | `Langlands.GroupScheme.GeometricConnectedness` |

These modules are reached through the seven imports of this file. The module
sets `backward.isDefEq.respectTransparency false`,
`backward.isDefEq.respectTransparency.types false`,
`backward.defeqAttrib.useBackward true` and `maxHeartbeats 800000`, as the
unipotent-radical modules it mirrors do.

## Provenance

Internal: these are formalization lemmas about the Library's representation of a
radical by a closed inclusion. They have no separate literature source. The
mathematical content (a solvable radical is preserved by isomorphisms and by
Galois automorphisms, and the radical property can be checked after a field
extension) is used in J. S. Milne, *Algebraic Groups* (2017), proof of
Proposition 19.1, printed p. 397 (registered as `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
