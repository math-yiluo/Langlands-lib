# Split components of the Levi `L'` of a geometric-lemma intersection datum

Fix a field `k` with a topology, a group scheme `G` over `k`, represented
parabolics `P = M N` and `Q = L U` of `G`, and a point `z ∈ G(k)`. Let `D` be a
`GeometricLemmaIntersectionDatum` for `z`
(`Langlands/Representation/Geometric/RepresentedGeometricLemmaStatement.lean`).
It provides the Levi `L' = L ∩ z⁻¹Mz` of the parabolic `Q' = L ∩ z⁻¹Pz` of `L`,
the Levi `M' = M ∩ zLz⁻¹` of `M`, an isomorphism `φ : L' ≅ M'` whose composite
into `G` is conjugation by `z`, and a split torus `t : torus → M'` that is a
maximal split torus of `G`.

This internal supporting module shows that `L'` contains a maximal split torus of
`G`. As a consequence, every split component `A_L` of `L` lies in `L'` and factors
through a split component `A_{L'}` of `L'`.

## Declarations

All declarations are in the namespace
`Langlands.Aubert.General.RepresentedParabolic.GeometricLemmaIntersectionDatum`.

- `leviTorus D : torus ⟶ L'` is `t ≫ φ⁻¹`, the torus of `D` moved into `L'`.
- `leviTorus_comp`: the composite of `leviTorus` into `G` equals the composite of
  `t` into `G` followed by `(innerIso z)⁻¹`, that is, conjugation by `z⁻¹`.
- `isMaximalSplitTorus_leviTorus_comp`: `leviTorus` followed by the inclusion
  `L' → G` is a maximal split torus of `G`.
- `isClosedSubgroup_lQ'_q'` and `isClosedSubgroup_lQ'_q'_lQ_q`: the inclusions
  `L' → L` and `L' → G` are closed subgroups.
- `isClosedSubgroup_leviTorus`: `leviTorus` is a closed subgroup of `L'`.
- `exists_factor_leviTorus`: every central split torus of `L'` factors through
  `leviTorus`.
- `exists_isCentralSplitTorus_factor`: every central split torus `a : A → L`
  factors as `g ≫ (L' → L)` for some `g : A → L'`, and `g` is a central split
  torus of `L'`.
- `exists_isSplitComponent_factor`: for every split component `a : A_L → L`
  there are a split component `a' : A_{L'} → L'` and a morphism
  `f : A_L → A_{L'}` with `f ≫ a' ≫ (L' → L) = a`.

## Proofs

- `leviTorus_comp` rewrites the compatibility field `φ_comp`,
  `φ.hom ≫ (M' → G) = (L' → G) ≫ innerIso z`, into
  `φ.inv ≫ (L' → G) = (M' → G) ≫ (innerIso z)⁻¹` with `Iso.inv_comp_eq` and
  `Iso.eq_comp_inv`, and then precomposes with `t`.
- `isMaximalSplitTorus_leviTorus_comp` applies `IsMaximalSplitTorus.comp_iso`
  to the field `isMaximalSplitTorus` and the automorphism `(innerIso z)⁻¹`, and
  rewrites with `leviTorus_comp`.
- The closed-subgroup lemmas compose the closed-subgroup properties of the Levi
  and parabolic inclusions (`IsRationalLeviSubgroup.isClosedSubgroup`,
  `IsParabolicSubgroup.isClosedSubgroup`, `IsClosedSubgroup.comp`).
  `isClosedSubgroup_leviTorus` cancels the closed inclusion `L' → G` with
  `IsClosedSubgroup.of_comp`.
- `exists_factor_leviTorus` is `IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus`
  for the ambient group `G`, the closed inclusion `L' → G` and the maximal split
  torus `leviTorus`.
- `exists_isCentralSplitTorus_factor` applies the same lemma with the ambient
  inclusion `L → G` and the maximal split torus `leviTorus ≫ (L' → L)`; this
  gives `g' : A → torus` with `g' ≫ leviTorus ≫ (L' → L) = a`, and
  `g := g' ≫ leviTorus`. The factor `g` is a closed subgroup of `L'`
  (`IsClosedSubgroup.of_comp`), it is a split torus because `a` is, and it is
  central in `L'` by `IsCentral.of_comp`. The last step uses that `L' → L` is a
  monomorphism (`IsClosedSubgroup.mono`, `Over.mono_of_mono_left`).
- `exists_isSplitComponent_factor` takes the central split torus `g` of `L'`
  from the previous lemma. It obtains a split component `a'` of `L'` from
  `exists_isSplitComponent_of_factor`, using the closed split torus `leviTorus`,
  through which every central split torus of `L'` factors. It then factors `g`
  through `a'` with `IsSplitComponent.exists_factor`.

## Provenance and scope

This is derived content for the proof of Renard VII.2.2
(`LeviInductionNormalizedTemperedStatement`). On PDF p.234 Renard applies
VII.1.1 to the pieces of the geometric lemma VI.5.1: a character of `A_L` is
restricted from a character of `A_{L ∩ w⁻¹Mw}`. This uses
`A_L ⊆ A_{L ∩ w⁻¹Mw}`, which holds because his representatives `w` normalize a
maximal split torus. The intersection datum records that property as the
maximal split torus field of `M'`, and this module moves it to `L'` and derives
the factorization of `A_L`. The module proves no statement about representations, and it
does not prove that the factor `f` is unique.
