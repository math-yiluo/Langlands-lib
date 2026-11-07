# Weyl normalization of opposite root groups on field fibres

Module `Langlands.GroupScheme.Reductive.LocalWeylNormalizationField`.

This module proves `FieldWeylNormalizationStatement`, stated in the module
`LocalWeylNormalizationStatement` (theorem `fieldWeylNormalization`). It is the field half
of the Weyl normalization step in the proof of the Isomorphism Theorem over a reduced
local ring. The ring half is Worker 712's `localWeylNormalization_of_field`.

Notation is that of `LocalSplitCell`: `Ga k` is the additive group, `rootPoint u Z c` is
the value `u(c)`, and `weylPoint u v = v(-1) u(1) v(-1)`. `pt` is the base `Spec k`, regarded
as the terminal object over `Spec k`.

## Main results

- `exists_fieldWeylNormalization`. Let `G` be a connected reductive group over a field `k`
  with affine structure morphism, and `i : 𝔾ₘ^I ⟶ G` a maximal torus. Let `P` be a reduced
  coordinate root datum whose field realization is the root datum of `(G, i)`. Let `a` be a
  root, `u` a root parametrization for `P.root a`, and `v` one for
  `P.root (P.reflectionPerm a a) = -P.root a`. Then there is `d ≠ 0` in `k` such that
  1. the pair `(u, scaleHom d ≫ v)` satisfies the rank-one relation
     `RootCell.RelationOver i a^∨ u (scaleHom d ≫ v) Z` on every test scheme `Z`, with `a^∨`
     the cocharacter of `P.coroot a`;
  2. `weylPoint u (scaleHom d ≫ v)` is a Weyl point for `P.reflection a`.
- `fieldWeylNormalization : FieldWeylNormalizationStatement`. For the data over a ring `R`
  and a field `k` with an `R`-algebra structure, it applies `exists_fieldWeylNormalization` to
  the base change. The inputs are the Library's `IsReductive.isConnectedReductive_algebraMap`,
  `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`, `IsFibrewiseRootDatumOf.field` and
  `LocalSplitBigCell.isRootParametrization_baseChangeRoot`.

## Proof of `exists_fieldWeylNormalization`

1. **A linked pair.** The Library's `exists_monic_rootRankOneRelations` gives monic maps
   `xp, xm : 𝔾ₐ ⟶ G`. They are equivariant for `a` and `-a` and satisfy the rank-one
   relation with the coroot `a^∨`. By `IsTorusEquivariant.represents_root`, both represent
   the whole root subgroups. The needed "no higher roots" condition comes from
   `hasNoHigherRoots_fieldRealization`, since `P` is reduced.
2. **Comparison with `u` and `v`** (`exists_eq_scaleHom_comp`). Two equivariant
   parametrizations `x, w` of the same root subgroup differ by a nonzero rescaling,
   `x = scaleHom l ≫ w`. The comparison isomorphism `isoOfIsRepresentedBy` commutes with the
   weight action. So it is linear in the coordinate (the Library's
   `RelativeRoot.isCoordinateLinear_of_weightCoordinates`), and a coordinate-linear
   endomorphism of `𝔾ₐ` is `scaleHom l` (`exists_eq_scaleHom`). Here `l ≠ 0` because
   `scaleHom 0` is not a monomorphism (`ne_zero_of_mono_scaleHom`). This gives
   `xp = scaleHom l ≫ u` and `xm = scaleHom m ≫ v`.
3. **Transfer of the relation** (`relationOver_scaleHom`). The relation for
   `(scaleHom l ≫ u, scaleHom m ≫ v)` is the relation for `(u, scaleHom (l m) ≫ v)`: substitute
   `X = X'/l` and `Y = l Y'`, so that `1 + XY = 1 + X'Y'`. Set `d = l m` and
   `v' = scaleHom d ≫ v`. By `IsRootParametrization.scale`, `v'` is again a root
   parametrization of `-a`.
4. **The normalizing opposite pair of `u(1)`.** The Library's
   `hasOppositeFactorPairs_of_rootDatum` gives points `p₁, p₂` of the root subgroup of `-a`
   such that `p₁ u(1) p₂` normalizes the torus. The key lemma is
   `one_add_mul_eq_zero_of_isOppositeFactorPair`: if `(p₁, v'(z))` is such a pair for
   `u(X) ≠ 1`, then `1 + Xz = 0`. Otherwise `w = 1 + Xz` is a unit, and the relation gives
   `u(X) v'(z) = v'(z/w) t u(X/w)` with `t = a^∨(w)` in the torus. Then `t⁻¹ p₁ u(X) v'(z)`
   is a normalizing point that is a product of a point of `U_{-a}` and a point of `U_a`. By
   the Library's `normalizer_eq_one_of_mul_opposite` it is `1`, so `p₁ u(X) v'(z) = t`
   centralizes the torus. This contradicts `IsOppositeFactorPair.weylAction_ne_self`.
   Applied to `u(1)`, the lemma gives `p₂ = v'(-1)`. Applied to the inverse pair
   `(p₂⁻¹, p₁⁻¹)` of `u(-1)`, it gives `p₁ = v'(-1)`. So `(v'(-1), v'(-1))` is the pair
   (`isOppositeFactorPair_weylPoint`), and `weylPoint u v'` normalizes the torus.
5. **The action.** By `IsOppositeFactorPair.coroot_spec`, `weylPoint u v'` acts on
   characters by `χ ↦ χ - ⟨χ, h⟩ a` for a cocharacter `h` with `⟨a, h⟩ = 2`. Since the Weyl
   image is finite (`splitTorusWeylImageFinite`), the Library's
   `IsRootDatumOf.coroot_eq_of_weylAction_of_finite_weylImage` gives `h = a^∨`. So the action
   on the exponent characters is `P.reflection a`
   (`fieldRealization_reflection_exponentCharacter`). By `splitTorus.eq_exponentCommIso_symm`,
   the normalizing torus automorphism is the exponent automorphism of `P.reflection a`, which
   is an involution. `isWeylPoint_of_isNormalizingPoint` converts this into `IsWeylPoint`.

## Auxiliary lemmas

- `scalarPoint_add`, `rootPoint_add`, `rootPoint_neg`, `comp_eq_rootPoint` and
  `scalarPoint_comp_eq_rootPoint` compute values of maps out of `𝔾ₐ`.
- `toUnit_left` and `baseScalar_ΓSpecIso_hom` relate the structure map of a test scheme over
  `Spec k` to pullback from the base point.
- `exists_rootPoint_eq`: every point of the represented root subgroup is a value of `v`.
- `isWeylPoint_of_isNormalizingPoint`, over any ring, is the converse of
  `IsWeylPoint.isNormalizingPoint`.

## Provenance

The statement is Conrad, *Reductive group schemes* (2014), Cor. 5.1.9 (PDF pp. 140-141), over a
field, in `𝔾ₐ`-coordinates. Parts (1) and (4) of the corollary describe the Weyl element
`w_a(X) = exp_a(X) exp_{-a}(-X^{-1}) exp_a(X)` and its inverse `w_{-a}(X^{-1})` for dual
sections. The proof here is internal to this formalization. Conrad reduces to `SL₂` and
`PGL₂`. Here, instead, the Library's linked rank-one parametrizations and normalizing opposite
pairs over a field (Conrad–Gabber–Prasad C.2.24) identify the normalized pair and its Weyl
element directly.
