# Cocharacter data

Module `Langlands.GroupScheme.Torus.CocharacterDatum`, namespace
`Langlands.GroupScheme.CocharacterDatum`.

This module sets up the bookkeeping for torus cocharacter detection
(`Langlands.GroupScheme.Torus.CocharacterDetection`). A homomorphism from the
diagonalizable group `D(Λ)` to a commutative group scheme `Z` is the same as a
point of `Z` over the group algebra `k[Λ]` that is multiplicative. The module
works with such points over `S[Λ]` for arbitrary `k`-algebras `S`, so that they
can be moved between coefficient rings (descent), and turns a multiplicative
point over `k[Λ]` into an actual homomorphism `D(Λ) ⟶ Z`.

Setting: `k` is a field, `Z` a commutative group scheme over `Spec k` (affine
where stated), `Λ` an additive commutative group, and `S`, `S'` are
`k`-algebras. Points of `Z` over `S` are the `Lie.AffinePoints Z.toGrp S`
(morphisms from `Spec S` over `Spec k`); for a `k`-algebra map `f`,
`Lie.affineMap Z.toGrp f` is the induced map on points. `S[Λ]` is
`AddMonoidAlgebra S Λ`.

## Definitions

- `coordAlgebra G`: the chosen coordinate algebra `AffineCoordinates.algebra G`
  of an affine group scheme `G`; `coordIso G` identifies its spectrum with the
  underlying scheme of `G`.
- `coord x`: for a point `x` of `G` over `S`, the `k`-algebra map
  `coordAlgebra G → S` that it corresponds to.
- `monomial S γ`: the monomial `X^γ`, as a unit of `S[Λ]`.
- `diagHom Λ`: the diagonal `γ ↦ (γ, γ)` from `Λ` to `Λ × Λ`.
- `expMap S g`: for an additive map `g : Λ →+ Λ'`, the map on points
  from `S[Λ]` to `S[Λ']` induced by `X^γ ↦ X^(g γ)`.
- `coeffMap f`: for a `k`-algebra map `f : S → S'`, the map on points from
  `S[Λ]` to `S'[Λ]` induced by applying `f` to coefficients.
- `IsMult p`: the point `p` over `S[Λ]` is multiplicative, meaning
  `expMap (diagHom Λ) p = expMap inl p * expMap inr p` over `S[Λ × Λ]`.
  For `S = k` this says that the morphism `D(Λ) → Z` given by `p` is a group
  homomorphism.
- `IsDatum χ m p` (structure with fields `mult` and `value`): `p` is
  multiplicative and the character `χ` of the character lattice of `Z` takes
  the value `monomial S m` on `p`. We call `p` a cocharacter datum of weight
  `m` for `χ`.
- `toFunctor S`: points of `Z` over `S`, viewed in the corepresented point
  functor `AffineCoordinates.functor Z.toGrp`.
- `specialize p S c`: for a point `p` over `k[Λ]` and a character
  `c : Multiplicative Λ →* Sˣ`, the point over `S` obtained along the algebra
  map `k[Λ] → S`, `X^γ ↦ c γ` (`Diagonalizable.lift`).
- `natOfMult p hp`: for multiplicative `p`, the natural transformation
  `Hom(Λ, Sˣ) → Z(S)`, `c ↦ specialize p S c`, from the point functor of
  `D(Λ)` (`Diagonalizable.functor`) to that of `Z`.
- `homOfMult p hp`: the group scheme homomorphism
  `(Diagonalizable.groupScheme k Λ).toGrp ⟶ Z.toGrp` obtained from
  `natOfMult p hp` by `Corepresented.groupSchemeMap`, followed by the
  identification `AffineCoordinates.groupSchemeIso`.

## Statements

Coordinates (`G` affine):

- `map_coord`, `coord_injective`: a point is recovered from its coordinate
  map.
- `coord_affineMap`: `coord (f_* x) = coord x ≫ f`.
- `affineMap_injective`: if `f` is injective, so is `f_*` on points.
- `exists_affineMap_eq` (descent of points along an injective map): if all
  coordinate values of a point over `S'` lie in the image of an injective
  `f : S → S'`, the point is `f_* y` for a point `y` over `S`.

Group algebras:

- `monomial_val`, `monomial_add`, `monomial_zero`, `monomial_nsmul`,
  `monomial_injective` (for nontrivial `S`).
- `mapAlgHom_comp_mapDomainAlgHom`, `mapAlgHom_mapDomainAlgHom`: changing
  coefficients commutes with changing exponents.
- `units_map_mapAlgHom_monomial`: coefficient change sends `X^γ` to `X^γ`.
- `mapAlgHom_injective`: coefficient change along an injective map is
  injective.
- `exists_mapAlgHom_eq`: an element of `S'[Λ]` all of whose coefficients lie
  in the image of an injective `f` comes from `S[Λ]`.

Character values:

- `characterValue_affineMap`: `χ(f_* t) = f(χ(t))`.
- `characterValue_mul`, `characterValue_one`: `χ` is multiplicative on points.

Cocharacter data:

- `coeffMap_expMap`: coefficient and exponent changes commute on points.
- `IsMult.coeff_map`, `IsDatum.coeff_map`: data are preserved by coefficient
  change.
- `IsMult.of_coeff_map`, `IsDatum.of_coeff_map` (`Z` affine): data are
  reflected by coefficient change along an injective map.
- `isMult_one`, `IsMult.mul`, `IsMult.inv`, `isDatum_one`, `IsDatum.mul`,
  `IsDatum.prod`: multiplicative points form a subgroup, and weights add
  under products (finite products in `IsDatum.prod`).
- `IsMult.expMap_add`: for multiplicative `p`,
  `expMap (g₁ + g₂) p = expMap g₁ p * expMap g₂ p`.
- `IsMult.expMap_nsmul`: for multiplicative `p`, `expMap (n • id) p = p ^ n`.
- `expMap_nsmul_injective` (`Z` affine, `Λ` torsion-free, `n ≠ 0`):
  `expMap (n • id)` is injective on points.

From multiplicative points to homomorphisms (`Z` affine):

- `toFunctor_injective`, `toFunctor_naturality`, `toFunctor_comp_hom`.
- `lift_mapDomain`, `specialize_mul` (for multiplicative `p`, specialization
  turns products of characters into products of points),
  `specialize_naturality`, `specialize_monomialUnits` (specializing along the
  universal character `γ ↦ X^γ` gives back `p`).
- `id_comp_homOfMult`: the universal point of `D(Λ)` is sent by
  `homOfMult p hp` to `p`.
- `characterRestrict_homOfMult_ne_zero`: if `p` is a datum of weight `m ≠ 0`
  for (the lattice image of) a rational character `χ`, then
  `characterRestrict (homOfMult p hp.mult) χ ≠ 0`.
- `characterRestrict_iso_ne_zero`: restriction along an isomorphism of group
  schemes sends nonzero characters to nonzero characters.
- `exists_gm_characterRestrict_ne_zero`: a datum of nonzero weight
  `m : PUnit → ℤ` over `k[PUnit → ℤ]` for `χ` gives
  `φ : (Gm (Spec k)).toGrp ⟶ Z.toGrp` with `characterRestrict φ χ ≠ 0`.

## Proofs

- Coordinates. `coord x` is the preimage of `x ≫ (coordIso G).inv` under the
  fully faithful functor `algSpec`. Naturality `coord_affineMap` follows by
  cancelling the isomorphism `coordIso G`. For `exists_affineMap_eq`, the
  coordinate map of the point over `S'` is corestricted to the range of `f`
  and composed with the inverse of `f : S ≃ f.range`; its spectrum is the
  required point.
- Group algebras. `monomial_injective` compares the coefficient at `γ` of the
  two monomials. `exists_mapAlgHom_eq` builds the preimage with
  `Finsupp.onFinset` on the support of `x`, choosing preimages of the
  coefficients.
- Character values. `characterValue_affineMap` unfolds `Lie.characterValue`
  through `Gm.affinePointsEquiv` and uses naturality of `Gm.pointsEquiv` and
  of `Scheme.ΓSpecIso`; multiplicativity is `MonObj.mul_comp` and
  `MonObj.one_comp`.
- Data. The coefficient lemmas rewrite with `coeffMap_expMap` and the fact
  that `Lie.affineMap` is a group homomorphism; the reflection lemmas use
  `affineMap_injective` and `mapAlgHom_injective`. `IsMult.expMap_add` applies
  `expMap (g₁.coprod g₂)` to the multiplicativity identity and computes the
  three composites. `IsMult.expMap_nsmul` is induction on `n`; the case
  `n = 0` uses `expMap 0 p = expMap 0 p * expMap 0 p`. Injectivity of
  `expMap (n • id)` is injectivity of `mapDomain` along the injective map
  `γ ↦ n • γ`.
- Construction. `specialize_mul` applies the specialization along the
  character `(γ, δ) ↦ c γ · c' δ` of `Λ × Λ` to the multiplicativity identity.
  Naturality of `natOfMult` is `specialize_naturality` plus
  `toFunctor_naturality`. `id_comp_homOfMult` follows from
  `Corepresented.groupSchemeMap_affinePoints`, the identification of the
  universal character of `D(Λ)` with the monomials, and
  `specialize_monomialUnits`.
- `characterRestrict_homOfMult_ne_zero`. If the restriction were zero, `χ`
  would take the value `1` on the image of the universal point, which is `p`
  by `id_comp_homOfMult`; but `χ(p) = X^m`, and `X^m = 1 = X^0` forces
  `m = 0` by `monomial_injective`.
- `exists_gm_characterRestrict_ne_zero` takes
  `φ = gmIso.hom ≫ splitIso.inv ≫ homOfMult p`, where `splitTorus.gmIso`
  identifies `𝔾_m` with the split torus of rank one and
  `Diagonalizable.splitIso` the split torus with `D(PUnit → ℤ)`. Restriction
  along a composite is the composite of restrictions (`characterRestrict_comp`),
  and restriction along an isomorphism preserves nonvanishing
  (`characterRestrict_iso_ne_zero`, via `e.inv_hom_id`).

## Provenance

Internal. The correspondence between homomorphisms `D(Λ) ⟶ Z` and
multiplicative points over `k[Λ]` is the standard description of
diagonalizable groups through their group algebras; here it is implemented
through the Library's corepresented group schemes
(`Corepresented.groupSchemeMap`) and `Diagonalizable.groupScheme`, and only
the direction from multiplicative points to homomorphisms is proved. Coefficient change, descent of points along
injective maps and the cocharacter datum bookkeeping are auxiliary
constructions designed by Worker 1001 for the proof of torus cocharacter
detection in task 6d0882ee; they are not quoted from a source.
