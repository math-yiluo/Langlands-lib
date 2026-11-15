# Field coordinates on a relative root group from an orthogonal orbit of simple roots

Module `Langlands.GroupScheme.Rational.OrthogonalOrbitRootCoordinates`, namespaces
`Langlands.GroupScheme.LinkedRootParametrization` and `Langlands.GroupScheme.SplitPinning`.

This module continues `GroupScheme.Rational.OrthogonalOrbitSpecialLinear`. That module
builds a homomorphism `fieldSL2 : SL₂(E) →* G(k)` from a Galois-stable set `O` of pairwise
orthogonal simple roots of a split pinning over a finite Galois extension `K/k`. Here we
prove three things about `fieldSL2`:

- its upper and lower unipotents lie in the relative root groups `U_{bS}(k)` and
  `U_{-bS}(k)`, for a relative root `bS` of a torus `S` to which every root of `O`
  restricts;
- rational torus points act on these unipotents through field-valued functions;
- under two explicit hypotheses, the maps `t ↦ fieldSL2 (upper t)` and
  `t ↦ fieldSL2 (lower t)` are isomorphisms from `E` onto `U_{bS}(k)` and `U_{-bS}(k)`.

The two hypotheses are explicit arguments, not proved here:

- (product) every point of the root group of `bS` over `K` is a positive orbit product
  `orbitXp c`, and its coordinates on `O` are unique (and the same for `-bS` with
  `orbitXm`);
- (fields) every Galois-equivariant family of scalars on `O` is `a ↦ τ a t` for some
  `t ∈ E` (`FamiliesFromField`).

The product hypothesis is the content of the separately submitted statement
`Langlands.Geometry.Building.SplitRelativeRootGroupProductStatement` (Borel–Tits 1965,
Th. 3.17), specialized to `O`. The fields hypothesis is the standard description of
`E` through its embeddings into `K`. No literature theorem is imported; all statements
are internal.

## Rational torus action on linked root points

Namespace `LinkedRootParametrization`. Here `X : LinkedRootParametrization i α ν` for
`i : T ⟶ G` over a field `k`.

- `charValue_base`: at the base point `Spec k`, the global character value
  `VectorGroup.charValue χ` at `z` is the image under `secMap k` of the rational value
  `rationalCharacterEval χ z`.
- `conj_xpPoint`: `z · xpPoint c · z⁻¹ = xpPoint (α(z) c)` for `z ∈ T(k)`.
- `conj_xmPoint`: `z · xmPoint c · z⁻¹ = xmPoint ((-α)(z) c)`.

Both are `positive_equivariant` / `negative_equivariant` at the base point, rewritten with
`charValue_base`.

## Galois transport and torus action on orbit products

Namespace `SplitPinning`. The setting is the one of section `Galois` of
`OrthogonalOrbitSpecialLinear`: fields `k ⊆ K`, a split pinning `p` of `G_K` whose torus
is identified with `T_K` by `eT` (with `hT`), Galois-compatible simple-root
parametrizations `x` (`hx`, `hroot`, permutation `ρ`), and a Galois-stable (`hOs`),
pairwise orthogonal (`hO`) finite set `O` of simple roots.

- `galoisFamily σ c`, the family `a ↦ σ (c ((ρ σ)⁻¹ a))`; `galoisFamily_apply`:
  its value at `ρ σ a` is `σ (c a)`.
- `orbitXp_congr`, `orbitXm_congr`: the Library orbit products `orbitXp`, `orbitXm`
  depend only on the coordinates on `O`.
- `rationalConjugate_orbitXp`, `rationalConjugate_orbitXm`: applying `σ ∈ Gal(K/k)` to the
  coefficients of an orbit product with coordinates `c` gives the orbit product with
  coordinates `galoisFamily σ c`. Proof: `RankOneRelation.map_prodHom_of_perm` with `ρ σ`
  restricted to `O`, then `RootMapsGaloisCompatible.rationalPoint` (positive) and
  `RootMapsGaloisCompatible.negPointFamily_rationalConjugate` (negative).
- `conj_orbitXp`, `conj_orbitXm`: for `w ∈ p.torus(K)`, conjugation by the image of `w`
  multiplies the coordinate at `a` by the value at `w` of the root of `a` (respectively of
  its negative). Proof: `map_prodHom_of_perm` with the identity permutation and
  `conj_xpPoint` / `conj_xmPoint`.
- `map_baseChange_map`: on `K`-points, `i_K` equals the pinning inclusion after the
  inverse of `eT`. This follows from `hT` and `eT.inv ≫ eT.hom = 𝟙`.

## Coordinates

Section `Coordinates` adds `[FiniteDimensional k K] [IsGalois k K]`, a field `E` over `k`
and embeddings `τ : simple roots → (E →ₐ[k] K)` with `τ (ρ σ a) = σ ∘ τ a` for `a ∈ O`
(`hτ`), as in `fieldSL2`.

- `FamiliesFromField k K p O τ`: the Prop saying that every family `c` with
  `c (ρ σ a) = σ (c a)` for `a ∈ O` has the form `c a = τ a t` on `O` for some `t ∈ E`.

It further fixes a torus `S` over `k` with `iS : S ⟶ G`, a morphism `g : S_K ⟶ p.torus`
with `g ≫ p.inclusion = (iS)_K` (`hg`), a character `bS ≠ 0` of `S` (`hb0`) with
`g ≫ root a = (bS)_K` for every `a ∈ O` (`hres`), `S` split (`hS`), and `G` smooth.

- `fieldSL2_upper_mem`, `fieldSL2_lower_mem`: `fieldSL2 (upper t) ∈ U_{bS}(k)` and
  `fieldSL2 (lower t) ∈ U_{-bS}(k)`. Proof: membership can be tested after scalar extension
  to `K` (`rationalExtend_mem_rootGroupPoints_iff`, which needs `hS`, `hb0` and
  smoothness), where the point is an orbit product (`rationalExtend_fieldSL2_upper` /
  `_lower`), and orbit products lie in the root group by
  `orbitXp_mem_rootGroupPoints` / `orbitXm_mem_rootGroupPoints`.
- `fieldSL2_upper_injective`, `fieldSL2_lower_injective`: if orbit-product coordinates are
  unique on `O` (`huniq`) and `O` is nonempty (`a₀ ∈ O`), then `t ↦ fieldSL2 (upper t)`
  and `t ↦ fieldSL2 (lower t)` are injective. Proof: `rationalExtend` the equation,
  compare coordinates at `a₀` and use injectivity of `τ a₀`.
- `exists_fieldSL2_upper_eq`, `exists_fieldSL2_lower_eq`: under the product hypothesis
  (`hprod`, `huniq`) and `FamiliesFromField`, every point of `U_{bS}(k)` (resp.
  `U_{-bS}(k)`) is `fieldSL2 (upper t)` (resp. `fieldSL2 (lower t)`). Proof: the scalar
  extension `g_K` is an orbit product `orbitXp c`. As `g_K` is Galois-fixed,
  `rationalConjugate_orbitXp` and uniqueness show that `c` is Galois-equivariant on `O`.
  `FamiliesFromField` then gives `t`, and injectivity of `rationalExtend`
  (`rationalExtend_injective_of_isAffineHom`) concludes.
- `conj_fieldSL2_upper`, `conj_fieldSL2_lower`: let `χ : T(k) → E` be any function with
  `τ a (χ z) = root a (w z)` for `a ∈ O` (respectively `= (-root a)(w z)`), where `w z` is
  `z` extended to `K` and moved to `p.torus` by `eT⁻¹`. Then
  `i(z) · fieldSL2 (upper t) · i(z)⁻¹ = fieldSL2 (upper (χ z · t))`, and the same for
  `lower`. Proof: after `rationalExtend` (injective), this is
  `GaloisPointComparison.rationalExtend_map`, `map_baseChange_map`, `conj_orbitXp`
  (resp. `conj_orbitXm`) and `orbitXp_congr`.
- `upperRootHom`, `lowerRootHom : Multiplicative E →* U_{±bS}(k)` send `t` to
  `fieldSL2 (upper t)`, resp. `fieldSL2 (lower t)`. They are homomorphisms by
  `Matrix.SpecialLinearGroup.transvection_add`. The `_apply` lemmas are definitional.
- `upperRootEquiv`, `lowerRootEquiv : Multiplicative E ≃* U_{±bS}(k)`:
  `MulEquiv.ofBijective` of the above. Their arguments are the product hypotheses for
  `bS` (`hprodp`, `huniqp`) or for `-bS` (`hprodm`, `huniqm`), together with
  `hfam : FamiliesFromField` and `ha₀ : a₀ ∈ O`. Bijectivity is the injectivity and
  existence lemmas above. `upperRootEquiv_apply` and `lowerRootEquiv_apply` are
  definitional.

The module proves neither the product hypothesis nor `FamiliesFromField`. It does not
build the character `χ` from a rational character of `T` over `E`, and it does not
choose `O`, `E` or `τ`. Those are later steps.
