# Isogeny sections of surjections of tori: proof

`Langlands.GroupScheme.torusSurjectionIsogenySection` proves
`Langlands.GroupScheme.TorusSurjectionIsogenySectionStatement.{u}` at an
arbitrary universe `u`. Its type is exactly the statement. It uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

Given a field `k`, commutative tori `B` and `C` over `Spec k`, and a
homomorphism `q : B.toGrp ⟶ C.toGrp` whose underlying scheme map is
surjective, the theorem gives a positive natural number `n` and a
homomorphism `s : C.toGrp ⟶ B.toGrp` with
`s ≫ q = multiplication C.toGrp n`.

The proof does not use Maschke's theorem over `ℚ`, which the statement's
Markdown suggests. It builds an integral retraction directly, using a Gram
matrix and its adjugate, and then averages it over the Galois group. The
resulting `n` is `(|Gal(L/k)| · det(AᵀA))²`, where `A` is the matrix of the
character map.

## Helper lemmas (namespace `Langlands.GroupScheme.TorusSurjectionIsogenySection`)

### Integral linear algebra (section `Algebra`)

- `exists_leftInverse_zsmul_of_injective`. Let `i : M →ₗ[ℤ] N` be an
  injective map of finite free `ℤ`-modules. Then some `r` and some nonzero
  integer `m` satisfy `r (i x) = m • x`. Proof: choose bases. Let `A` be the
  matrix of `i` and `G = Aᵀ A` its Gram matrix. If `A v = 0`, then
  `i (bM.equivFun.symm v) = 0` by `LinearMap.toMatrix_mulVec_repr`, so
  `v = 0` by injectivity. If `det G = 0`, some `v ≠ 0` has `G v = 0`
  (`Matrix.exists_mulVec_eq_zero_iff`). Then
  `(A v) ⬝ᵥ (A v) = v ⬝ᵥ (G v) = 0`, which forces `A v = 0` over the ordered
  ring `ℤ` (`dotProduct_self_eq_zero`). That is a contradiction. So
  `m = det G ≠ 0`, and `r` is the linear map with matrix `adj(G) Aᵀ`. Its
  composite with `i` has matrix `adj(G) G = det G • 1`
  (`Matrix.adjugate_mul`, `Matrix.toLin_mul`).
- `exists_equivariant_leftInverse_of_leftInverse`. Let a finite group `G`
  act on `M` and `N` by `ℤ`-representations, and let `i` be equivariant.
  If `r₀ ∘ i = m • id`, then the average `r = Σ_g ρM g ∘ r₀ ∘ ρN g⁻¹` is
  equivariant (reindex the sum by `g ↦ h g`) and satisfies
  `r ∘ i = (|G| · m) • id`.
- `exists_equivariant_retraction` combines the two. With
  `d = |G| · m ≠ 0`, the map `d • r` is still equivariant and satisfies
  `(d • r) ∘ i = (d.natAbs · d.natAbs) • id`, where `d.natAbs² = d² > 0`.
  This gives a positive natural number `n`.

### Characters (section `Geometry`)

- `characterLattice_free_finite`. The character lattice of a split torus over
  a field is a finite free `ℤ`-module. It is transported from `J → ℤ` along
  the split isomorphism, using `characterLattice.congr` and
  `splitTorus.characterLatticeEquiv`.
- `pullback_injective_of_surjective`. Let `f : T ⟶ T'` be a homomorphism of
  commutative group schemes over a field, with surjective underlying scheme
  morphism and with `T'` reduced. Then `characterLattice.pullback f` is
  injective. If `f ≫ ψ = 0`, then `ψ` and the trivial character agree after
  precomposition with the dominant morphism `f`. Since `Gm` is affine, hence
  separated, over the base (`isSplitTorus_gm.isAffineHom`), Mathlib's
  `ext_of_isDominant_of_isSeparated` gives equality of the underlying scheme
  morphisms. So `ψ = 0`.
- `baseChange_map_zsmul_id`. Base change sends `n • 𝟙 C` to `n • 𝟙` of the
  base change. Both sides are `multiplication _ n`, so this is
  `multiplication_baseChange`.

## Main proof

1. **Common splitting field.** `IsTorus.commonFiniteGaloisSplitting` gives a
   finite Galois extension `L / k` over which `B_L` and `C_L` are split tori.
   Here `bc = CommGroupScheme.baseChange (algebraBaseMap k L)`.
2. **Character map.** Let `q' = Additive.ofMul q : B ⟶ C` in
   `CommGroupScheme`. Set
   `i = characterLattice.pullback (bc.map q') : X^*(C_L) → X^*(B_L)`. It is
   `Gal(L/k)`-equivariant by `characterLattice.galoisRepresentation_naturality`.
3. **Injectivity.** `C_L` is integral (`IsSplitTorus.isIntegral`), hence
   reduced. The underlying morphism of `bc.map q'` is surjective because
   surjectivity is stable under base change
   (`MorphismProperty.overPullbackMap`). So `i` is injective by
   `pullback_injective_of_surjective`.
4. **Retraction.** Both lattices are finite free
   (`characterLattice_free_finite`), and `Gal(L/k)` is finite.
   `exists_equivariant_retraction` gives `n > 0` and an equivariant `r` with
   `r ∘ i = n • id`.
5. **Descent.** `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`,
   applied with target `B` (split over `L`) and source `C`, turns the equivariant
   character map `r` into a homomorphism `s' : C ⟶ B` whose base change pulls
   back characters by `r`. Take `s = CommGroupScheme.groupHom s'`.
6. **Identification.** The same descent lemma, applied with target and source
   `C` (split over `L`) and character map `n • id` on `X^*(C_L)`, has a unique
   solution. Both `s' ≫ q'`
   and `n • 𝟙 C` are solutions:
   - `bc.map (s' ≫ q')` pulls back `χ` to `r (i χ) = n • χ`;
   - `bc.map (n • 𝟙 C) = n • 𝟙` (`baseChange_map_zsmul_id`) pulls back `χ`
     to `n • χ`.

   Hence `s' ≫ q' = n • 𝟙 C`. Applying `CommGroupScheme.groupHom` gives
   `s ≫ q = multiplication C.toGrp n`, since `n • 𝟙 C` is by definition
   `Additive.ofMul (multiplication C.toGrp n)`.

## Library and Mathlib inputs

- `Langlands.GroupScheme.Torus.CommonFiniteGaloisSplitting`
  (`IsTorus.commonFiniteGaloisSplitting`).
- `Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent`
  (`IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`).
- `Langlands.GroupScheme.Torus.GaloisCharacterFunctor`
  (`characterLattice.galoisRepresentation`, `_naturality`).
- `Langlands.GroupScheme.Torus.Integral` (`IsSplitTorus.isIntegral`).
- `Langlands.GroupScheme.Torus.SplitLatticeBaseChange`
  (`splitTorus.characterLatticeEquiv`).
- `Langlands.AbelianScheme.Multiplication` (`multiplication_baseChange`).
- Mathlib: `ext_of_isDominant_of_isSeparated`, `Matrix.adjugate_mul`,
  `Matrix.exists_mulVec_eq_zero_iff`, `LinearMap.toMatrix_mulVec_repr`.

## Provenance

This proves an internal statement. Its Markdown records its role as the
finite-index input of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Corollary B.8.6. The proof here is the standard argument through
Galois character lattices. It replaces the rational Maschke step with an
explicit integral Gram–adjugate retraction followed by Galois averaging.
