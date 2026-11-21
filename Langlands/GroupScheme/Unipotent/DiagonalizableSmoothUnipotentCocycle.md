# Diagonalizable one-cocycles in smooth unipotent groups

Worker 386. This is an internal derived module for the conjugacy of sections of
trigonalizable groups (Task 7806). Its main theorem says that, over an algebraically
closed field of any characteristic, every rational one-cocycle of a diagonalizable group
`D(Λ)`, with `Λ` finitely generated, in a smooth affine unipotent group is a coboundary.
This is `VanishingStatement.{u}`, proved here as `exists_coboundary`.

## Notation

`k` is a field in universe `u`. `𝔻 Λ` is the diagonalizable group
`Diagonalizable.groupScheme (CommRingCat.of k) Λ`, viewed as a group scheme, and `T₀` is
the base `Over.mk (𝟙 (Spec k))`. For `g : Λ' →+ Λ`, `ρ g` is the underlying scheme
morphism of `Diagonalizable.restrictMap (CommRingCat.of k) g : 𝔻 Λ ⟶ 𝔻 Λ'`. A cocycle
`c : a.Cocycle T₀` is a morphism `T₀ × 𝔻 Λ ⟶ U` with `c(h h') = c(h) · h(c(h'))`, and
`a.coboundary v` is the cocycle `h ↦ v · h(v)⁻¹`.

## Main theorems

`exists_coboundary`: let `k` be algebraically closed and `Λ` a finitely generated abelian
group in universe `u`. Let `U` be a group scheme over `Spec k` that is smooth and affine
over the base, with `IsUnipotent U`. Then for every automorphic action `a` of `𝔻 Λ` on `U`
and every cocycle `c : a.Cocycle T₀` there is a rational point `v : T₀ ⟶ U.X` with
`c = a.coboundary v`.
The proof splits on the characteristic of `k`: in characteristic zero it is
`diagonalizableUnipotentCocycle.exists_coboundary_of_smooth` with the `CharZero` case of
its hypothesis; in characteristic `p` it is `exists_coboundary_of_charP`.

`exists_coboundary_of_charP`: the same conclusion under `[CharP k p]` for a prime `p`.

`U` need not be connected.

## Proof in characteristic `p`

1. `exists_split` writes `Λ` through homomorphisms `g₁ : Λ →+ Λ₁`, `g₂ : Λ →+ Λ₂`,
   `s₁ : Λ₁ →+ Λ`, `s₂ : Λ₂ →+ Λ` with `s₁ g₁ + s₂ g₂ = id`, where `Λ₁` is finitely
   generated with `p`-primary torsion and `Λ₂` is finite and killed by an integer `m`
   prime to `p`. Put `ι₁ = restrictMap g₁ : 𝔻 Λ₁ ⟶ 𝔻 Λ` and `ι₂ = restrictMap g₂`.
2. By `Diagonalizable.diagonalizableSmoothConnectedCriteria`, `𝔻 Λ₁` is connected and
   `𝔻 Λ₂` is smooth (its character group has no `p`-torsion).
3. By `eq_mul_of_split`, every point `x` of `𝔻 Λ` is
   `((x ≫ ρ s₁) ≫ ρ g₁) * ((x ≫ ρ s₂) ≫ ρ g₂)`, a product of a point through `ι₁` and a
   point through `ι₂`.
4. The rational points of `𝔻 Λ₂` form a finite group (`finite_points`), killed by `m`
   (`pow_eq_one_points`), so their number is prime to every power of `p`
   (`coprime_card_of_pow_eq_one`, by Cauchy's theorem).
5. The rational points of `U` form a nilpotent group (`isNilpotent_points_of_isUnipotent`)
   killed by some `p ^ r` (`exists_hasUniformPowerExponent_of_isUnipotent`).
6. Morphisms `T₀ × 𝔻 Λ₂ ⟶ U` that agree on all rational points are equal
   (`hom_ext_of_smooth`).
7. Every cocycle of the restricted action `a.restrict ι₁` is a coboundary, by
   `diagonalizableUnipotentCocycle.exists_coboundary_of_smooth` with `𝔻 Λ₁` connected.
8. `exists_coboundary_of_split` combines these facts.

## Helper results

- `exists_split`: from `Diagonalizable.exists_freeFiniteEquiv`, `Λ ≃ (I → ℤ) × A` with
  `A` finite. Write `|A| = p ^ a · m` with `p ∤ m`, choose `u, v` with
  `p ^ a u + m v = 1`, and let `Λ₂` be the image of `e = p ^ a u` acting on `A`, which is
  idempotent on `A`. Then `Λ₁` is the kernel of the projection `Ψ` of `Λ` onto `Λ₂`, and
  a torsion element of `Λ₁` lies in `A` with `e` acting as `0`, so it is killed by `p ^ a`.
- `comp_restrictMap_add`, `comp_restrictMap_id`: the morphism induced by `g + h` is the
  pointwise product of those induced by `g` and `h`, and the identity of `Λ` induces the
  identity. Both are checked on character values (`Diagonalizable.pointsEquiv_restrictMap`).
- `eq_mul_of_split`: the point decomposition of step 3.
- `pow_eq_one_points`: if `m` kills `Λ`, then `y ^ m = 1` for every point `y` of `𝔻 Λ`.
- `finite_monoidHom_units`: homomorphisms from a finite group to the units of a domain
  form a finite set (they land in the roots of unity of order the exponent).
- `finite_points`: `𝔻 Λ` has finitely many rational points when `Λ` is finite.
- `coprime_card_of_pow_eq_one`: a finite group killed by `m`, with `m` prime to the prime
  `p`, has order prime to `p ^ r`.
- `hom_ext_of_smooth`: let `k` be separably closed, `X` smooth over `Spec k` and `Y`
  separated. Two morphisms `T₀ × X ⟶ Y` that agree after `lift (𝟙 T₀) y` for every
  rational point `y` of `X` are equal. `X` is reduced
  (`SmoothReducedProof.isReduced_of_smooth_over_field`) with dense rational points
  (`hasDenseRationalPoints_of_smooth_of_isSepClosed`), so `hom_ext_of_denseRationalPoints`
  applies after composing with the section `X ⟶ T₀ × X`.
- `mulAutRestrict`: an action `φ : F →* MulAut G` restricted to a subgroup `Z` that every
  `φ f` maps into itself, with `coe_mulAutRestrict_apply`.

## Proof of `exists_coboundary_of_split`

The data are group schemes `D`, `U`, `D₁`, `D₂` over `Spec k`, an action `a` of `D` on `U`,
homomorphisms `ι₁ : D₁ ⟶ D` and `ι₂ : D₂ ⟶ D` such that the points of `D` commute and
every point of `D` is a product of a point through `ι₁` and a point through `ι₂`, and
the following hypotheses: every rational cocycle of `a.restrict ι₁` is a coboundary;
`D₂` has finitely many rational points; the group of rational points of `U` is nilpotent
and killed by `n`, with `n` prime to the number of rational points of `D₂`; and
morphisms `T₀ × D₂ ⟶ U` are determined by their values on rational points. Let `c` be a
rational cocycle.

1. The restriction `c.precomp ι₁` is the coboundary of some `v`. The conjugate
   `c₁ = Cocycle.conjugate v⁻¹ c` is trivial on points through `ι₁`.
2. Since the points of `D` commute, the cocycle identity for `c₁` on `x y = y x`, with `x`
   through `ι₁` and `y` through `ι₂`, shows that the values of `c₁` on points through
   `ι₂` are fixed by `D₁`, i.e. lie in the fixed subgroup of `a.restrict ι₁`.
3. Let `Z` be the group of `D₁`-fixed rational points of `U`. The rational points of `D₂`
   act on `Z` through `(a.restrict ι₂).pointsAction` and `mulAutRestrict`, and
   `f ↦ c₁(ι₂ f)` is a cocycle of this finite group in `Z`. `Z` is nilpotent and killed
   by `n`, so `Langlands.Group.CoprimeNilpotentCocycle.exists_coboundary` gives `g ∈ Z`
   with `c₁(ι₂ f) = g · (ι₂ f)(g)⁻¹` for every rational point `f` of `D₂`.
4. `c₂ = Cocycle.conjugate g⁻¹ c₁` is trivial on rational points of `D₂`, hence on all of
   `D₂` by the extension hypothesis. It is still trivial on `D₁`, because `g` is fixed
   by `D₁`.
5. By the cocycle identity and the point decomposition, `c₂` is the trivial cocycle, so
   `c = a.coboundary (v * g)` (`conjugate_coboundary`, `conjugate_conjugate_inv`).

## Provenance

Internal. The reduction from `D(Λ)` to a connected part `D(Λ₁)` and a finite part
`D(Λ₂)`, through the `D₁`-fixed subgroup of `U`, follows the dévissage of SGA 3,
Exp. XVII, Lemme 5.7.2 (proof of Théorème 5.1.1 ii) b)), which passes to the centralizer
of the lift of the first factor. Here the dévissage is done on rational points and only once,
for a direct product decomposition of `D(Λ)`. The finite part is handled by the
elementary coprime-action lemma `Langlands.Group.CoprimeNilpotentCocycle.exists_coboundary`
on rational points, not by the smoothness of the fixed subgroup (SGA 3 uses 5.6.1 for
that), and the connected part by `diagonalizableUnipotentCocycle.exists_coboundary_of_smooth`.
