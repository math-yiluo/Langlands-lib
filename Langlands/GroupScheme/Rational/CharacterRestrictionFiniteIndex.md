# Finite-index restriction of rational characters to a central split torus

Author: Worker 1001.

This module proves the finite-index half of `CharacterRestrictionStatement`
(in [`CharactersStatement`](CharactersStatement.md)). It does not prove that
statement, whose other half is injectivity. The exported theorem is

```lean
theorem Langlands.GroupScheme.IsSplitComponent.finiteIndex_range_characterRestrict
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : A.toGrp ⟶ G} (hi : IsSplitComponent i) :
    (characterRestrict i).range.FiniteIndex
```

`characterRestrict i : rationalCharacters G →+ rationalCharacters A.toGrp` is the
restriction `X^*(G)_k → X^*(A)` of [`Characters`](Characters.md). The result
holds for every field `k`, with no condition on the characteristic and no
perfectness.

The theorem follows from a more general one:
`CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict`. That
version assumes only that `G.X.hom` is affine (`IsAffineHom`) and locally of
finite type (`LocallyOfFiniteType`), and that `i` is a central split torus
(`IsCentralSplitTorus i`). It uses neither reductivity, nor smoothness, nor
connectedness, nor the maximality in `IsSplitComponent`. For a split component of a
connected reductive group these hypotheses come from
`IsConnectedReductive.isAffineHom`, from `IsConnectedReductive.smooth` (Mathlib:
smooth implies locally of finite presentation, hence of finite type), and from
`IsSplitComponent.isCentralSplitTorus`.

All declarations except the exported theorem live in
`Langlands.GroupScheme.CharacterRestrictionFiniteIndex`. The module uses the
option `backward.isDefEq.respectTransparency false`, as the Library's torus
modules do. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Sources and provenance

The statement being proved is from Renard, *Représentations des groupes
réductifs p-adiques* (French version of 9 July 2026), source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, V.2.6,
Lemme and its proof (printed pp.107–108, PDF pp.113–114): « le réseau
𝑋^∗(𝐺) = 𝑋^∗(𝐺′) est d'indice fini dans 𝑋^∗(𝐴′_𝐺) et donc d'indice fini dans
𝑋^∗(𝐴_𝐺) ». See also Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (J. Inst. Math. Jussieu 2, 2003), source ID
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`, I.1
(printed pp.238–239), « Rat(G) ⊗_Z Q (≃ Rat(A_G) ⊗_Z Q ⊂ a*_G) ».

The proof here is internal and does not follow Renard. Renard identifies
`X^*(G)` with `X^*(G′)` for the torus `G′ = G/𝒟G = R(G)/(R(G) ∩ 𝒟G)` (V.2.2).
He then compares it with the split component `A′_G = A_G/(A_G ∩ 𝒟G)` of `G′`.
That needs the structure theory of reductive groups. This module uses
instead a faithful finite-dimensional representation (Milne, *Algebraic Groups*,
2017, Theorem 4.9 and Corollary 4.10, already proved in the Library as
`affineLinearEmbeddingStatement`), the weight decomposition of a split torus
acting through it, and determinants of weight blocks. That is the standard
argument that a central torus is detected by determinants of representations. It
is why the general theorem needs no reductivity.

## Outline of the proof

Fix a field `k`, an affine group `G` of finite type over `k`, and a central split
torus `i : A ⟶ G`. `IsSplitSubtorus` gives `A.toGrp ≅ splitTorus (Spec k) J` for
a finite `J`, and says `i` is a closed immersion. Put `j := e.inv ≫ i`. The
Library's `affineLinearEmbeddingStatement` gives `ρ : MatrixRepresentation G (Fin N)`
that is a closed immersion. Then `ρ ∘ j` is a closed immersion, hence a
monomorphism.

1. **Weights.** Let `K = k[ℤ^I]` (`AddMonoidAlgebra k (I → ℤ)`). Let `t_univ` be the
   Library's universal point `splitTorus.universalPoint I` over `K`, with
   coordinates the monomials `e_i`. Its matrix `universalMatrix ρ I j` under
   `ρ ∘ j` lies in `GL_N(K)`. Its coefficients give the *weight matrices*
   `weight ρ I j m : Matrix (Fin N) (Fin N) k`, one for each `m : I → ℤ`. They
   vanish outside the finite set `weightSupport ρ I j`.
2. **Evaluation formula** (`affinePointsEquiv_eval`). Let `A` be a `k`-algebra and
   `t : I → Aˣ`. At the torus point with coordinates `t`, the `(a, b)` entry of
   the matrix of `ρ ∘ j` is `∑ₘ P_m a b • tᵐ`, where
   `tᵐ = exponentValue I t m = ∏ᵢ tᵢ ^ mᵢ`. Proof: the point is the image of
   `t_univ` under `evaluateUnits t` (`universalPoint_evaluateUnits`). Matrix points
   are natural (`GeneralLinear.affinePointsEquiv_naturality`), and
   `evaluateUnits t` sends the monomial `m` to `tᵐ`.
3. **Idempotents.**
   - `sum_weight`: the identity point (`t = 1`) gives `∑ₘ P_m = 1`.
   - `weight_mul_weight`: `P_m P_n = if m = n then P_m else 0`. Over
     `k[ℤ^I × ℤ^I]`, take the torus points with coordinates the monomials
     `(eᵢ, 0)` and `(0, eᵢ)`. Their product has coordinates `(eᵢ, eᵢ)`. By the
     evaluation formula and multiplicativity of `ρ ∘ j`,
     `∑ₘ P_m · (m, m) = (∑ₘ P_m · (m, 0)) (∑ₙ P_n · (0, n))`. Compare the
     coefficients of `(m, n)`.
4. **Centrality.**
   - `weight_commute_affine`: for every `k`-algebra `B` and every `B`-point `y` of
     `G`, the matrix of `ρ` at `y` commutes with `P_m`. Over `B[ℤ^I]`, the point
     `y` (through `b ↦ single 0 b`) commutes with the torus point with coordinates
     the monomials `eᵢ`, because `j` is central (`IsCentral`,
     `commute_of_mem_center`). Compare the coefficients of `m`.
   - `weight_commute_points`: for affine `G`, the same holds for points over
     every test scheme `T`, with the scalars `k → Γ(T, 𝒪_T)` of `scalars T`. Every
     point factors through an affine presentation `Spec B ≅ G.X`
     (`essImage_algSpec`), and the matrix points and scalars are natural
     (`GeneralLinear.pointsEquiv_naturality`, `scalars_naturality`,
     `scalars_algSpec`, `GeneralLinear.pointsEquiv_eq_affinePointsEquiv`).
5. **Blocks.** `exists_factor_of_mul_self` writes any idempotent `P` over a field
   as `P = U V` with `V U = 1`, through a basis of the image of `P`. For
   `P_m = U V` with `U : Matrix (Fin N) (Fin d) k`:
   - `compress` (pure matrix algebra) sends an invertible `M` commuting with `U V`
     to the invertible `V M U`. Since `V M₁ U V M₂ U = V M₁ M₂ U` when `M₂`
     commutes with `U V` (`compress_mul_compress`), this is multiplicative.
   - `blockPoints` applies `compress` to the matrices `ρ(g)` of points of `G` over
     every test scheme. `blockRepresentation : MatrixRepresentation G (Fin d)` is
     the resulting homomorphism `G ⟶ GL_d`, built with the Library's
     `homOfPoints`. Naturality is `blockPoints_naturality`.
   - `blockCharacter` is `blockRepresentation` followed by
     `GeneralLinear.determinantCharacter`. On points it is `det (V ρ(g) U)`
     (`characterEval_blockCharacter`).
6. **Restriction of a block character** (`characterRestrict_blockCharacter`):
   `characterRestrict j (blockCharacter …) = d • (torusCharacterEquiv k I).symm m`.
   Here `torusCharacterEquiv k I : X^*(𝔾_m^I) ≃+ ℤ^I` is the Library's
   `characterLatticeEquiv`, transported along `equivCharacterLattice`.
   - Characters of the affine torus are determined by their values on points over
     `k`-algebras (`rationalCharacters_ext_affine`).
   - At the point with coordinates `t`, the evaluation formula and
     `V P_n U = if n = m then 1 else 0` (`compress_weight`) give the block matrix
     `tᵐ • 1` (`blockPoints_torus`). Its determinant is `(tᵐ)^d`.
   - The torus character `m` takes the value `tᵐ`, by the Library's
     `characterValue_characterLatticeEquiv_symm` (`sectionsHom_characterEval_torus`).
   - Values are compared in `B` through `sectionsHom k B = (ΓSpecIso B).hom`, which
     is injective.
7. **The weights generate** (`closure_weights_eq_top`). Let `Λ` be the subgroup
   generated by the `m` with `P_m ≠ 0`.
   - Over `k[ℤ^I/Λ]`, take the torus point with coordinates the classes of the
     `eᵢ`. By the evaluation formula and `sum_weight`, its matrix under `ρ ∘ j` is
     `∑ₘ P_m = 1`.
   - Since `ρ ∘ j` is a monomorphism (`Over.mono_of_mono_left`), the point is the
     identity. So every `eᵢ` has trivial class, and `Λ = ℤ^I`.
8. **Finite index.**
   - `exists_nsmul_mem_range`: let `D` be the product of the block sizes
     `d_m ≠ 0` (`ne_zero_of_factor`) over the `m` with `P_m ≠ 0`. Then
     `D • m = (D / d_m) • (d_m • m)` lies in the range for each such `m`. The set
     of exponents with this property is a subgroup, so it is everything by step 7.
   - `finiteIndex_range_characterRestrict` transports this along
     `characterRestrict e.inv`, an additive equivalence with inverse
     `characterRestrict e.hom`. So `D • X^*(A) ⊆ range (characterRestrict i)`.
     `X^*(A) ≃ ℤ^J` is finitely generated, so the quotient by the range is
     finitely generated and killed by `D`, hence finite (Mathlib's
     `Module.finite_of_fg_torsion`). This is `finiteIndex_of_nsmul_mem`.

## Declarations

General algebra:

- `monomialUnit x`: the unit `single x 1` of `B[M]`.
  `exponentValue_monomialUnit φ m`: at the coordinates
  `monomialUnit (φ eᵢ)`, `tᵐ = monomialUnit (φ m)` for an additive `φ`.
  `exponentValue_monomialUnit_id` is the case `φ = id`.
- `compress U V hVU M hM`, `compress_val`, `compress_mul_compress`,
  `inv_commute_of_commute`, `val_map`.
- `exists_factor_of_mul_self`, `ne_zero_of_factor`, `finiteIndex_of_nsmul_mem`.
- `coeff_smul_single_one`, `coeff_smul_single`: coefficients of scaled monomials.

Weights (variables `ρ : MatrixRepresentation G (Fin N)`, `I` a finite type with
decidable equality, `j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G`):

- `universalMatrix`, `weight`, `weightSupport`, `weight_eq_zero`,
  `weight_apply_eq_zero`, `universalMatrix_apply`, `affinePointsEquiv_eval`,
  `sum_ite_eq_of_weightSupport`, `sum_weight`, `weight_mul_weight`,
  `weight_commute_affine` (needs `IsCentral j`), and `closure_weights_eq_top`
  (needs `Mono (j.hom.hom ≫ ρ.hom.hom).left`).

Points over test schemes:

- `scalars T : k →+* Γ(T.left, ⊤)`, the structure map
  `(ΓSpecIso k).inv ≫ T.hom.appTop`; `scalars_naturality`, `scalars_algSpec`.
- `weight_commute_points` (needs `IsCentral j` and `IsAffine G.X.left`).
- Block data, with hypotheses `hc : IsCentral j`, `[IsAffine G.X.left]`,
  `m : I → ℤ`, `U`, `V`, `hUV : U * V = weight ρ I j m` and `hVU : V * U = 1`:
  `map_mul_map_eq_one`, `commute_blockIdempotent`, `blockPoints`,
  `blockPoints_val`, `blockPoints_naturality`, `blockPointsSymm_naturality`,
  `blockRepresentation`, `pointsEquiv_blockRepresentation`, `blockCharacter`,
  `characterEval_blockCharacter`, `compress_weight`, `blockPoints_torus`,
  `characterRestrict_blockCharacter`.
- `sectionsHom k B`, `sectionsHom_inv`, `sectionsHom_comp_scalars`,
  `map_sectionsHom_pointsEquiv`: comparing global sections of `Spec B` with `B`.
- `torusCharacterEquiv k I`, `sectionsHom_characterEval_torus`,
  `characterEval_nsmul`, `rationalCharacters_ext_affine`.

Finite index:

- `exists_nsmul_mem_range` (needs `IsCentral j`, `IsAffine G.X.left` and the
  monomorphism hypothesis).
- `finiteIndex_range_characterRestrict` and the exported
  `Langlands.GroupScheme.IsSplitComponent.finiteIndex_range_characterRestrict`.
