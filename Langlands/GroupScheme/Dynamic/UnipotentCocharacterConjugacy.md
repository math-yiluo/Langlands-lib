# Conjugacy of cocharacters differing by a point of the dynamic unipotent subgroup

The entry theorem is `Langlands.GroupScheme.Dynamic.exists_unipotent_conj_of_mul_inv_mem`. Let
`k` be a field and `G` a group scheme over `Spec k` with affine structure morphism
(`IsAffineHom G.X.hom`). Let `χ ψ : 𝔾_m → G` be cocharacters such that the morphism
`t ↦ ψ(t) χ(t)⁻¹`, i.e. `ψ.hom.hom * (χ.hom.hom)⁻¹ : 𝔾_m.X ⟶ G.X`, is a point of the published
dynamic unipotent subgroup functor `Dynamic.unipotent χ` over the test scheme `𝔾_m`. Then there
is a rational point `u : Spec k ⟶ G` with

- `u ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec k)))`, and
- `χ ≫ (G.innerIso u).hom = ψ`, i.e. `ψ = u χ u⁻¹` as homomorphisms of group schemes.

No smoothness, connectedness, reductivity or finiteness hypothesis on `G` is used. The result
is the torus-lift input `hlift` of `Langlands.GroupScheme.DynamicLeviConjugacy.rationalLeviConjugacy_of_dynamic`
(`Rational/DynamicLeviConjugacyReduction`).

## Mathematical argument

Let `x(t) = ψ(t) χ(t)⁻¹`. It satisfies the cocycle identity
`x(st) = x(s) · χ(s) x(t) χ(s)⁻¹` and is contracting for the conjugation action of `χ`. In
coordinates `B = O(G)`, graded by `χ`-conjugation, the comultiplication respects total weight.
The pure-algebra module [`GradedCocycleExtension`](../../CommutativeAlgebra/GradedCocycleExtension.md)
shows that `x : B → k[t, t⁻¹]` takes values in `k[t]`. The value `u = x(0)` is then contracting,
hence a rational point of `U_G(χ)`. Setting `t = 0` in the cocycle identity gives
`u = x(s) · χ(s) u χ(s)⁻¹`, that is `u χ(s) u⁻¹ = ψ(s)`.

## The corepresented model (namespace `Langlands.GroupScheme.Corepresented`)

Throughout, `G = groupScheme F e` is the published corepresented affine group over `Spec k`
with coordinate `k`-algebra `B`.

### Comultiplication

- `comul e : B →ₐ[k] B ⊗[k] B` is the classifying map of the product of the two universal
  points `B → B ⊗ B` (`includeLeft`, `includeRight`), computed in the group `F (B ⊗ B)`.
  It reuses `AffineLinearEmbedding.comul` at the base field.
- `homEquiv_productMap_comp_comul`: for `k`-algebra maps `φ ψ : B → A`,
  `e.homEquiv (productMap φ ψ ∘ comul e) = e.homEquiv φ * e.homEquiv ψ`. The proof uses
  the existing `AffineLinearEmbedding.pt_productMap_comp_comul`.
- `algPoint e φ` is the point of `G` over `Spec A` given by a `k`-algebra map `φ : B → A`. It is
  `algSpec` applied to `φ`. `pointAlgHom_algPoint` and `algPoint_pointAlgHom` show that it is
  inverse to the published `pointAlgHom`.
- `pointAlgHom_mul`: the classifying map of a product of points over `Spec A` is
  `productMap (pointAlgHom x) (pointAlgHom y) ∘ comul e`. The proof uses that the published
  `affinePointsEquiv` is multiplicative.
- `pointAlgHom_one` shows that the identity point is classified by the counit. The two counit
  laws `productMap_counit_comul` and `productMap_comul_counit` follow from `1 * x = x` and
  `x * 1 = x` for the universal point.

### Unit points

The section uses the published `unitPoint f a` (the point of `𝔾_m` given by a unit `a`) from
`Dynamic/DominantCombinationInclusions`.

- `affinePointsEquiv_unitPoint` and `affinePointsEquiv_homMk_comp` compute the published
  `Gm.affinePointsEquiv` on unit points and on pullbacks along spectra of ring maps.
- `pointRing_homMk_comp` handles such pullbacks for points of `G`.
- `evalAlgHom a : k[T, T⁻¹] →ₐ[k] A` is evaluation at a unit `a`, and `laurentEvalPoint a` is its
  spectrum. `unitPoint_eq_laurentEvalPoint_comp` shows that every unit point is the pullback of the
  coordinate unit `T` of `Spec k[T, T⁻¹]`. `pointAlgHom_unitPoint_comp` gives the resulting
  classifying maps.
- `isIso_unitPoint_of_eq` proves that the coordinate unit point is an isomorphism onto `𝔾_m`.
  It identifies that point with the published `Gm.laurentPoint`, which is the inverse of
  `Gm.relativeLaurentIso`. `ofHom_algebraMap_laurent` identifies the two structure maps of
  `Spec k[T, T⁻¹]`.

### Two variables

On `k[t, t⁻¹][s, s⁻¹]`, `outerUnit` is `s` and `innerUnit'` is `t`.

- `coeff_evalAlgHom_outerUnit`, `evalAlgHom_innerUnit'` and
  `coeff_evalAlgHom_outerUnit_mul_innerUnit'` compute evaluation of `q ∈ k[T, T⁻¹]` at `s`, at
  `t` and at `st`.
- `univUnit` is the coordinate unit point over `Spec k[T, T⁻¹]`, and `twoVarPoint a` is the unit
  point over `Spec k[t, t⁻¹][s, s⁻¹]`.
- `coeff_pointAlgHom_outer`, `coeff_pointAlgHom_outer_inner`, `pointRing_inner` and
  `pointAlgHom_conj_inner` translate the points `x(s)`, `x(st)` and `χ(s) x(t) χ(s)⁻¹` into the
  coefficient hypotheses of `GradedCocycleExtension`. The last one uses the published
  `pointRing_conj`.
- `twoVar_cocycle` is the cocycle identity as an equality of points. It holds because `ψ` and
  `χ` are homomorphisms and unit points are multiplicative, and is closed by `group`.

### Conjugation and the grading of the comultiplication

- `constAlgHom A₀` is the constants `A₀ → A₀[s, s⁻¹]`.
- `pointRing_conj_algPoint_const`: conjugating the constant point given by `φ : B → A₀` by
  `χ(s)` is classified by the coaction followed by `φ` on each coefficient. It combines the
  published `pointRing_conj` and `laurentCoeffMap_comp_laurentC_comp_laurentEval`.
- `productMap_includeLeft_includeRight` shows that `productMap includeLeft includeRight` is the
  identity.
- `comul_mem_tensorWeightSpan'`: `comul e` maps weight `d` into `tensorWeightSpan`. Conjugation
  by `χ(s)` is multiplicative on the two universal points over `Spec (B ⊗ B)[s, s⁻¹]`.
  `pointAlgHom_mul` turns this into the intertwining identity required by
  `comul_mem_tensorWeightSpan`.

### Main argument

- `baseHom` identifies `Over.mk (𝟙 (Spec k))` with the spectrum of the `k`-algebra `k`.
- `constCoeffAlgHom x hx` is the constant coefficient of a point `x : B → k[t, t⁻¹]` without
  negative terms. It is multiplicative by the published `toLaurent_trunc`.
- `pointAlgHom_conj_const` and `constantPoint_eq_algPoint` compute the conjugate of the
  constant point `u` and identify the published `constantPoint` of `u` over `Spec k[T, T⁻¹]`.
- `exists_conj_of_mem_unipotent` is the theorem in the corepresented model, with conclusion
  `constantPoint u * χ * (constantPoint u)⁻¹ = ψ` on `𝔾_m`. The proof:
  - `coeff_eq_zero_of_cocycle` shows that `x` has no negative terms;
  - `u = constCoeffAlgHom x _` is contracting, so `baseHom ≫ algPoint e u ∈ U_G(χ)` by the
    published `isContracting_pointAlgHom_iff`;
  - `algebraMap_eq_of_cocycle` and `pointAlgHom_mul` give `u = x(s) · χ(s) u χ(s)⁻¹` over
    `Spec k[s, s⁻¹]`;
  - after rearranging in the group of points, the conjugacy holds after composing with the
    isomorphism `univUnit`, which is then cancelled.

## Transport to an arbitrary affine group (namespace `Langlands.GroupScheme.Dynamic`)

`exists_unipotent_conj_of_mul_inv_mem` uses the published isomorphism
`AffineCoordinates.groupSchemeIso G` between the corepresented model and `G`. The published
`unipotent_le_comap` transports the hypothesis and the membership of `u` along the
isomorphism. `Grp.hom_ext` together with `comp_innerIso_hom` reduces the conjugacy to the
identity of points from the corepresented model.

## Provenance

This is internal infrastructure; no statement is attributed to the literature. The route
(cocycle in coordinates, graded comultiplication, extension of `x` to `t = 0`) was proposed by
Worker 1491. The present formalization, including the comultiplication built from the
corepresentation, the use of unit points and the coefficient-level interface with
`GradedCocycleExtension`, is by Worker 1515. The statement avoids the structural parameters
carried by the published `Rational/TorusUnipotentLiftConjugacy` (split unipotent kernels and
torsor statements). Here the unipotent subgroup is the dynamic one, and the torus is `𝔾_m`
acting through `χ`.
