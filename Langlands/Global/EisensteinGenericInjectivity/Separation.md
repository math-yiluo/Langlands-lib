# Separation of Eisenstein frequencies along an archimedean ray

Module `Langlands.Global.EisensteinGenericInjectivity.Separation` proves
`frequency_separation`: for a parabolic `P` of a connected reductive group `G` over a number
field, with a parabolic root presentation whose split component is a split torus, and a compact
subgroup `K` with `P(𝔸) K = G(𝔸)`, there is a rational character `χ` of `P` such that moving any
finite family of points of `G(𝔸)` along the archimedean ray of the split component makes every
nontrivial family of rational cosets `P(F) \ G(F)` change the total Iwasawa height at `χ`,
except for finitely many ray parameters. The module
`Langlands.Global.EisensteinGenericInjectivity.Anchor` uses it to isolate the coefficient of the
trivial coset in an exponential series.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`, universe
`u`. Notation: `σ_w(x) = placeMatrix σ w x`, `e_j = Pi.single j 1`, `H(x) = hK.height x χ` for
`hK : IsIwasawaCompact p K`, `ray(s) = ray F c s` (module
`Langlands.Global.EisensteinGenericInjectivity.Ray`), `rational F G : G(F) → G(𝔸)` the
principal points. Complete types are printed by `PrettyPrinter.ppSignature` (the `#check` form),
with the namespaces of the page of `Langlands.Global.EisensteinGenericInjectivity.PlaceHeight`
open.

## Declarations

### Height energies

- `placeMatrix_inv_mulVec_ne_zero`: `σ_w(z⁻¹) v ≠ 0` for `v ≠ 0`. The matrix `σ_w(z⁻¹)` is the
  underlying matrix of the unit `Matrix.GeneralLinearGroup.map (placeHom w)` of
  `adelicMatrix F G σ z⁻¹`, so the Library lemma `FlagCore.mulVec_ne_zero` (module
  `Langlands.GroupScheme.FlagCoreLinear`) applies.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_inv_mulVec_ne_zero.{u} {F : Type u}
    [Field F] [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ}
    (σ : G.MatrixRepresentation (Fin N)) (w : Langlands.Global.InfinitePlace F)
    (z : AdelicGroupPoints F G) {v : Fin N → ℂ} (hv : v ≠ 0) : placeMatrix σ w z⁻¹ *ᵥ v ≠ 0
  ```
- `heightEnergy hK χ Q σ j z = exp(2 H(z)) ∏_w Q_w(σ_w(z⁻¹) e_j)^{mult w}`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.heightEnergy.{u} {F : Type u} [Field F]
    [NumberField F] {G P : Langlands.GroupScheme (Spec ↧F)} {p : P ⟶ G}
    {K : Subgroup (AdelicGroupPoints F G)} {N : ℕ} (hK : IsIwasawaCompact p K)
    (χ : P.rationalCharacters) (Q : Langlands.Global.InfinitePlace F → (Fin N → ℂ) → ℝ)
    (σ : G.MatrixRepresentation (Fin N)) (j : Fin N) (z : AdelicGroupPoints F G) : ℝ
  ```
- `heightEnergy_eq_of_finite_eq`: if `σ(p(q)) e_j = χ(q) e_j` for `q ∈ P(𝔸)` and the `Q_w` are
  invariant energies, `heightEnergy` depends only on the finite part of `z`. This is
  `exp_two_mul_height_sub` of the module `Langlands.Global.EisensteinGenericInjectivity.PlaceHeight`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.heightEnergy_eq_of_finite_eq.{u} {F : Type u}
    [Field F] [NumberField F] {G P : Langlands.GroupScheme (Spec ↧F)} [IsAffine G.X.left]
    [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion (Over.Hom.left p.hom.hom)]
    {K : Subgroup (AdelicGroupPoints F G)} {N : ℕ} {σ : G.MatrixRepresentation (Fin N)} {j : Fin N}
    (hK : IsIwasawaCompact p K) {χ : P.rationalCharacters}
    {Q : Langlands.Global.InfinitePlace F → (Fin N → ℂ) → ℝ}
    (hQ : ∀ (w : Langlands.Global.InfinitePlace F), IsInvariantEnergy σ w K (Q w))
    (ha :
      ∀ (q : AdelicGroupPoints F P),
        ↑((adelicMatrix F G σ) ((AdelicGroupPoints.map F P G p) q)) *ᵥ Pi.single j 1 =
          ↑((character F P (Additive.toMul χ)) q) • Pi.single j 1)
    (x y : AdelicGroupPoints F G) (hxy : (finite F G) x = (finite F G) y) :
    heightEnergy hK χ Q σ j x = heightEnergy hK χ Q σ j y
  ```

### Rational columns

- `placeMatrix_rational`: for a rational point `x`, `σ_w(x)` is the rational matrix of `x`
  mapped by `w.embedding` (`placeHom_algebraMap`).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_rational.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) (x : RationalGroupPoints F G) :
    placeMatrix σ w ((rational F G) x) =
      (↑((rationalMatrix F G σ) x)).map ⇑(InfinitePlace.embedding w)
  ```
- `rationalColumn σ j x = σ(x⁻¹) e_j ∈ F^N`, the `j`-th column of the rational matrix of `x⁻¹`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.rationalColumn.{u} {F : Type u} [Field F]
    {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N)) (j : Fin N)
    (x : RationalGroupPoints F G) : Fin N → F
  ```
- `placeMatrix_rational_inv_single`: `σ_w(x⁻¹) e_j` is `w.embedding` applied to
  `rationalColumn σ j x`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_rational_inv_single.{u} {F : Type u}
    [Field F] [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ}
    (σ : G.MatrixRepresentation (Fin N)) (w : Langlands.Global.InfinitePlace F) (j : Fin N)
    (x : RationalGroupPoints F G) :
    placeMatrix σ w ((rational F G) x)⁻¹ *ᵥ Pi.single j 1 = fun i =>
      (InfinitePlace.embedding w) (rationalColumn σ j x i)
  ```
- `rationalColumn_ne_zero`: the column is nonzero (Library lemma
  `PrimitiveAdelicHeight.rational_mulVec_ne_zero`, module `Langlands.Global.PrimitiveAdelicBasis`).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.rationalColumn_ne_zero.{u} {F : Type u} [Field F]
    {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N)) (j : Fin N)
    (x : RationalGroupPoints F G) : rationalColumn σ j x ≠ 0
  ```
- `weight_lt_of_rationalColumn_ne_zero`: under the strict weight gap
  `σ.HasStrictOrbitWeightUpperBound e j`, a nonzero entry `i ≠ j` of the column has
  `e_i < e_j`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.weight_lt_of_rationalColumn_ne_zero.{u} {F : Type u}
    [Field F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} {σ : G.MatrixRepresentation (Fin N)}
    {j : Fin N} {e : Fin N → ℤ} (hgap : σ.HasStrictOrbitWeightUpperBound e j)
    (x : RationalGroupPoints F G) {i : Fin N} (hij : i ≠ j) (hu : rationalColumn σ j x i ≠ 0) :
    e i < e j
  ```

### Energies along the ray

- `rowWeights σ j e x i = e_j − e_i` on the support of the column and `0` off it.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.rowWeights.{u} {F : Type u} [Field F]
    {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N)) (j : Fin N)
    (e : Fin N → ℤ) (x : RationalGroupPoints F G) : Fin N → ℕ
  ```
- `rowVectors σ j w g x i = σ_w(g⁻¹) (w.embedding(u_i) e_i)` with `u = rationalColumn σ j x`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.rowVectors.{u} {F : Type u} [Field F] [NumberField F]
    {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N)) (j : Fin N)
    (w : Langlands.Global.InfinitePlace F) (g : AdelicGroupPoints F G) (x : RationalGroupPoints F G) :
    Fin N → Fin N → ℂ
  ```
- `ray_inv_mulVec_column`: if `c ≫ σ` is diagonal with weights `e`, then
  `σ_w(ray(s)⁻¹) u = (exp s)^{−e_j} ∑_i (exp s)^{rowWeights i} w.embedding(u_i) e_i`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.ray_inv_mulVec_column.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} {σ : G.MatrixRepresentation (Fin N)}
    {j : Fin N} {e : Fin N → ℤ} {c : (Gm (Spec ↧F)).toGrp ⟶ G}
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (↧F) e)
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (w : Langlands.Global.InfinitePlace F) (s : ℝ)
    (x : RationalGroupPoints F G) :
    (placeMatrix σ w (ray F c s)⁻¹ *ᵥ fun i => (InfinitePlace.embedding w) (rationalColumn σ j x i)) =
      ↑(Real.exp s) ^ (-e j) •
        ∑ i,
          ↑(Real.exp s ^ rowWeights σ j e x i) •
            (InfinitePlace.embedding w) (rationalColumn σ j x i) • Pi.single i 1
  ```
- `energy_rational_ray`: for a quadratic energy (module
  `Langlands.Global.EisensteinGenericInjectivity.Energy`),
  `Q(σ_w((x · ray(s) · g)⁻¹) e_j) = |(exp s)^{−e_j}|² · P(exp s)` where
  `P = energyPoly B (rowVectors σ j w g x) (rowWeights σ j e x)` (module
  `Langlands.Global.EisensteinGenericInjectivity.Poly`).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.energy_rational_ray.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {K : Subgroup (AdelicGroupPoints F G)}
    {N : ℕ} {σ : G.MatrixRepresentation (Fin N)} {j : Fin N} {e : Fin N → ℤ}
    {c : (Gm (Spec ↧F)).toGrp ⟶ G} {w : Langlands.Global.InfinitePlace F} {Q : (Fin N → ℂ) → ℝ}
    {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ} (hQ : IsQuadraticEnergy σ w K Q B)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (↧F) e)
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (g : AdelicGroupPoints F G)
    (x : RationalGroupPoints F G) (s : ℝ) :
    Q (placeMatrix σ w ((rational F G) x * (ray F c s * g))⁻¹ *ᵥ Pi.single j 1) =
      ‖↑(Real.exp s) ^ (-e j)‖ ^ 2 *
        Polynomial.eval (Real.exp s) (energyPoly B (rowVectors σ j w g x) (rowWeights σ j e x))
  ```
- `energy_ray`: `Q(σ_w((ray(s) · g)⁻¹) e_j) = |(exp s)^{−e_j}|² · Q(σ_w(g⁻¹) e_j)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.energy_ray.{u} {F : Type u} [Field F] [NumberField F]
    {G : Langlands.GroupScheme (Spec ↧F)} {K : Subgroup (AdelicGroupPoints F G)} {N : ℕ}
    {σ : G.MatrixRepresentation (Fin N)} {j : Fin N} {e : Fin N → ℤ} {c : (Gm (Spec ↧F)).toGrp ⟶ G}
    {w : Langlands.Global.InfinitePlace F} {Q : (Fin N → ℂ) → ℝ} (hQ : IsInvariantEnergy σ w K Q)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (↧F) e) (g : AdelicGroupPoints F G)
    (s : ℝ) :
    Q (placeMatrix σ w (ray F c s * g)⁻¹ *ᵥ Pi.single j 1) =
      ‖↑(Real.exp s) ^ (-e j)‖ ^ 2 * Q (placeMatrix σ w g⁻¹ *ᵥ Pi.single j 1)
  ```
- `exists_rowHeight`: there is `κ > 0`, independent of `s`, with
  `exp(2 (H(ray(s) g) − H(x · ray(s) g))) = κ ∏_w P_w(exp s)^{mult w}`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.exists_rowHeight.{u} {F : Type u} [Field F]
    [NumberField F] {G P : Langlands.GroupScheme (Spec ↧F)} [IsAffine G.X.left] [IsAffine P.X.left]
    {p : P ⟶ G} [IsClosedImmersion (Over.Hom.left p.hom.hom)] {K : Subgroup (AdelicGroupPoints F G)}
    {N : ℕ} {σ : G.MatrixRepresentation (Fin N)} {j : Fin N} {e : Fin N → ℤ}
    {c : (Gm (Spec ↧F)).toGrp ⟶ G} (hK : IsIwasawaCompact p K) {χ : P.rationalCharacters}
    {Q : Langlands.Global.InfinitePlace F → (Fin N → ℂ) → ℝ}
    {B : Langlands.Global.InfinitePlace F → (Fin N → ℂ) → (Fin N → ℂ) → ℝ}
    (hQ : ∀ (w : Langlands.Global.InfinitePlace F), IsQuadraticEnergy σ w K (Q w) (B w))
    (ha :
      ∀ (q : AdelicGroupPoints F P),
        ↑((adelicMatrix F G σ) ((AdelicGroupPoints.map F P G p) q)) *ᵥ Pi.single j 1 =
          ↑((character F P (Additive.toMul χ)) q) • Pi.single j 1)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (↧F) e)
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (g : AdelicGroupPoints F G)
    (x : RationalGroupPoints F G) :
    ∃ κ,
      0 < κ ∧
        ∀ (s : ℝ),
          Real.exp
              (2 *
                ((hK.height (ray F c s * g)) χ -
                  (hK.height ((rational F G) x * (ray F c s * g))) χ)) =
            κ *
              ∏ w,
                Polynomial.eval (Real.exp s)
                    (energyPoly (B w) (rowVectors σ j w g x) (rowWeights σ j e x)) ^
                  InfinitePlace.mult w
  ```
- `rowPoly_top`: `P_w` has degree at most `2D`, `D` the largest of the `rowWeights`, and a
  positive coefficient in degree `2D`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.rowPoly_top.{u} {F : Type u} [Field F] [NumberField F]
    {G : Langlands.GroupScheme (Spec ↧F)} {K : Subgroup (AdelicGroupPoints F G)} {N : ℕ}
    {σ : G.MatrixRepresentation (Fin N)} {j : Fin N} {e : Fin N → ℤ}
    {w : Langlands.Global.InfinitePlace F} {Q : (Fin N → ℂ) → ℝ} {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ}
    (hQ : IsQuadraticEnergy σ w K Q B) (g : AdelicGroupPoints F G) (x : RationalGroupPoints F G) :
    (energyPoly B (rowVectors σ j w g x) (rowWeights σ j e x)).natDegree ≤
        2 * Finset.univ.sup (rowWeights σ j e x) ∧
      0 <
        (energyPoly B (rowVectors σ j w g x) (rowWeights σ j e x)).coeff
          (2 * Finset.univ.sup (rowWeights σ j e x))
  ```
- `one_le_sup_rowWeights`: if the coset of the rational point `x` in `P(F) \ G(F)` is not the
  trivial coset, then `D ≥ 1`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.one_le_sup_rowWeights.{u} {F : Type u} [Field F]
    [NumberField F] {G P : Langlands.GroupScheme (Spec ↧F)} [IsAffine G.X.left] {p : P ⟶ G} {N : ℕ}
    {σ : G.MatrixRepresentation (Fin N)} {j : Fin N} {e : Fin N → ℤ}
    (hstab : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j)
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (x : RationalGroupPoints F G)
    (hx : ⟦⟨(rational F G) x, ⋯⟩⟧ ≠ ⟦1⟧) : 1 ≤ Finset.univ.sup (rowWeights σ j e x)
  ```

### Main result

- `frequency_separation r hA hG hK`: there is `χ : rationalCharacters P` such that for every
  `m`, every `g : Fin m → G(𝔸)` and every `cs : Fin m → P(F) \ G(F)` other than the constant
  trivial coset, the set of `s ∈ ℝ` with
  `∑_k H(γ_k · ray(s) · g_k) = ∑_k H(ray(s) · g_k)`, where `γ_k = out(cs_k)` and
  `c = ζ ≫ a ≫ l ≫ p` for the split-component cocharacter `ζ`, is finite.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.frequency_separation.{u} {F : Type u} [Field F]
    [NumberField F] {G P M : Langlands.GroupScheme (Spec ↧F)}
    {A : Langlands.CommGroupScheme (Spec ↧F)} [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion (Over.Hom.left p.hom.hom)] {l : M ⟶ P}
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a) (hA : IsSplitTorus A.toGrp)
    (hG : G.IsConnectedReductive) {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) :
    ∃ χ,
      ∀ (m : ℕ) (g : Fin m → AdelicGroupPoints F G) (cs : Fin m → ParabolicRationalCosets F p),
        (cs ≠ fun x => ⟦1⟧) →
          {s |
              ∑ k,
                  (hK.height
                      (↑(Quotient.out (cs k)) *
                        (ray F
                            (Langlands.CommGroupScheme.groupHom r.splitComponentCocharacter ≫
                              a ≫ l ≫ p)
                            s *
                          g k)))
                    χ =
                ∑ k,
                  (hK.height
                      (ray F
                          (Langlands.CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p)
                          s *
                        g k))
                    χ}.Finite
  ```

## Proof of `frequency_separation`

1. `exists_lineData` (module `Langlands.Global.EisensteinGenericInjectivity.LineData`) supplies
   `σ`, the line `j`, the weights `e` and the strict gap. `χ` is the rational character by which
   `P` acts on the line `j` (`coordinateLineRationalCharacter`), so
   `σ(p(q)) e_j = χ(q) e_j`. `exists_quadraticEnergy` gives a quadratic energy `(Q_w, B_w)` at
   every infinite place.
2. For a rational point `x` and a point `g`, the finite parts of `x · ray(s) · g` and
   `ray(s) · g` are those of `x · g` and `g` (`finite_ray`), so their height energies do not
   depend on `s` (`heightEnergy_eq_of_finite_eq`). Comparing them with `energy_rational_ray`
   and `energy_ray` gives `exists_rowHeight`.
3. `rowPoly_top`: the top coefficient of `P_w` is `Q_w` of `σ_w(g⁻¹)` applied to the part of
   `u` of largest weight gap, a nonzero vector, hence positive. `one_le_sup_rowWeights`: if
   every entry of `u` off `j` vanished, `u` would be a multiple of `e_j`, and the injective
   `parabolicRationalProjectiveEmbedding` with the exact line stabilizer (module
   `Langlands.Global.AdelicParabolicProjectiveHeight`) would make the coset of `x` trivial. So
   some `u_i ≠ 0` with `i ≠ j`, hence `e_i < e_j` and `D ≥ 1`.
4. If the two sums of heights agree at `s`, multiplying the identities of step 2 over `k` gives
   `Π(exp s) = (∏_k κ_k)⁻¹` for the polynomial `Π = ∏_{k,w} P_{k,w}^{mult w}`. By
   `coeff_prod_pow_of_natDegree_le` its coefficient in degree `∑_{k,w} mult w · 2 D_k` is a
   product of positive numbers, and this degree is positive for the index `k` with a nontrivial
   coset. `finite_setOf_eval_eq` and the injectivity of `exp` make the set of such `s` finite.

## Sources

The argument is not taken from a source; J. Bernstein and E. Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §8.5, printed pp. 224–225,
separate the exponents of the constant term along a regular element `a ∈ A_Q` instead (Lemma of
§8.5 and the difference operator `D(λ)`). The height `H` is the map `H_M`, `m_P` of §2.1,
printed p. 190.
