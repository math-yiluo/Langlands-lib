import Langlands.Global.EisensteinGenericInjectivity.Energy
import Langlands.Global.EisensteinGenericInjectivity.Poly
import Langlands.Global.EisensteinGenericInjectivity.LineData
import Langlands.Global.EisensteinGenericInjectivity.Ray
import Langlands.Global.PrimitiveAdelicBasis
import Langlands.GroupScheme.FlagCoreLinear

/-! # Separation of Eisenstein frequencies along an archimedean ray -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Polynomial
open scoped CategoryTheory.MonObj NNReal Matrix

set_option autoImplicit false

namespace Langlands.Global.EisensteinGenericInjectivity

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  {N : ℕ} {σ : MatrixRepresentation G (Fin N)} {j : Fin N}

omit [IsAffine G.X.left] in
/-- The complex matrix of an adelic point at an infinite place is the underlying matrix of the
complex unit `GeneralLinearGroup.map (placeHom w)`, so `FlagCore.mulVec_ne_zero` applies. -/
theorem placeMatrix_inv_mulVec_ne_zero (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (z : AdelicGroupPoints F G) {v : Fin N → ℂ} (hv : v ≠ 0) :
    placeMatrix σ w z⁻¹ *ᵥ v ≠ 0 :=
  FlagCore.mulVec_ne_zero (Matrix.GeneralLinearGroup.map (placeHom w)
    (adelicMatrix F G σ z⁻¹)) hv

/-- The height at the line character combined with the archimedean energies of the inverse
orbit vector. By the archimedean formula it depends only on the finite part. -/
def heightEnergy (hK : IsIwasawaCompact p K) (χ : rationalCharacters P)
    (Q : InfinitePlace F → (Fin N → ℂ) → ℝ) (σ : MatrixRepresentation G (Fin N)) (j : Fin N)
    (z : AdelicGroupPoints F G) : ℝ :=
  Real.exp (2 * hK.height z χ) *
    ∏ w : InfinitePlace F, Q w (placeMatrix σ w z⁻¹ *ᵥ Pi.single j 1) ^ w.mult

theorem heightEnergy_eq_of_finite_eq (hK : IsIwasawaCompact p K) {χ : rationalCharacters P}
    {Q : InfinitePlace F → (Fin N → ℂ) → ℝ} (hQ : ∀ w, IsInvariantEnergy σ w K (Q w))
    (ha : ∀ q : AdelicGroupPoints F P,
      ((adelicMatrix F G σ (map F P G p q) : AdelicGL F N) :
          Matrix (Fin N) (Fin N) (AdeleRing (𝓞 F) F)) *ᵥ Pi.single j 1 =
        (character F P χ.toMul q).val • Pi.single j 1)
    (x y : AdelicGroupPoints F G) (hxy : finite F G x = finite F G y) :
    heightEnergy hK χ Q σ j x = heightEnergy hK χ Q σ j y := by
  have h := exp_two_mul_height_sub hK hQ ha x y hxy
  have hpos : ∀ z : AdelicGroupPoints F G,
      0 < ∏ w : InfinitePlace F, Q w (placeMatrix σ w z⁻¹ *ᵥ Pi.single j 1) ^ w.mult :=
    fun z => Finset.prod_pos fun w _ => pow_pos ((hQ w).pos _
      (placeMatrix_inv_mulVec_ne_zero σ w z (Pi.single_eq_zero_iff.not.mpr one_ne_zero))) _
  simp only [div_pow] at h
  rw [Finset.prod_div_distrib] at h
  have hx := hpos x
  have hy := hpos y
  unfold heightEnergy
  rw [show 2 * hK.height y χ = 2 * (hK.height y χ - hK.height x χ) + 2 * hK.height x χ by ring,
    Real.exp_add, h]
  field_simp

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
theorem placeMatrix_rational (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (x : RationalGroupPoints F G) :
    placeMatrix σ w (rational F G x) =
      ((rationalMatrix F G σ x : RationalGL F N) : Matrix (Fin N) (Fin N) F).map
        w.embedding := by
  ext a b
  simp only [placeMatrix, adelicMatrix_rational, Matrix.map_apply, AdelicGL.rational_apply,
    placeHom_algebraMap]

/-- The rational column of the inverse orbit of the selected coordinate vector. -/
def rationalColumn (σ : MatrixRepresentation G (Fin N)) (j : Fin N) (x : RationalGroupPoints F G) :
    Fin N → F :=
  fun i => ((rationalMatrix F G σ x⁻¹ : RationalGL F N) : Matrix (Fin N) (Fin N) F) i j

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
theorem placeMatrix_rational_inv_single (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (j : Fin N) (x : RationalGroupPoints F G) :
    placeMatrix σ w (rational F G x)⁻¹ *ᵥ Pi.single j 1 =
      fun i => w.embedding (rationalColumn σ j x i) := by
  rw [← map_inv, placeMatrix_rational, Matrix.mulVec_single_one]
  rfl

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
theorem rationalColumn_ne_zero (σ : MatrixRepresentation G (Fin N)) (j : Fin N)
    (x : RationalGroupPoints F G) : rationalColumn σ j x ≠ 0 := by
  have h := PrimitiveAdelicHeight.rational_mulVec_ne_zero F N (rationalMatrix F G σ x⁻¹)
    (v := Pi.single j 1) (Pi.single_eq_zero_iff.not.mpr one_ne_zero)
  rwa [Matrix.mulVec_single_one] at h

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- The strict weight gap on the rational inverse orbit column. -/
theorem weight_lt_of_rationalColumn_ne_zero {e : Fin N → ℤ}
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (x : RationalGroupPoints F G) {i : Fin N}
    (hij : i ≠ j) (hu : rationalColumn σ j x i ≠ 0) : e i < e j := by
  by_contra hle
  push Not at hle
  apply hu
  have h0 := hgap _ x⁻¹ i hij hle
  rw [MatrixRepresentation.pointMatrix_eq_affineMatrix] at h0
  let S : CommAlgCat.{u} (CommRingCat.of F) := CommAlgCat.of F F
  let φ := (Corepresented.affineSectionsIso S).inv.hom.toRingHom
  have hφ : Function.Injective φ := by
    intro a b hab
    have hc := congrArg (Corepresented.affineSectionsIso S).hom.hom hab
    have hleft (a : S) : (Corepresented.affineSectionsIso S).hom.hom (φ a) = a :=
      ConcreteCategory.congr_hom (Corepresented.affineSectionsIso S).inv_hom_id a
    exact (hleft a).symm.trans (hc.trans (hleft b))
  apply hφ
  rw [map_zero]
  exact h0

open Classical in
/-- The exponents of the inverse orbit column along the ray: the weight gap on its support. -/
def rowWeights (σ : MatrixRepresentation G (Fin N)) (j : Fin N) (e : Fin N → ℤ)
    (x : RationalGroupPoints F G) : Fin N → ℕ :=
  fun i => if rationalColumn σ j x i = 0 then 0 else (e j - e i).toNat

/-- The vectors whose combination along the ray gives the inverse orbit vector. -/
def rowVectors (σ : MatrixRepresentation G (Fin N)) (j : Fin N) (w : InfinitePlace F)
    (g : AdelicGroupPoints F G) (x : RationalGroupPoints F G) : Fin N → Fin N → ℂ :=
  fun i => placeMatrix σ w g⁻¹ *ᵥ (w.embedding (rationalColumn σ j x i) • Pi.single i 1)

variable {e : Fin N → ℤ} {c : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
theorem ray_inv_mulVec_column
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (w : InfinitePlace F) (s : ℝ)
    (x : RationalGroupPoints F G) :
    placeMatrix σ w (ray F c s)⁻¹ *ᵥ (fun i => w.embedding (rationalColumn σ j x i)) =
      ((Real.exp s : ℂ) ^ (-e j)) • ∑ i, (((Real.exp s) ^ rowWeights σ j e x i : ℝ) : ℂ) •
        (w.embedding (rationalColumn σ j x i) • Pi.single i 1) := by
  rw [placeMatrix_ray_inv σ c e hc w s]
  funext i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hu : rationalColumn σ j x i = 0
  · simp [hu]
  · have hle : e i ≤ e j := by
      by_cases hij : i = j
      · rw [hij]
      · exact (weight_lt_of_rationalColumn_ne_zero hgap x hij hu).le
    have hz : (Real.exp s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'
    have hd : ((rowWeights σ j e x i : ℕ) : ℤ) = e j - e i := by
      unfold rowWeights
      simp only [hu, ite_false]
      exact Int.toNat_of_nonneg (by omega)
    rw [Complex.ofReal_pow, ← zpow_natCast, hd, ← mul_assoc, ← zpow_add₀ hz]
    congr 2
    ring

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
theorem energy_rational_ray {w : InfinitePlace F} {Q : (Fin N → ℂ) → ℝ}
    {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ} (hQ : IsQuadraticEnergy σ w K Q B)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (g : AdelicGroupPoints F G)
    (x : RationalGroupPoints F G) (s : ℝ) :
    Q (placeMatrix σ w (rational F G x * (ray F c s * g))⁻¹ *ᵥ Pi.single j 1) =
      ‖(Real.exp s : ℂ) ^ (-e j)‖ ^ 2 *
        (energyPoly B (rowVectors σ j w g x) (rowWeights σ j e x)).eval (Real.exp s) := by
  rw [mul_inv_rev, mul_inv_rev, ← placeMatrix_mulVec_mulVec, ← placeMatrix_mulVec_mulVec,
    placeMatrix_rational_inv_single, ray_inv_mulVec_column hc hgap w s x, Matrix.mulVec_smul,
    hQ.smul, Matrix.mulVec_sum, eval_energyPoly (fun a => hQ.expand N a _)]
  simp only [Matrix.mulVec_smul, rowVectors]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
theorem energy_ray {w : InfinitePlace F} {Q : (Fin N → ℂ) → ℝ}
    (hQ : IsInvariantEnergy σ w K Q)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (g : AdelicGroupPoints F G) (s : ℝ) :
    Q (placeMatrix σ w (ray F c s * g)⁻¹ *ᵥ Pi.single j 1) =
      ‖(Real.exp s : ℂ) ^ (-e j)‖ ^ 2 * Q (placeMatrix σ w g⁻¹ *ᵥ Pi.single j 1) := by
  rw [mul_inv_rev, ← placeMatrix_mulVec_mulVec, placeMatrix_ray_inv σ c e hc w s,
    Matrix.diagonal_mulVec_single, mul_one, ← hQ.smul]
  congr 1
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [Pi.single_apply]

/-- Along the ray, the height difference between a rational translate and the ray point is a
positive constant times a product of polynomial energies. -/
theorem exists_rowHeight (hK : IsIwasawaCompact p K) {χ : rationalCharacters P}
    {Q : InfinitePlace F → (Fin N → ℂ) → ℝ} {B : InfinitePlace F → (Fin N → ℂ) → (Fin N → ℂ) → ℝ}
    (hQ : ∀ w, IsQuadraticEnergy σ w K (Q w) (B w))
    (ha : ∀ q : AdelicGroupPoints F P,
      ((adelicMatrix F G σ (map F P G p q) : AdelicGL F N) :
          Matrix (Fin N) (Fin N) (AdeleRing (𝓞 F) F)) *ᵥ Pi.single j 1 =
        (character F P χ.toMul q).val • Pi.single j 1)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (g : AdelicGroupPoints F G)
    (x : RationalGroupPoints F G) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℝ,
      Real.exp (2 * (hK.height (ray F c s * g) χ -
          hK.height (rational F G x * (ray F c s * g)) χ)) =
        κ * ∏ w : InfinitePlace F, ((energyPoly (B w) (rowVectors σ j w g x)
          (rowWeights σ j e x)).eval (Real.exp s)) ^ w.mult := by
  have hQ' : ∀ w, IsInvariantEnergy σ w K (Q w) := fun w => (hQ w).toIsInvariantEnergy
  let HE := heightEnergy hK χ Q σ j
  have hHE : ∀ z, 0 < HE z := fun z => mul_pos (Real.exp_pos _)
    (Finset.prod_pos fun w _ => pow_pos ((hQ w).pos _
      (placeMatrix_inv_mulVec_ne_zero σ w z (Pi.single_eq_zero_iff.not.mpr one_ne_zero))) _)
  let q : InfinitePlace F → ℝ := fun w => Q w (placeMatrix σ w g⁻¹ *ᵥ Pi.single j 1)
  have hq : 0 < ∏ w, q w ^ w.mult := Finset.prod_pos fun w _ => pow_pos ((hQ w).pos _
    (placeMatrix_inv_mulVec_ne_zero σ w g (Pi.single_eq_zero_iff.not.mpr one_ne_zero))) _
  refine ⟨HE g / (HE (rational F G x * g) * ∏ w, q w ^ w.mult),
    div_pos (hHE g) (mul_pos (hHE _) hq), fun s => ?_⟩
  have hfin1 : finite F G (ray F c s * g) = finite F G g := by
    rw [map_mul, finite_ray, one_mul]
  have hfin2 : finite F G (rational F G x * (ray F c s * g)) = finite F G (rational F G x * g) := by
    rw [map_mul, map_mul, finite_ray, one_mul, map_mul]
  have h1 : HE (ray F c s * g) = HE g := heightEnergy_eq_of_finite_eq hK hQ' ha _ _ hfin1
  have h2 : HE (rational F G x * (ray F c s * g)) = HE (rational F G x * g) :=
    heightEnergy_eq_of_finite_eq hK hQ' ha _ _ hfin2
  let c2 : ℝ := ‖(Real.exp s : ℂ) ^ (-e j)‖ ^ 2
  have hc2 : 0 < c2 := by
    have : (Real.exp s : ℂ) ^ (-e j) ≠ 0 :=
      zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne')
    positivity
  let P : InfinitePlace F → ℝ := fun w => (energyPoly (B w) (rowVectors σ j w g x)
    (rowWeights σ j e x)).eval (Real.exp s)
  have e1 : HE (ray F c s * g) =
      Real.exp (2 * hK.height (ray F c s * g) χ) *
        ((∏ w : InfinitePlace F, c2 ^ w.mult) * ∏ w, q w ^ w.mult) := by
    simp only [HE, heightEnergy, energy_ray (hQ' _) hc, mul_pow, Finset.prod_mul_distrib, c2, q]
  have e2 : HE (rational F G x * (ray F c s * g)) =
      Real.exp (2 * hK.height (rational F G x * (ray F c s * g)) χ) *
        ((∏ w : InfinitePlace F, c2 ^ w.mult) * ∏ w, P w ^ w.mult) := by
    simp only [HE, heightEnergy, energy_rational_ray (hQ _) hc hgap, mul_pow,
      Finset.prod_mul_distrib, c2, P]
  have hC : 0 < ∏ w : InfinitePlace F, c2 ^ w.mult := Finset.prod_pos fun w _ => pow_pos hc2 _
  have hP : ∏ w, P w ^ w.mult ≠ 0 := by
    intro h0
    have := hHE (rational F G x * (ray F c s * g))
    rw [e2, h0, mul_zero, mul_zero] at this
    exact lt_irrefl _ this
  change _ = HE g / (HE (rational F G x * g) * ∏ w, q w ^ w.mult) * ∏ w, P w ^ w.mult
  rw [← h1, ← h2, e1, e2, mul_sub, Real.exp_sub]
  have hE2 := Real.exp_pos (2 * hK.height (rational F G x * (ray F c s * g)) χ)
  field_simp

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The energy polynomial of a row has degree at most twice the largest weight gap, with a
positive coefficient there. -/
theorem rowPoly_top {w : InfinitePlace F} {Q : (Fin N → ℂ) → ℝ}
    {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ} (hQ : IsQuadraticEnergy σ w K Q B)
    (g : AdelicGroupPoints F G) (x : RationalGroupPoints F G) :
    (energyPoly B (rowVectors σ j w g x) (rowWeights σ j e x)).natDegree ≤
        2 * Finset.univ.sup (rowWeights σ j e x) ∧
      0 < (energyPoly B (rowVectors σ j w g x) (rowWeights σ j e x)).coeff
        (2 * Finset.univ.sup (rowWeights σ j e x)) := by
  classical
  set d := rowWeights σ j e x with hd_def
  set D := Finset.univ.sup d with hD_def
  have hd : ∀ r, d r ≤ D := fun r => Finset.le_sup (Finset.mem_univ r)
  refine ⟨natDegree_energyPoly_le hd, ?_⟩
  rw [coeff_energyPoly_top (fun a => hQ.expand N a _) hd]
  apply hQ.pos
  let u := rationalColumn σ j x
  let a : Fin N → ℝ := fun r => if d r = D then 1 else 0
  have hsum : (∑ r, ((a r : ℝ) : ℂ) • rowVectors σ j w g x r) =
      placeMatrix σ w g⁻¹ *ᵥ ∑ r, ((a r : ℝ) : ℂ) • (w.embedding (u r) • Pi.single r 1) := by
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, rowVectors, u]
  change (∑ r, ((a r : ℝ) : ℂ) • rowVectors σ j w g x r) ≠ 0
  rw [hsum]
  apply placeMatrix_inv_mulVec_ne_zero
  have hv : ∀ i, (∑ r, ((a r : ℝ) : ℂ) • (w.embedding (u r) • Pi.single r (1 : ℂ))) i =
      (a i : ℂ) * w.embedding (u i) := by
    intro i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hex : ∃ i, a i = 1 ∧ u i ≠ 0 := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ d ⟨j, Finset.mem_univ j⟩
    have hD : D = d i₀ := le_antisymm (Finset.sup_le fun i _ => hi₀ i (Finset.mem_univ i))
      (Finset.le_sup (Finset.mem_univ i₀))
    by_cases hu₀ : u i₀ = 0
    · have hdi₀ : d i₀ = 0 := by
        have hu₀' : rationalColumn σ j x i₀ = 0 := hu₀
        simp only [hd_def, rowWeights, hu₀', ite_true]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (rationalColumn_ne_zero σ j x)
      refine ⟨i, ?_, hi⟩
      have : d i = D := by
        have := hd i
        omega
      simp [a, this]
    · exact ⟨i₀, by simp [a, hD], hu₀⟩
  obtain ⟨i, hai, hui⟩ := hex
  intro h0
  have := congrFun h0 i
  rw [hv i, hai] at this
  simp only [Complex.ofReal_one, one_mul, Pi.zero_apply] at this
  exact hui (w.embedding.injective (this.trans (map_zero _).symm))

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- A rational point outside the parabolic gives a row of positive degree. -/
theorem one_le_sup_rowWeights
    (hstab : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j)
    (hgap : σ.HasStrictOrbitWeightUpperBound e j) (x : RationalGroupPoints F G)
    (hx : (Quotient.mk _ (⟨rational F G x, ⟨x, rfl⟩⟩ : rationalSubgroup F G) :
      ParabolicRationalCosets F p) ≠ Quotient.mk _ 1) :
    1 ≤ Finset.univ.sup (rowWeights σ j e x) := by
  classical
  suffices h : ∃ i, i ≠ j ∧ rationalColumn σ j x i ≠ 0 by
    obtain ⟨i, hij, hu⟩ := h
    have hlt := weight_lt_of_rationalColumn_ne_zero hgap x hij hu
    have hdi : 1 ≤ rowWeights σ j e x i := by
      unfold rowWeights
      simp only [hu, ite_false]
      omega
    exact hdi.trans (Finset.le_sup (Finset.mem_univ i))
  by_contra hcon
  push Not at hcon
  apply hx
  apply (parabolicRationalProjectiveEmbedding σ j hstab).injective
  have h1 : (1 : rationalSubgroup F G) = ⟨rational F G 1, ⟨1, rfl⟩⟩ :=
    Subtype.ext (map_one _).symm
  rw [h1, parabolicRationalProjectiveEmbedding_mk, parabolicRationalProjectiveEmbedding_mk]
  unfold rationalOrbitPoint
  rw [Projectivization.mk_eq_mk_iff]
  let u := rationalColumn σ j x
  have hcol : ((rationalMatrix F G σ x⁻¹ : RationalGL F N) : Matrix (Fin N) (Fin N) F) *ᵥ
      Pi.single j 1 = u := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hu : u = u j • Pi.single j 1 := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hcon i hij, hij, u]
  have huj : u j ≠ 0 := by
    intro h
    apply rationalColumn_ne_zero σ j x
    change u = 0
    rw [hu, h, zero_smul]
  refine ⟨Units.mk0 (u j) huj, ?_⟩
  rw [inv_one, map_one, Units.val_one, Matrix.one_mulVec, hcol, Units.smul_def,
    Units.val_mk0, ← hu]

end Langlands.Global.EisensteinGenericInjectivity

namespace Langlands.Global.EisensteinGenericInjectivity

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- **Frequency separation.** For a suitable line character `χ` of the parabolic, moving
any finite family of points along the archimedean ray of the split component makes every
nontrivial family of rational parabolic cosets change the total height at `χ`, except for
finitely many ray parameters. -/
theorem frequency_separation (r : ParabolicRootPresentation p l a) (hA : IsSplitTorus A.toGrp)
    (hG : IsConnectedReductive G) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) :
    ∃ χ : rationalCharacters P, ∀ (m : ℕ) (g : Fin m → AdelicGroupPoints F G)
      (cs : Fin m → ParabolicRationalCosets F p),
      cs ≠ (fun _ => Quotient.mk _ 1) →
        {s : ℝ | ∑ k, hK.height (((Quotient.out (cs k) : rationalSubgroup F G) :
            AdelicGroupPoints F G) * (ray F (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
              a ≫ l ≫ p) s * g k)) χ =
          ∑ k, hK.height (ray F (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
              a ≫ l ≫ p) s * g k) χ}.Finite := by
  classical
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨N, j, σ, e, hstab, hdiag, hgap⟩ := exists_lineData r hA hG
  have hline : (σ.restrict p).PreservesCoordinateLine j :=
    MatrixRepresentation.HasExactCoordinateLineStabilizer.preservesCoordinateLine_restrict
      hstab p le_rfl
  let χ := (σ.restrict p).coordinateLineRationalCharacter j hline
  have ha : ∀ q : AdelicGroupPoints F P,
      ((adelicMatrix F G σ (map F P G p q) : AdelicGL F N) :
          Matrix (Fin N) (Fin N) (AdeleRing (𝓞 F) F)) *ᵥ Pi.single j 1 =
        (character F P χ.toMul q).val • Pi.single j 1 := fun q =>
    (σ.restrict p).affine_coordinateLineCharacter_action j hline
      (CommAlgCat.of F (AdeleRing (𝓞 F) F)) q
  choose Q B hQ using fun w => exists_quadraticEnergy σ w K hK.isCompact
  refine ⟨χ, fun m g cs hcs => ?_⟩
  set c := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hc_def
  have hrep : ∀ k, ∃ x : RationalGroupPoints F G, rational F G x =
      ((Quotient.out (cs k) : rationalSubgroup F G) : AdelicGroupPoints F G) :=
    fun k => (Quotient.out (cs k)).property
  choose x hx using hrep
  choose κ hκ hrow using fun k => exists_rowHeight hK hQ ha hdiag hgap (g k) (x k)
  let Pk : Fin m → InfinitePlace F → ℝ[X] := fun k w =>
    energyPoly (B w) (rowVectors σ j w (g k) (x k)) (rowWeights σ j e (x k))
  let Dk : Fin m → ℕ := fun k => Finset.univ.sup (rowWeights σ j e (x k))
  let Pi' : ℝ[X] := ∏ kw : Fin m × InfinitePlace F, Pk kw.1 kw.2 ^ kw.2.mult
  have htop := coeff_prod_pow_of_natDegree_le Finset.univ (fun kw : Fin m × InfinitePlace F =>
      Pk kw.1 kw.2) (fun kw => kw.2.mult) (fun kw => 2 * Dk kw.1)
    (fun kw _ => (rowPoly_top (hQ kw.2) (g kw.1) (x kw.1)).1)
  let deg := ∑ kw : Fin m × InfinitePlace F, kw.2.mult * (2 * Dk kw.1)
  have hcoeff : Pi'.coeff deg ≠ 0 := by
    rw [htop.2]
    exact (Finset.prod_pos fun kw _ => pow_pos (rowPoly_top (hQ kw.2) (g kw.1) (x kw.1)).2 _).ne'
  have hdeg : 0 < deg := by
    obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hcs
    have hcoset : (Quotient.mk _ (⟨rational F G (x k₀), ⟨x k₀, rfl⟩⟩ : rationalSubgroup F G) :
        ParabolicRationalCosets F p) ≠ Quotient.mk _ 1 := by
      have h' : (⟨rational F G (x k₀), ⟨x k₀, rfl⟩⟩ : rationalSubgroup F G) =
          Quotient.out (cs k₀) := Subtype.ext (hx k₀)
      rw [h', Quotient.out_eq]
      exact hk₀
    have h1 := one_le_sup_rowWeights hstab hgap (x k₀) hcoset
    let w₀ : InfinitePlace F := Classical.arbitrary _
    have hm : 0 < w₀.mult := InfinitePlace.mult_pos
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun kw _ => Nat.zero_le _)
      (Finset.mem_univ (k₀, w₀)))
    exact Nat.mul_pos hm (by simp only [Dk]; omega)
  refine ((finite_setOf_eval_eq hdeg hcoeff (∏ k, κ k)⁻¹).preimage
    Real.exp_injective.injOn).subset fun s hs => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hs ⊢
  simp only [← hx] at hs
  have hsum0 : ∑ k, (hK.height (ray F c s * g k) χ -
      hK.height (rational F G (x k) * (ray F c s * g k)) χ) = 0 := by
    rw [Finset.sum_sub_distrib, hs, sub_self]
  have hprod : ∏ k, (κ k * ∏ w : InfinitePlace F, ((Pk k w).eval (Real.exp s)) ^ w.mult) = 1 := by
    rw [← Finset.prod_congr rfl fun k _ => hrow k s, ← Real.exp_sum, ← Finset.mul_sum, hsum0,
      mul_zero, Real.exp_zero]
  rw [Finset.prod_mul_distrib] at hprod
  have heval : Pi'.eval (Real.exp s) =
      ∏ k, ∏ w : InfinitePlace F, ((Pk k w).eval (Real.exp s)) ^ w.mult := by
    simp only [Pi', eval_prod, eval_pow]
    rw [Fintype.prod_prod_type]
  rw [heval]
  exact eq_inv_of_mul_eq_one_right hprod

end Langlands.Global.EisensteinGenericInjectivity
