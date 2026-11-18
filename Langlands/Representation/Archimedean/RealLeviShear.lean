import Langlands.Representation.Archimedean.RealLeviLeviBorel

/-!
# Block lower unitriangular times opposite-radical coordinates as `N̄_B`-coordinates

Tools for the proof of `RealLeviParabolicIntegrationStatement`.

For a monotone block function `cl : Fin N → ι`, every lower unitriangular matrix factors uniquely
as `lowerM cl Z * lowerC cl X`: a block diagonal lower unitriangular matrix (coordinates
`Z : CoordM cl → ℝ`) times an element of the opposite unipotent radical of the block upper
triangular parabolic subgroup (coordinates `X : CoordC cl → ℝ`). Its entries are `Z` at the
positions inside the blocks and `(shearL Z X)` at the positions below the blocks, where
`shearL Z` is the linear map `X ↦ ((lowerM Z) * (n̄(X) - 1))_{pq}` (`cl q < cl p`). Its matrix
is block triangular for the row index with identity diagonal blocks, so its determinant is `1`
(`det_shearL`) and it preserves Lebesgue measure. Hence `(Z, X) ↦ embedS (Z, shearL Z X)` is a
measure-preserving map onto the coordinates `CoordC (vcl N)` of `N̄_B` (`measurePreserving_shear`)
with `n̄_B(embedS (Z, shearL Z X)) = lowerM Z * lowerC X` (`lowerC_shear`).
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviShear

open RealLeviChartIntegrable RealLeviTwoBlock RealLeviBorel RealLeviLeviBorel

variable {ι : Type*} [LinearOrder ι] {N : ℕ}

/-! ## The strictly lower part of `n̄(X)` -/

section Strict

variable (cl : Fin N → ι)

/-- `n̄(X) - 1`: the matrix with the entries `X_{pq}` at the coordinates and `0` elsewhere. -/
def strictC (X : CoordC cl → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun p q => if h : cl q < cl p then X ⟨(p, q), h⟩ else 0

theorem lowerC_eq_strictC_add_one (X : CoordC cl → ℝ) : lowerC cl X = strictC cl X + 1 := by
  ext p q
  simp only [lowerC, strictC, of_apply, Matrix.add_apply, one_apply]
  by_cases h : cl q < cl p
  · have hpq : p ≠ q := fun e => by rw [e] at h; exact lt_irrefl _ h
    rw [dite_eq_left h, dite_eq_left h, ite_eq_right hpq, add_zero]
  · rw [dite_eq_right h, dite_eq_right h, zero_add]

theorem strictC_add (X Y : CoordC cl → ℝ) : strictC cl (X + Y) = strictC cl X + strictC cl Y := by
  ext p q
  simp only [strictC, of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem strictC_smul (t : ℝ) (X : CoordC cl → ℝ) : strictC cl (t • X) = t • strictC cl X := by
  ext p q
  simp only [strictC, of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem continuous_strictC : Continuous (strictC cl) := by
  refine continuous_matrix fun p q => ?_
  simp only [strictC, of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem strictC_single (y : CoordC cl) (r q : Fin N) :
    strictC cl (Pi.single y 1) r q = if r = y.1.1 ∧ q = y.1.2 then 1 else 0 := by
  rw [strictC, of_apply]
  by_cases h : cl q < cl r
  · rw [dite_eq_left h, Pi.single_apply]
    by_cases hy : r = y.1.1 ∧ q = y.1.2
    · have e : (⟨(r, q), h⟩ : CoordC cl) = y := Subtype.ext (Prod.ext hy.1 hy.2)
      rw [ite_eq_left e, ite_eq_left hy]
    · have e : (⟨(r, q), h⟩ : CoordC cl) ≠ y := fun e => hy (by rw [← e]; exact ⟨rfl, rfl⟩)
      rw [ite_eq_right e, ite_eq_right hy]
  · have hy : ¬ (r = y.1.1 ∧ q = y.1.2) := by
      rintro ⟨rfl, rfl⟩
      exact h y.2
    rw [dite_eq_right h, ite_eq_right hy]

end Strict

/-! ## Products with block diagonal lower unitriangular matrices -/

section Product

variable {cl : Fin N → ι}

theorem lowerM_self (Z : CoordM cl → ℝ) (p : Fin N) : lowerM cl Z p p = 1 := by
  rw [lowerM, of_apply, dite_eq_right fun h => lt_irrefl _ h.2, ite_eq_left rfl]

theorem lowerM_eq_zero_of_ne (Z : CoordM cl → ℝ) {p r : Fin N} (h : cl p ≠ cl r) :
    lowerM cl Z p r = 0 := by
  have h1 : ¬ (cl p = cl r ∧ r < p) := fun h' => h h'.1
  have h2 : p ≠ r := fun h' => h (h' ▸ rfl)
  rw [lowerM, of_apply, dite_eq_right h1, ite_eq_right h2]

theorem lowerM_mul_strictC_eq_zero (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) {p q : Fin N}
    (hpq : ¬ cl q < cl p) : (lowerM cl Z * strictC cl X) p q = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : cl p = cl r
  · have h' : ¬ cl q < cl r := by rw [← hr]; exact hpq
    rw [strictC, of_apply, dite_eq_right h', mul_zero]
  · rw [lowerM_eq_zero_of_ne Z hr, zero_mul]

theorem lowerM_mul_lowerC (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) :
    lowerM cl Z * lowerC cl X = lowerM cl Z * strictC cl X + lowerM cl Z := by
  rw [lowerC_eq_strictC_add_one, Matrix.mul_add, Matrix.mul_one]

end Product

/-! ## The shear -/

section Shear

variable (cl : Fin N → ι)

/-- `X ↦ ((lowerM Z) (n̄(X) - 1))_{pq}` (`cl q < cl p`): the coordinates below the blocks of
`lowerM Z * lowerC X`. -/
def shearL (Z : CoordM cl → ℝ) : (CoordC cl → ℝ) →ₗ[ℝ] (CoordC cl → ℝ) where
  toFun X x := (lowerM cl Z * strictC cl X) x.1.1 x.1.2
  map_add' X Y := by
    funext x
    simp only [strictC_add, Matrix.mul_add, Matrix.add_apply, Pi.add_apply]
  map_smul' t X := by
    funext x
    simp only [strictC_smul, Matrix.mul_smul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

theorem shearL_apply (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) (x : CoordC cl) :
    shearL cl Z X x = (lowerM cl Z * strictC cl X) x.1.1 x.1.2 :=
  rfl

theorem toMatrix'_shearL (Z : CoordM cl → ℝ) (x y : CoordC cl) :
    LinearMap.toMatrix' (shearL cl Z) x y =
      if x.1.2 = y.1.2 then lowerM cl Z x.1.1 y.1.1 else 0 := by
  rw [LinearMap.toMatrix'_apply, shearL_apply, mul_apply]
  simp only [strictC_single]
  by_cases hq : x.1.2 = y.1.2
  · rw [ite_eq_left hq]
    simp only [hq, and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  · rw [ite_eq_right hq]
    simp only [hq, and_false, ite_false, mul_zero, Finset.sum_const_zero]

/-- `det (shearL Z) = 1`: its matrix is block triangular for the row index, with identity
diagonal blocks. -/
theorem det_shearL (Z : CoordM cl → ℝ) : LinearMap.det (shearL cl Z) = 1 := by
  rw [← LinearMap.det_toMatrix']
  set A := LinearMap.toMatrix' (shearL cl Z) with hA
  set b : CoordC cl → (Fin N)ᵒᵈ := fun x => OrderDual.toDual x.1.1 with hbdef
  have hb : A.BlockTriangular b := by
    intro i j hij
    rw [hA, toMatrix'_shearL]
    split_ifs
    · exact lowerM_isLowerTriangular cl Z hij
    · rfl
  rw [hb.det]
  refine Finset.prod_eq_one fun k _ => ?_
  have h1 : A.toSquareBlock b k = 1 := by
    ext i j
    rw [toSquareBlock_def, of_apply, hA, toMatrix'_shearL, one_apply]
    have hp : i.1.1.1 = j.1.1.1 := OrderDual.toDual.injective (i.2.trans j.2.symm)
    by_cases hq : i.1.1.2 = j.1.1.2
    · have hij : i = j := Subtype.ext (Subtype.ext (Prod.ext hp hq))
      rw [ite_eq_left hq, ite_eq_left hij, hp, lowerM_self]
    · have hij : i ≠ j := fun h => hq (by rw [h])
      rw [ite_eq_right hq, ite_eq_right hij]
  rw [h1, det_one]

theorem map_shearL (Z : CoordM cl → ℝ) : Measure.map (shearL cl Z) volume = volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [det_shearL]; exact one_ne_zero),
    det_shearL, inv_one, abs_one, ENNReal.ofReal_one, one_smul]

theorem continuous_shearL :
    Continuous (Function.uncurry fun (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) => shearL cl Z X) := by
  refine continuous_pi fun x => ?_
  show Continuous fun z : (CoordM cl → ℝ) × (CoordC cl → ℝ) =>
    (lowerM cl z.1 * strictC cl z.2) x.1.1 x.1.2
  exact (((continuous_lowerM cl).comp continuous_fst).matrix_mul
    ((continuous_strictC cl).comp continuous_snd)).matrix_elem _ _

end Shear

/-! ## Splitting the coordinates of `N̄_B` -/

section Split

variable {cl : Fin N → ι}

/-- The coordinates inside the blocks and below the blocks as coordinates of `N̄_B`. -/
def toCoordS (hcl : Monotone cl) : CoordM cl ⊕ CoordC cl → CoordC (vcl N)
  | .inl z => ⟨z.1, Fin.lt_def.mp z.2.2⟩
  | .inr x => ⟨x.1, Fin.lt_def.mp (hcl.reflect_lt x.2)⟩

theorem toCoordS_bijective (hcl : Monotone cl) : Function.Bijective (toCoordS hcl) := by
  constructor
  · rintro (⟨pq, hz⟩ | ⟨pq, hx⟩) (⟨pq', hz'⟩ | ⟨pq', hx'⟩) h <;>
      replace h := congrArg Subtype.val h <;>
      simp only [toCoordS] at h
    · subst h
      rfl
    · subst h
      exact absurd hz.1 (ne_of_gt hx')
    · subst h
      exact absurd hz'.1 (ne_of_gt hx)
    · subst h
      rfl
  · rintro ⟨⟨p, q⟩, h⟩
    by_cases hc : cl p = cl q
    · exact ⟨.inl ⟨(p, q), hc, Fin.lt_def.mpr h⟩, rfl⟩
    · have hlt : cl q < cl p := lt_of_le_of_ne (hcl (Fin.lt_def.mpr h).le) (Ne.symm hc)
      exact ⟨.inr ⟨(p, q), hlt⟩, rfl⟩

/-- `(Z, Y) ↦` the coordinates of `N̄_B` with `Z` inside and `Y` below the blocks. -/
def embedS (hcl : Monotone cl) :
    ((CoordM cl → ℝ) × (CoordC cl → ℝ)) ≃ᵐ (CoordC (vcl N) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : CoordM cl ⊕ CoordC cl => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Equiv.ofBijective _ (toCoordS_bijective hcl)))

variable (hcl : Monotone cl)

theorem measurePreserving_embedS : MeasurePreserving (embedS hcl) volume volume := by
  have e1 := measurePreserving_piCongrLeft (fun _ : CoordC (vcl N) => (volume : Measure ℝ))
    (Equiv.ofBijective _ (toCoordS_bijective hcl))
  have e2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : CoordM cl ⊕ CoordC cl => ℝ)
  exact e1.comp e2

theorem embedS_inl (Z : CoordM cl → ℝ) (Y : CoordC cl → ℝ) (z : CoordM cl) :
    embedS hcl (Z, Y) (toCoordS hcl (.inl z)) = Z z := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (Equiv.ofBijective _ (toCoordS_bijective hcl)) (β := fun _ => ℝ)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : CoordM cl ⊕ CoordC cl => ℝ)).symm (Z, Y))
    (.inl z)
  exact h

theorem embedS_inr (Z : CoordM cl → ℝ) (Y : CoordC cl → ℝ) (x : CoordC cl) :
    embedS hcl (Z, Y) (toCoordS hcl (.inr x)) = Y x := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (Equiv.ofBijective _ (toCoordS_bijective hcl)) (β := fun _ => ℝ)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : CoordM cl ⊕ CoordC cl => ℝ)).symm (Z, Y))
    (.inr x)
  exact h

end Split

/-! ## The factorization `n̄_B = lowerM Z * lowerC X` -/

section Factor

variable {cl : Fin N → ι} (hcl : Monotone cl)

/-- The shear `(Z, X) ↦` the coordinates of `lowerM Z * lowerC X` in `N̄_B`. -/
def shear (z : (CoordM cl → ℝ) × (CoordC cl → ℝ)) : CoordC (vcl N) → ℝ :=
  embedS hcl (z.1, shearL cl z.1 z.2)

/-- **The shear preserves Lebesgue measure.** -/
theorem measurePreserving_shear :
    MeasurePreserving (shear hcl) (volume.prod volume) volume := by
  have hsk : MeasurePreserving
      (fun z : (CoordM cl → ℝ) × (CoordC cl → ℝ) => (id z.1, shearL cl z.1 z.2))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id volume) (continuous_shearL cl).measurable
      (ae_of_all _ fun Z => map_shearL cl Z)
  exact (measurePreserving_embedS hcl).comp hsk

/-- **The factorization.** `n̄_B(shear (Z, X)) = lowerM Z * lowerC X`. -/
theorem lowerC_shear (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) :
    lowerC (vcl N) (shear hcl (Z, X)) = lowerM cl Z * lowerC cl X := by
  ext p q
  rw [lowerM_mul_lowerC, Matrix.add_apply]
  by_cases hpq : vcl N q < vcl N p
  · rw [lowerC, of_apply, dite_eq_left hpq]
    by_cases hc : cl p = cl q
    · have hz : (⟨(p, q), hpq⟩ : CoordC (vcl N)) =
          toCoordS hcl (.inl ⟨(p, q), hc, Fin.lt_def.mpr hpq⟩) := rfl
      have hn : ¬ cl q < cl p := by rw [hc]; exact lt_irrefl _
      rw [hz, shear, embedS_inl, lowerM_mul_strictC_eq_zero Z X hn, zero_add, lowerM, of_apply,
        dite_eq_left ⟨hc, Fin.lt_def.mpr hpq⟩]
    · have hlt : cl q < cl p := lt_of_le_of_ne (hcl (Fin.lt_def.mpr hpq).le) (Ne.symm hc)
      have hz : (⟨(p, q), hpq⟩ : CoordC (vcl N)) = toCoordS hcl (.inr ⟨(p, q), hlt⟩) := rfl
      rw [hz, shear, embedS_inr, shearL_apply, lowerM_eq_zero_of_ne Z hc, add_zero]
  · rw [lowerC, of_apply, dite_eq_right hpq]
    have hn : ¬ cl q < cl p := fun h => hpq (Fin.lt_def.mp (hcl.reflect_lt h))
    have hn2 : ¬ (cl p = cl q ∧ q < p) := fun h => hpq (Fin.lt_def.mp h.2)
    rw [lowerM_mul_strictC_eq_zero Z X hn, zero_add, lowerM, of_apply, dite_eq_right hn2]

theorem lowerCGL_shear (Z : CoordM cl → ℝ) (X : CoordC cl → ℝ) :
    lowerCGL (vcl_monotone N) (shear hcl (Z, X)) = lowerMGL cl Z * lowerCGL hcl X := by
  ext : 1
  rw [lowerCGL_val, Units.val_mul, lowerMGL_val, lowerCGL_val]
  exact lowerC_shear hcl Z X

end Factor

end RealLeviShear

end Langlands.Archimedean
