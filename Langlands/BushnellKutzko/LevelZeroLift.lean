import Langlands.BushnellKutzko.LevelZeroSwapMembership

/-! # Integral lifts of matrices over the residue field -/

open Matrix ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {f : ℕ}

/-- An integral lift of a residue class, as an element of the integers. -/
def liftO (c : 𝓀[F]) : 𝒪[F] := (IsLocalRing.residue_surjective c).choose

@[simp] theorem residue_liftO (c : 𝓀[F]) : IsLocalRing.residue 𝒪[F] (liftO c) = c :=
  (IsLocalRing.residue_surjective c).choose_spec

theorem lift_eq_liftO (c : 𝓀[F]) : lift c = (liftO c : F) := rfl

/-- The entrywise integral lift of a matrix over the residue field. -/
def liftM (X : Matrix (Fin f) (Fin f) 𝓀[F]) : Matrix (Fin f) (Fin f) F := fun a b => lift (X a b)

theorem liftM_le_one (X : Matrix (Fin f) (Fin f) 𝓀[F]) (a b : Fin f) :
    valuation F (liftM X a b) ≤ 1 := lift_le_one _

@[simp] theorem res_liftM (X : Matrix (Fin f) (Fin f) 𝓀[F]) (a b : Fin f) :
    res (liftM X a b) = X a b := res_lift _

/-- An invertible matrix over the integers, viewed over the field, is integral with integral
inverse. -/
theorem isIntGL_map (A : GL (Fin f) 𝒪[F]) :
    IsIntGL (Matrix.GeneralLinearGroup.map (Subring.subtype 𝒪[F]) A : GL (Fin f) F) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · exact ((A : Matrix (Fin f) (Fin f) 𝒪[F]) a b).2
  · rw [← map_inv]
    exact (((A⁻¹ : GL (Fin f) 𝒪[F]) : Matrix (Fin f) (Fin f) 𝒪[F]) a b).2

/-- The integral lift of an invertible matrix over the residue field is invertible over the
integers. -/
def liftGLO (X : GL (Fin f) 𝓀[F]) : GL (Fin f) 𝒪[F] :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr (by
    have h : IsUnit (IsLocalRing.residue 𝒪[F]
        ((X : Matrix (Fin f) (Fin f) 𝓀[F]).map liftO).det) := by
      rw [RingHom.map_det]
      have : ((X : Matrix (Fin f) (Fin f) 𝓀[F]).map liftO).map (IsLocalRing.residue 𝒪[F]) =
          (X : Matrix (Fin f) (Fin f) 𝓀[F]) := by
        ext a b; simp
      rw [RingHom.mapMatrix_apply, this]
      exact (Matrix.isUnit_iff_isUnit_det _).mp X.isUnit
    exact isUnit_of_map_unit (IsLocalRing.residue 𝒪[F]) _ h) :
    IsUnit ((X : Matrix (Fin f) (Fin f) 𝓀[F]).map liftO)).unit

/-- The integral lift of an invertible matrix over the residue field, over the field. -/
def liftGL (X : GL (Fin f) 𝓀[F]) : GL (Fin f) F :=
  Matrix.GeneralLinearGroup.map (Subring.subtype 𝒪[F]) (liftGLO X)

theorem isIntGL_liftGL (X : GL (Fin f) 𝓀[F]) : IsIntGL (liftGL X) := isIntGL_map _

theorem coe_liftGL (X : GL (Fin f) 𝓀[F]) :
    ((liftGL X : GL (Fin f) F) : Matrix (Fin f) (Fin f) F) =
      liftM (X : Matrix (Fin f) (Fin f) 𝓀[F]) := by
  ext a b
  rfl

theorem res_liftGL (X : GL (Fin f) 𝓀[F]) (a b : Fin f) :
    res (((liftGL X : GL (Fin f) F) : Matrix (Fin f) (Fin f) F) a b) =
      (X : Matrix (Fin f) (Fin f) 𝓀[F]) a b := by
  rw [coe_liftGL, res_liftM]

/-- A matrix congruent to the identity modulo the maximal ideal is invertible with integral
inverse. -/
theorem exists_isIntGL_of_sub_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (h : ∀ p q, valuation F (A p q - (1 : Matrix ι ι F) p q) < 1) :
    ∃ Ag : GL ι F, (Ag : Matrix ι ι F) = A ∧
      ∀ p q, valuation F (((Ag⁻¹ : GL ι F) : Matrix ι ι F) p q) ≤ 1 := by
  have h1 : ∀ p q, valuation F ((1 : Matrix ι ι F) p q) ≤ 1 := by
    intro p q; by_cases hpq : p = q <;> simp [hpq, Matrix.one_apply]
  have hint : ∀ p q, valuation F (A p q) ≤ 1 := fun p q => by
    have := Valuation.map_add_le _ (h p q).le (h1 p q)
    simpa using this
  let AO : Matrix ι ι 𝒪[F] := fun p q => ⟨A p q, hint p q⟩
  have hred : AO.map (IsLocalRing.residue 𝒪[F]) = 1 := by
    ext p q
    simp only [Matrix.map_apply]
    have hr : res (A p q) = res ((1 : Matrix ι ι F) p q) :=
      (res_eq_res_iff (hint p q) (h1 p q)).mpr (h p q)
    rw [res_of_le (hint p q)] at hr
    rw [hr]
    by_cases hpq : p = q
    · subst hpq; simp
    · simp [Matrix.one_apply_ne hpq]
  have hdet : IsUnit AO.det := by
    have : IsUnit (IsLocalRing.residue 𝒪[F] AO.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hred, Matrix.det_one]
      exact isUnit_one
    exact isUnit_of_map_unit (IsLocalRing.residue 𝒪[F]) _ this
  let AOu : GL ι 𝒪[F] := ((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit
  refine ⟨Matrix.GeneralLinearGroup.map (Subring.subtype 𝒪[F]) AOu, ?_, fun p q => ?_⟩
  · ext p q; rfl
  · rw [← map_inv]
    exact (((AOu⁻¹ : GL ι 𝒪[F]) : Matrix ι ι 𝒪[F]) p q).2

end Langlands.BushnellKutzko.LevelZero
