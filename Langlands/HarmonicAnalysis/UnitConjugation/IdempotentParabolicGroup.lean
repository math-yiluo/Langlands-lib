import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizerPairing

/-! # The upper triangular unit group of an idempotent

The units of the subalgebra with zero opposite corner factor into the units of
the idempotent centralizer and the subgroup obtained by adding one to the upper
corner. Conjugation by these upper-corner units is affine on the Levi algebra.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open Function

universe u v

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

private theorem right_mul_eq_of_lower_eq_zero {a : A} (ha : (1 - e) * a * e = 0) :
    a * e = e * (a * e) := by
  rw [sub_mul, one_mul, sub_mul, sub_eq_zero, mul_assoc] at ha
  exact ha

/-- The upper triangular subalgebra determined by `e`, given by vanishing of
the opposite corner. -/
def parabolicSubalgebra (he : IsIdempotentElem e) : Subalgebra F A where
  carrier := {a | (1 - e) * a * e = 0}
  one_mem' := by
    change (1 - e) * 1 * e = 0
    rw [mul_one, (idempotent_mul_rules he).2.1]
  mul_mem' {a b} ha hb := by
    change (1 - e) * a * e = 0 at ha
    change (1 - e) * b * e = 0 at hb
    change (1 - e) * (a * b) * e = 0
    calc
      _ = (1 - e) * a * (b * e) := by simp only [mul_assoc]
      _ = (1 - e) * a * (e * (b * e)) :=
        congrArg ((1 - e) * a * ·) (right_mul_eq_of_lower_eq_zero hb)
      _ = ((1 - e) * a * e) * (b * e) := (mul_assoc _ _ _).symm
      _ = 0 := by rw [ha, zero_mul]
  zero_mem' := by
    change (1 - e) * 0 * e = 0
    rw [mul_zero, zero_mul]
  add_mem' {a b} ha hb := by
    change (1 - e) * a * e = 0 at ha
    change (1 - e) * b * e = 0 at hb
    change (1 - e) * (a + b) * e = 0
    rw [mul_add, add_mul, ha, hb, add_zero]
  algebraMap_mem' c := by
    change (1 - e) * algebraMap F A c * e = 0
    rw [mul_assoc, Algebra.commutes c e, ← mul_assoc,
      (idempotent_mul_rules he).2.1, zero_mul]

theorem mem_parabolicSubalgebra_iff (he : IsIdempotentElem e) {a : A} :
    a ∈ parabolicSubalgebra F he ↔ (1 - e) * a * e = 0 := Iff.rfl

private theorem diagonalProjection_mul_of_lower_eq_zero (he : IsIdempotentElem e) {a b : A}
    (ha : (1 - e) * a * e = 0) (hb : (1 - e) * b * e = 0) :
    diagonalProjection F e (a * b) = diagonalProjection F e a * diagonalProjection F e b := by
  have hfa : (1 - e) * a * (1 - e) = (1 - e) * a := by
    rw [mul_sub, mul_one, ha, sub_zero]
  obtain ⟨_, _, _, _, hee, hfe, hef, hff⟩ := idempotent_mul_rules he
  calc
    _ = e * (a * (b * e)) + ((1 - e) * a) * (b * (1 - e)) := by
      simp only [diagonalProjection_apply, mul_assoc]
    _ = e * (a * (e * (b * e))) + ((1 - e) * a * (1 - e)) * (b * (1 - e)) :=
      congrArg₂ (· + ·) (congrArg (fun x => e * (a * x)) (right_mul_eq_of_lower_eq_zero hb))
        (congrArg (· * (b * (1 - e))) hfa.symm)
    _ = _ := by
      simp only [diagonalProjection_apply, add_mul, mul_add, mul_assoc, hee, hfe, hef, hff,
        mul_zero, add_zero, zero_add]

/-- Taking the diagonal blocks is an algebra homomorphism on upper triangular
elements. -/
def parabolicDiagonal (he : IsIdempotentElem e) : parabolicSubalgebra F he →ₐ[F] Levi where
  toFun a := ⟨diagonalProjection F e a,
    (mem_centralizer_singleton_iff F).2 (commute_diagonalProjection he a)⟩
  map_one' := Subtype.ext (diagonalProjection_of_commute he (by simp))
  map_mul' a b := Subtype.ext (diagonalProjection_mul_of_lower_eq_zero F he a.property b.property)
  map_zero' := Subtype.ext ((diagonalProjection F e).map_zero)
  map_add' a b := Subtype.ext ((diagonalProjection F e).map_add (a : A) (b : A))
  commutes' c := Subtype.ext (diagonalProjection_of_commute he (Algebra.commutes c e).symm)

/-- The subgroup of ambient units obtained from the units of the upper triangular
subalgebra. -/
def parabolicUnits (he : IsIdempotentElem e) : Subgroup Aˣ :=
  (Units.map (parabolicSubalgebra F he).val.toMonoidHom).range

theorem mem_parabolicUnits_iff_of_finite [FiniteDimensional F A] (he : IsIdempotentElem e)
    (g : Aˣ) : g ∈ parabolicUnits F he ↔ (1 - e) * (g : A) * e = 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact p.val.property
  · intro hg
    let P := parabolicSubalgebra F he
    let a : P := ⟨(g : A), hg⟩
    have hInj : Injective (LinearMap.mulLeft F a) := by
      intro b c hbc
      have h : (g : A) * (b : A) = (g : A) * (c : A) := congrArg Subtype.val hbc
      exact Subtype.ext (g.mul_right_inj.mp h)
    obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.mp hInj 1
    change a * b = 1 at hb
    have hba : b * a = 1 := by
      apply hInj
      change a * (b * a) = a * 1
      rw [← mul_assoc, hb, one_mul, mul_one]
    exact ⟨⟨a, b, hb, hba⟩, Units.ext rfl⟩

theorem isClosed_parabolicUnits [FiniteDimensional F A] [TopologicalSpace A]
    [T2Space A] [IsTopologicalRing A] (he : IsIdempotentElem e) :
    IsClosed (parabolicUnits F he : Set Aˣ) := by
  have hEq : (parabolicUnits F he : Set Aˣ) = {g : Aˣ | (1 - e) * (g : A) * e = 0} :=
    Set.ext (mem_parabolicUnits_iff_of_finite F he)
  rw [hEq]
  exact isClosed_eq ((continuous_const.mul Units.continuous_val).mul continuous_const) continuous_const

private theorem mul_upperCorner_mem (x : Levi) {z : A} (hz : z ∈ Upper) :
    (x : A) * z ∈ Upper := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨(x : A) * w, ?_⟩
  simp only [cornerProjection_apply, ← mul_assoc, (mem_centralizer_singleton_iff F).1 x.property]

private theorem upperCorner_mul_mem (x : Levi) {z : A} (hz : z ∈ Upper) :
    z * (x : A) ∈ Upper := by
  obtain ⟨w, rfl⟩ := hz
  have hx : (x : A) * (1 - e) = (1 - e) * (x : A) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, (mem_centralizer_singleton_iff F).1 x.property]
  refine ⟨w * (x : A), ?_⟩
  simp only [cornerProjection_apply, mul_assoc, hx]

private theorem upperCorner_mul_eq_zero (he : IsIdempotentElem e) (z w : Upper) :
    (z : A) * (w : A) = 0 := by
  obtain ⟨z', hz⟩ := z.property
  obtain ⟨w', hw⟩ := w.property
  obtain ⟨_, _, _, _, _, hfe, _, _⟩ := idempotent_mul_rules he
  rw [← hz, ← hw]
  simp only [cornerProjection_apply, mul_assoc, hfe, mul_zero]

/-- The unit `1 + Z` with inverse `1 - Z` for `Z` in the upper corner. -/
def upperCornerUnit (he : IsIdempotentElem e) (z : Upper) : Aˣ where
  val := 1 + (z : A)
  inv := 1 - (z : A)
  val_inv := by
    calc
      _ = 1 - (z : A) * z := by noncomm_ring
      _ = 1 := by rw [upperCorner_mul_eq_zero F he z z, sub_zero]
  inv_val := by
    calc
      _ = 1 - (z : A) * z := by noncomm_ring
      _ = 1 := by rw [upperCorner_mul_eq_zero F he z z, sub_zero]

/-- The additive group of the upper corner maps multiplicatively into the unit group. -/
def upperCornerUnitsHom (he : IsIdempotentElem e) : Multiplicative Upper →* Aˣ where
  toFun z := upperCornerUnit F he z.toAdd
  map_one' := Units.ext (add_zero (1 : A))
  map_mul' z w := by
    apply Units.ext
    change 1 + ((z.toAdd : A) + (w.toAdd : A)) = (1 + (z.toAdd : A)) * (1 + (w.toAdd : A))
    simp only [add_mul, mul_add, one_mul, mul_one, upperCorner_mul_eq_zero F he, add_zero]
    abel

/-- The unipotent subgroup consisting of one plus the upper corner. -/
def upperCornerUnits (he : IsIdempotentElem e) : Subgroup Aˣ :=
  (upperCornerUnitsHom F he).range

private theorem upperCornerUnitsHom_injective (he : IsIdempotentElem e) :
    Injective (upperCornerUnitsHom F he) := by
  intro z w h
  have h' : 1 + (z.toAdd : A) = 1 + (w.toAdd : A) := congrArg Units.val h
  exact Subtype.ext (add_left_cancel h')

/-- The upper corner in additive coordinates is continuously isomorphic to
the unipotent subgroup. -/
def upperCornerUnitsEquiv [TopologicalSpace A] [IsTopologicalRing A] (he : IsIdempotentElem e) :
    Multiplicative Upper ≃ₜ* upperCornerUnits F he where
  __ := MonoidHom.ofInjective (upperCornerUnitsHom_injective F he)
  continuous_toFun := by
    change Continuous (fun z : Multiplicative Upper =>
      (⟨upperCornerUnitsHom F he z, ⟨z, rfl⟩⟩ : upperCornerUnits F he))
    apply Continuous.subtype_mk
    exact Units.continuous_iff.2
      ⟨continuous_const.add continuous_subtype_val, continuous_const.sub continuous_subtype_val⟩
  continuous_invFun := by
    let E := MonoidHom.ofInjective (upperCornerUnitsHom_injective F he)
    change Continuous (fun g : upperCornerUnits F he => (E.symm g).toAdd)
    apply continuous_induced_rng.2
    change Continuous (fun g : upperCornerUnits F he => ((E.symm g).toAdd : A))
    have heq (g : upperCornerUnits F he) : ((E.symm g).toAdd : A) = ((g : Aˣ) : A) - 1 := by
      have h : 1 + ((E.symm g).toAdd : A) = ((g : Aˣ) : A) :=
        congrArg Units.val (MonoidHom.apply_ofInjective_symm (upperCornerUnitsHom_injective F he) g)
      rw [← h]
      abel
    simp_rw [heq]
    exact (Units.continuous_val.comp continuous_subtype_val).sub continuous_const

/-- The image of the units of the Levi algebra in the ambient unit group. -/
def leviUnits : Subgroup Aˣ := (Units.map (Levi).val.toMonoidHom).range

theorem leviUnits_le_normalizer_upperCornerUnits (he : IsIdempotentElem e) :
    leviUnits F (e := e) ≤ Subgroup.normalizer (upperCornerUnits F he : Set Aˣ) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨m, rfl⟩ _ ⟨z, rfl⟩
  let t : Upper := ⟨(m.val : A) * (z.toAdd : A) * ((m⁻¹ : Leviˣ).val : A),
    upperCorner_mul_mem F (m⁻¹ : Leviˣ).val (mul_upperCorner_mem F m.val z.toAdd.property)⟩
  refine ⟨Multiplicative.ofAdd t, Units.ext ?_⟩
  change 1 + (m.val : A) * (z.toAdd : A) * ((m⁻¹ : Leviˣ).val : A) =
    (m.val : A) * (1 + (z.toAdd : A)) * ((m⁻¹ : Leviˣ).val : A)
  have hm : (m.val : A) * ((m⁻¹ : Leviˣ).val : A) = 1 := congrArg Subtype.val m.mul_inv
  rw [mul_add, mul_one, add_mul, hm]

/-- The coordinates of the upper triangular unit group, in Levi then unipotent order. -/
theorem exists_levi_mul_upperCornerUnit (he : IsIdempotentElem e) (g : Aˣ)
    (hg : g ∈ parabolicUnits F he) :
    ∃ (m : Leviˣ) (z : Upper),
      g = Units.map (Levi).val.toMonoidHom m * upperCornerUnit F he z := by
  obtain ⟨p, rfl⟩ := hg
  let m : Leviˣ := Units.map (parabolicDiagonal F he).toMonoidHom p
  let mG : Aˣ := Units.map (Levi).val.toMonoidHom m
  let w := cornerProjection F e (p.val : A)
  let z : Upper := ⟨((m⁻¹ : Leviˣ).val : A) * w,
    mul_upperCorner_mem F (m⁻¹ : Leviˣ).val (cornerProjection_mem F e (p.val : A))⟩
  refine ⟨m, z, Units.ext ?_⟩
  change (p.val : A) = (mG : A) * (1 + (((mG⁻¹ : Aˣ) : A) * w))
  rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  have h := diagonal_add_corners F e (p.val : A)
  rw [cornerProjection_apply F (1 - e), sub_sub_cancel, p.val.property, add_zero] at h
  exact h.symm

/-- The upper-corner conjugation orbit of a Levi element has affine coordinates. -/
theorem upperCornerUnit_inv_conj (he : IsIdempotentElem e) (y : Levi) (z : Upper) :
    (((upperCornerUnit F he z)⁻¹ : Aˣ) : A) * (y : A) * (upperCornerUnit F he z : A) =
      (y : A) + ((y : A) * (z : A) - (z : A) * (y : A)) := by
  let yz : Upper := ⟨(y : A) * (z : A), mul_upperCorner_mem F y z.property⟩
  have hzyz : (z : A) * (y : A) * (z : A) = 0 := by
    rw [mul_assoc]
    exact upperCorner_mul_eq_zero F he z yz
  change (1 - (z : A)) * (y : A) * (1 + (z : A)) = _
  calc
    _ = (y : A) + ((y : A) * (z : A) - (z : A) * (y : A)) -
        (z : A) * (y : A) * (z : A) := by noncomm_ring
    _ = _ := by rw [hzyz, sub_zero]

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
