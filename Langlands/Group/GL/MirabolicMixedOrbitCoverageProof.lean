import Langlands.Group.GL.MirabolicMixedOrbitSpecializations

/-! Elementary inverse-row proof of the two mixed mirabolic orbits. -/

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

open scoped Matrix

open Langlands.Geometric
open Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

namespace Coverage

variable {R : Type u} [Field R] {n : ℕ}

/-- The lower-left rectangle below the cut `s` vanishes. -/
def UpperHead (s : ℕ) (A : GeneralLinear n R) : Prop :=
  ∀ i j : Fin n, s < i.val → j.val ≤ s → A.val i j = 0

/-- The coordinates up to and including `s` vanish. -/
def ZeroHead (s : ℕ) (v : Fin n → R) : Prop :=
  ∀ j : Fin n, j.val ≤ s → v j = 0

private theorem zeroHead_vecMul {s : ℕ} {A : GeneralLinear n R}
    (hA : UpperHead s A) {v : Fin n → R} (hv : ZeroHead s v) :
    ZeroHead s (v ᵥ* A.val) := by
  intro j hj
  change ∑ i, v i * A.val i j = 0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val ≤ s
  · simp [hv i hi]
  · simp [hA i j (by omega) hj]

private theorem zeroHead_vecMul_iff {s : ℕ} {A : GeneralLinear n R}
    (hA : UpperHead s A) (hAi : UpperHead s A⁻¹) (v : Fin n → R) :
    ZeroHead s (v ᵥ* A.val) ↔ ZeroHead s v := by
  refine ⟨fun h => ?_, zeroHead_vecMul hA⟩
  have h := zeroHead_vecMul hAi h
  simpa only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.vecMul_one] using h

/-- An upper matrix with a prescribed nonzero row, with both the chosen row
and its pivot in the same side of the cut. -/
private theorem exists_upper_row (s : ℕ) (v : Fin n → R)
    (l p : Fin n) (hp : v p ≠ 0)
    (hside : (l.val ≤ s ∧ p.val ≤ s) ∨
      (s < l.val ∧ s < p.val ∧ ZeroHead s v)) :
    ∃ A : GeneralLinear n R, (∀ j, A.val l j = v j) ∧ UpperHead s A := by
  classical
  let B : Matrix (Fin n) (Fin n) R := (1 : Matrix (Fin n) (Fin n) R).updateRow p v
  have hsum : (∑ i, v i • (1 : Matrix (Fin n) (Fin n) R) i) = v := by
    ext j
    simp [Matrix.one_apply, eq_comm]
  have hdet : B.det = v p := by
    simpa only [hsum, Matrix.det_one, smul_eq_mul, mul_one] using
      Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) R) p v
  let C := B.submatrix (Equiv.swap l p) id
  have hC : C.det ≠ 0 := by
    dsimp [C]
    rw [Matrix.det_permute, hdet]
    by_cases h : l = p
    · subst p
      simpa using hp
    · simpa [Equiv.Perm.sign_swap h] using hp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero C hC, ?_, ?_⟩
  · intro j
    change B (Equiv.swap l p l) j = v j
    simp [B]
  · intro i j hi hj
    change B (Equiv.swap l p i) j = 0
    by_cases hil : i = l
    · subst i
      rcases hside with hside | hside
      · omega
      · simpa [B] using hside.2.2 j hj
    · by_cases hip : i = p
      · subst i
        have hlp : l ≠ p := Ne.symm hil
        have hlj : l ≠ j := by
          rcases hside with hside | hside <;> intro h <;>
            have he := congrArg Fin.val h <;> omega
        simp [B, hlp, hlj]
      · have hij : i ≠ j := by
          intro h
          have he := congrArg Fin.val h
          omega
        simp [Equiv.swap_apply_of_ne_of_ne hil hip, B, hip, hij]

private theorem exists_nonzero_row (A : GeneralLinear n R) (i : Fin n) :
    ∃ j, A.val i j ≠ 0 := by
  by_contra! h
  have hz : (A * A⁻¹).val i i = 0 := by
    change (A.val * (A⁻¹).val) i i = 0
    simp [Matrix.mul_apply, h]
  simp at hz

section OrbitCriterion

variable {t : ℕ}

/-- The final row of the inverse projected matrix. -/
def inverseRow (g : mirabolic (t + 1) R) : Fin (t + 1) → R :=
  (projection g⁻¹).val (Fin.last t)

private theorem row_mul (A B : GeneralLinear n R) (i : Fin n) :
    (A * B).val i = A.val i ᵥ* B.val := rfl

private theorem orbit_iff_row (H : Subgroup (mirabolic (t + 1) R))
    (w g : mirabolic (t + 1) R) :
    Induction.quotientMap H g ∈ cosetOrbit H (plusSubgroup t R) w ↔
      ∃ h : mirabolic (t + 1) R, h ∈ H ∧
        (projection (w * h)).val (Fin.last t) = inverseRow g := by
  constructor
  · rintro ⟨q, hq⟩
    let h := w⁻¹ * q.val * g⁻¹
    have hh : h ∈ H :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hq.symm)
    refine ⟨h, hh, ?_⟩
    have hwh : w * h = q.val * g⁻¹ := by simp [h, mul_assoc]
    rw [hwh, map_mul, row_mul]
    funext j
    change ∑ i, (projection q.val).val (Fin.last t) i *
      (projection g⁻¹).val i j = _
    have hqrow : ∀ i, (projection q.val).val (Fin.last t) i =
        if i = Fin.last t then 1 else 0 := q.property
    simp [hqrow, inverseRow]
  · rintro ⟨h, hh, hrow⟩
    let q := w * h * g
    have hq : q ∈ plusSubgroup t R := by
      intro j
      change (projection (w * h * g)).val (Fin.last t) j = _
      rw [map_mul, row_mul, hrow]
      change ((projection g⁻¹).val * (projection g).val) (Fin.last t) j = _
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one]
      simp [Matrix.one_apply, eq_comm]
    refine ⟨⟨q, hq⟩, ?_⟩
    apply Eq.symm
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa [q, mul_assoc] using hh

private theorem orbit_of_row (H : Subgroup (mirabolic (t + 1) R))
    (hlevi : ∀ A : GeneralLinear (t + 1) R, UpperHead s A → levi A ∈ H)
    (w g : mirabolic (t + 1) R) (l : Fin (t + 1))
    (hw : ∀ j, (projection w).val (Fin.last t) j = if j = l then 1 else 0)
    (p : Fin (t + 1)) (hp : inverseRow g p ≠ 0)
    (hside : (l.val ≤ s ∧ p.val ≤ s) ∨
      (s < l.val ∧ s < p.val ∧ ZeroHead s (inverseRow g))) :
    Induction.quotientMap H g ∈ cosetOrbit H (plusSubgroup t R) w := by
  obtain ⟨A, hArow, hA⟩ := exists_upper_row s (inverseRow g) l p hp hside
  apply (orbit_iff_row H w g).mpr
  refine ⟨levi A, hlevi A hA, ?_⟩
  rw [map_mul, projection_levi, row_mul]
  funext j
  change ∑ i, (projection w).val (Fin.last t) i * A.val i j = _
  simpa [hw] using hArow j

private theorem orbit_zeroHead_iff (H : Subgroup (mirabolic (t + 1) R))
    (hupper : ∀ h ∈ H, UpperHead s (projection h))
    (w g : mirabolic (t + 1) R)
    (hg : Induction.quotientMap H g ∈ cosetOrbit H (plusSubgroup t R) w) :
    ZeroHead s (inverseRow g) ↔ ZeroHead s ((projection w).val (Fin.last t)) := by
  obtain ⟨h, hh, hrow⟩ := (orbit_iff_row H w g).mp hg
  rw [← hrow, map_mul, row_mul]
  exact zeroHead_vecMul_iff (hupper h hh) (by
    simpa only [map_inv] using hupper h⁻¹ (H.inv_mem hh)) _

private theorem identity_orbit_iff (H : Subgroup (mirabolic (t + 1) R))
    (hupper : ∀ h ∈ H, UpperHead s (projection h))
    (hlevi : ∀ A : GeneralLinear (t + 1) R, UpperHead s A → levi A ∈ H)
    (hst : s < t) (g : mirabolic (t + 1) R) :
    Induction.quotientMap H g ∈ cosetOrbit H (plusSubgroup t R) 1 ↔
      ZeroHead s (inverseRow g) := by
  have hzero : ZeroHead s ((projection (1 : mirabolic (t + 1) R)).val (Fin.last t)) := by
    intro j hj
    have hjl : j ≠ Fin.last t := by
      intro h
      have he := congrArg Fin.val h
      simp only [Fin.val_last] at he
      omega
    simp [Ne.symm hjl]
  constructor
  · intro hg
    exact (orbit_zeroHead_iff H hupper 1 g hg).mpr hzero
  · intro hg
    obtain ⟨p, hp⟩ := exists_nonzero_row (projection g⁻¹) (Fin.last t)
    apply orbit_of_row H hlevi 1 g (Fin.last t) (by
      intro j; simp [Matrix.one_apply, eq_comm]) p hp
    refine Or.inr ⟨hst, ?_, hg⟩
    by_contra! hps
    exact hp (hg p hps)

private theorem cycle_orbit_iff (H : Subgroup (mirabolic (t + 1) R))
    (hupper : ∀ h ∈ H, UpperHead s (projection h))
    (hlevi : ∀ A : GeneralLinear (t + 1) R, UpperHead s A → levi A ∈ H)
    (hst : s < t) (w : mirabolic (t + 1) R)
    (hw : ∀ j, (projection w).val (Fin.last t) j =
      if j = (⟨s, by omega⟩ : Fin (t + 1)) then 1 else 0)
    (g : mirabolic (t + 1) R) :
    Induction.quotientMap H g ∈ cosetOrbit H (plusSubgroup t R) w ↔
      ¬ ZeroHead s (inverseRow g) := by
  constructor
  · intro hg hz
    have hzw := (orbit_zeroHead_iff H hupper w g hg).mp hz
    have he := hzw ⟨s, by omega⟩ (by simp)
    simp [hw] at he
  · intro hg
    have hp : ∃ p : Fin (t + 1), p.val ≤ s ∧ inverseRow g p ≠ 0 := by
      simpa only [ZeroHead, not_forall, exists_prop] using hg
    obtain ⟨p, hps, hp⟩ := hp
    exact orbit_of_row H hlevi w g ⟨s, by omega⟩ hw p hp (Or.inl ⟨le_rfl, hps⟩)

section Topology

variable [TopologicalSpace R] [T2Space R]
  [IsTopologicalGroup (mirabolic (t + 1) R)]

private theorem cycle_orbit_isOpen (H : Subgroup (mirabolic (t + 1) R))
    (hupper : ∀ h ∈ H, UpperHead s (projection h))
    (hlevi : ∀ A : GeneralLinear (t + 1) R, UpperHead s A → levi A ∈ H)
    (hst : s < t) (w : mirabolic (t + 1) R)
    (hw : ∀ j, (projection w).val (Fin.last t) j =
      if j = (⟨s, by omega⟩ : Fin (t + 1)) then 1 else 0) :
    IsOpen (cosetOrbit H (plusSubgroup t R) w) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isOpen_preimage.mp
  change IsOpen {g : mirabolic (t + 1) R |
    Induction.quotientMap H g ∈ cosetOrbit H (plusSubgroup t R) w}
  have hset : {g : mirabolic (t + 1) R |
      Induction.quotientMap H g ∈ cosetOrbit H (plusSubgroup t R) w} =
      ⋃ j : Fin (t + 1), ⋃ (_ : j.val ≤ s), {g | inverseRow g j ≠ 0} := by
    ext g
    simpa only [Set.mem_ofPred_eq, Set.mem_iUnion, ZeroHead, not_forall, exists_prop] using
      cycle_orbit_iff H hupper hlevi hst w hw g
  rw [hset]
  apply isOpen_iUnion
  intro j
  apply isOpen_iUnion
  intro _
  exact isOpen_ne_fun ((entry (F := R) (Fin.last t).castSucc j.castSucc).continuous.comp
    continuous_inv) continuous_const

private theorem exists_ordered (H : Subgroup (mirabolic (t + 1) R))
    (hupper : ∀ h ∈ H, UpperHead s (projection h))
    (hlevi : ∀ A : GeneralLinear (t + 1) R, UpperHead s A → levi A ∈ H)
    (hst : s < t) (w : mirabolic (t + 1) R)
    (hw : ∀ j, (projection w).val (Fin.last t) j =
      if j = (⟨s, by omega⟩ : Fin (t + 1)) then 1 else 0) :
    ∃ d : OrderedDoubleCosets H (plusSubgroup t R) 2,
      d.representative = ![w, 1] := by
  have hcover : ∀ x : Induction.LeftQuotient H,
      ∃ i : Fin 2, x ∈ cosetOrbit H (plusSubgroup t R) (![w, 1] i) := by
    intro x
    induction x using Quotient.inductionOn with
    | _ g =>
      by_cases hz : ZeroHead s (inverseRow g)
      · exact ⟨1, (identity_orbit_iff H hupper hlevi hst g).mpr hz⟩
      · exact ⟨0, (cycle_orbit_iff H hupper hlevi hst w hw g).mpr hz⟩
  have hdisjoint : Disjoint (cosetOrbit H (plusSubgroup t R) w)
      (cosetOrbit H (plusSubgroup t R) 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    induction x using Quotient.inductionOn with
    | _ g =>
      exact ((cycle_orbit_iff H hupper hlevi hst w hw g).mp hx)
        ((identity_orbit_iff H hupper hlevi hst g).mp hy)
  refine ⟨{ representative := ![w, 1]
            covers := hcover
            disjoint := ?_
            initial_open := ?_ }, rfl⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact (hij rfl).elim
  · intro k
    fin_cases k
    · simp
    · have hset : {x : Induction.LeftQuotient H | ∃ i : Fin 2,
          i.val < 1 ∧ x ∈ cosetOrbit H (plusSubgroup t R) (![w, 1] i)} =
          cosetOrbit H (plusSubgroup t R) w := by
        ext x
        constructor
        · rintro ⟨i, hi, hx⟩
          have hi0 : i = 0 := by apply Fin.ext; simp; omega
          simpa [hi0] using hx
        · intro hx
          exact ⟨0, by decide, hx⟩
      rw [hset]
      exact cycle_orbit_isOpen H hupper hlevi hst w hw
    · have hset : {x : Induction.LeftQuotient H | ∃ i : Fin 2,
          i.val < 2 ∧ x ∈ cosetOrbit H (plusSubgroup t R) (![w, 1] i)} = Set.univ := by
        ext x
        constructor
        · intro _; trivial
        · intro _
          obtain ⟨i, hi⟩ := hcover x
          exact ⟨i, i.isLt, hi⟩
      rw [hset]
      exact isOpen_univ

end Topology

end OrbitCriterion

end Coverage

universe uF

/-- The actual two mixed mirabolic orbits, with the published cycle first. -/
theorem mirabolicMixedOrbitCoverage {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MirabolicMixedOrbitCoverageStatement F T := by
  let := T.topology
  let := T.fieldT2
  constructor
  · intro k r
    let := T.generalLinearTopologicalGroup (k + r + 3)
    let : IsTopologicalGroup (mirabolic (k + r + 2) F.Carrier) := inferInstance
    simpa only [leftRepresentative] using
      Coverage.exists_ordered (s := k) (t := k + r + 1) (leftInducing k r F.Carrier)
        (fun h hh => leftInducing_projection_upperHead k r h hh)
        (fun A hA => levi_mem_leftInducing k r A hA) (by omega)
        (leftCycleElement k r F.Carrier) (by
          intro j
          simpa only [Fin.ext_iff] using leftCycleElement_projection_lastRow (R := F.Carrier) k r j)
  · intro k r
    let := T.generalLinearTopologicalGroup (k + r + 3)
    let : IsTopologicalGroup (mirabolic (k + r + 2) F.Carrier) := inferInstance
    simpa only [rightRepresentative] using
      Coverage.exists_ordered (s := r) (t := k + r + 1) (rightInducing k r F.Carrier)
        (fun h hh => rightInducing_projection_upperHead k r h hh)
        (fun A hA => levi_mem_rightInducing k r A hA) (by omega)
        (rightCycleElement k r F.Carrier) (by
          intro j
          simpa only [Fin.ext_iff] using rightCycleElement_projection_lastRow (R := F.Carrier) k r j)

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
