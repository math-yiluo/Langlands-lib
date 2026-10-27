import Langlands.Group.GL.UpperBruhatCells
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# Character-compatible monomial representatives

Shalika's compatibility condition for a matrix `s` and the standard character on the
actual upper-unipotent subgroup, and the locus of diagonal parameters `d` for which
`permutation (n + 1) F w * Iwasawa.diagonalUnits d` is compatible. The locus is closed,
being an intersection of equalizers of continuous complex-valued defect functions.
-/

noncomputable section

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis

universe uR uF

section Ring

variable {R : Type uR} [CommRing R] [TopologicalSpace R]

/-- The matrix `s` is character compatible when every upper-unipotent `u` carried by
conjugation with `s` to an upper-unipotent `v` has the same standard character value. -/
def IsCharacterCompatibleRepresentative (ψ : UnitaryAdditiveCharacter R) (n : ℕ)
    (s : Langlands.GeneralLinear (n + 1) R) : Prop :=
  ∀ u v : upperUnipotent (n + 1) R, s * u.val * s⁻¹ = v.val →
    standardCharacter ψ n u = standardCharacter ψ n v

/-- The literal meaning of compatibility. -/
theorem isCharacterCompatibleRepresentative_iff (ψ : UnitaryAdditiveCharacter R) (n : ℕ)
    (s : Langlands.GeneralLinear (n + 1) R) :
    IsCharacterCompatibleRepresentative ψ n s ↔
      ∀ u v : upperUnipotent (n + 1) R, s * u.val * s⁻¹ = v.val →
        standardCharacter ψ n u = standardCharacter ψ n v :=
  Iff.rfl

/-- Compatibility evaluated through the additive character on first-superdiagonal sums. -/
theorem isCharacterCompatibleRepresentative_iff_complex (ψ : UnitaryAdditiveCharacter R)
    (n : ℕ) (s : Langlands.GeneralLinear (n + 1) R) :
    IsCharacterCompatibleRepresentative ψ n s ↔
      ∀ u v : upperUnipotent (n + 1) R, s * u.val * s⁻¹ = v.val →
        ψ.complex (∑ i : Fin n, u.val i.castSucc i.succ) =
          ψ.complex (∑ i : Fin n, v.val i.castSucc i.succ) := by
  simp only [isCharacterCompatibleRepresentative_iff, ← standardCharacter_apply,
    Units.val_inj]

/-- The same condition, with the conjugation written as `s * u = v * s`. -/
theorem isCharacterCompatibleRepresentative_iff_mul_eq (ψ : UnitaryAdditiveCharacter R)
    (n : ℕ) (s : Langlands.GeneralLinear (n + 1) R) :
    IsCharacterCompatibleRepresentative ψ n s ↔
      ∀ u v : upperUnipotent (n + 1) R, s * u.val = v.val * s →
        standardCharacter ψ n u = standardCharacter ψ n v := by
  simp only [isCharacterCompatibleRepresentative_iff, mul_inv_eq_iff_eq_mul]

/-- Compatibility tested on each `u` whose `s`-conjugate is upper unipotent. -/
theorem isCharacterCompatibleRepresentative_iff_conj_mem (ψ : UnitaryAdditiveCharacter R)
    (n : ℕ) (s : Langlands.GeneralLinear (n + 1) R) :
    IsCharacterCompatibleRepresentative ψ n s ↔
      ∀ (u : upperUnipotent (n + 1) R) (h : s * u.val * s⁻¹ ∈ upperUnipotent (n + 1) R),
        standardCharacter ψ n u = standardCharacter ψ n ⟨s * u.val * s⁻¹, h⟩ := by
  constructor
  · intro hs u h
    exact hs u ⟨s * u.val * s⁻¹, h⟩ rfl
  · intro hs u v huv
    have h : s * u.val * s⁻¹ ∈ upperUnipotent (n + 1) R := huv ▸ v.property
    rw [hs u h]
    congr 1
    exact Subtype.ext huv

/-- The identity matrix is compatible. -/
theorem isCharacterCompatibleRepresentative_one (ψ : UnitaryAdditiveCharacter R) (n : ℕ) :
    IsCharacterCompatibleRepresentative ψ n 1 := by
  intro u v huv
  congr 1
  apply Subtype.ext
  simpa using huv

/-- In rank one the standard character is trivial, so every matrix is compatible. -/
theorem isCharacterCompatibleRepresentative_rankOne (ψ : UnitaryAdditiveCharacter R)
    (s : Langlands.GeneralLinear 1 R) :
    IsCharacterCompatibleRepresentative ψ 0 s := by
  intro u v _
  rw [standardCharacter_rankOne, MonoidHom.one_apply, MonoidHom.one_apply]

end Ring

section Field

variable {F : Type uF} [Field F]

/-- Entries after conjugation by `permutation m F w * Iwasawa.diagonalUnits d`. -/
theorem monomial_conjugate_entry {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → Fˣ)
    (g : Langlands.GeneralLinear m F) (i j : Fin m) :
    (permutation m F w * Iwasawa.diagonalUnits d * g *
        (permutation m F w * Iwasawa.diagonalUnits d)⁻¹) i j =
      (d (w⁻¹ i) : F) * g (w⁻¹ i) (w⁻¹ j) * (d (w⁻¹ j) : F)⁻¹ := by
  have h : permutation m F w * Iwasawa.diagonalUnits d * g *
      (permutation m F w * Iwasawa.diagonalUnits d)⁻¹ =
        permutation m F w * (Iwasawa.diagonalUnits d * g * Iwasawa.diagonalUnits d⁻¹) *
          (permutation m F w)⁻¹ := by
    rw [mul_inv_rev, map_inv]
    group
  rw [h, permutation_conjugate_entry, Iwasawa.diagonalUnits_mul_mul_apply, Pi.inv_apply,
    Units.val_inv_eq_inv_val]

/-- Conjugation by a monomial matrix lands in the upper-unipotent subgroup exactly when
conjugation by its permutation factor does. -/
theorem monomial_conj_mem_upperUnipotent_iff {m : ℕ} (w : Equiv.Perm (Fin m))
    (d : Fin m → Fˣ) (g : Langlands.GeneralLinear m F) :
    permutation m F w * Iwasawa.diagonalUnits d * g *
        (permutation m F w * Iwasawa.diagonalUnits d)⁻¹ ∈ upperUnipotent m F ↔
      permutation m F w * g * (permutation m F w)⁻¹ ∈ upperUnipotent m F := by
  rw [mem_upperUnipotent_iff, mem_upperUnipotent_iff]
  simp only [monomial_conjugate_entry, permutation_conjugate_entry]
  apply and_congr
  · apply forall₂_congr
    intro i j
    apply imp_congr_right
    intro _
    simp [Units.ne_zero]
  · apply forall_congr'
    intro i
    rw [mul_right_comm, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

/-- If `permutation m F w` conjugates `g` into the upper-unipotent subgroup, then so does
every monomial matrix `permutation m F w * Iwasawa.diagonalUnits d`. -/
theorem monomial_conj_mem_upperUnipotent {m : ℕ} (w : Equiv.Perm (Fin m))
    (d : Fin m → Fˣ) {g : Langlands.GeneralLinear m F}
    (h : permutation m F w * g * (permutation m F w)⁻¹ ∈ upperUnipotent m F) :
    permutation m F w * Iwasawa.diagonalUnits d * g *
      (permutation m F w * Iwasawa.diagonalUnits d)⁻¹ ∈ upperUnipotent m F :=
  (monomial_conj_mem_upperUnipotent_iff w d g).mpr h

/-- Conversely, membership after monomial conjugation gives membership after conjugation
by the permutation factor alone. -/
theorem permutation_conj_mem_upperUnipotent_of_monomial {m : ℕ} (w : Equiv.Perm (Fin m))
    (d : Fin m → Fˣ) {g : Langlands.GeneralLinear m F}
    (h : permutation m F w * Iwasawa.diagonalUnits d * g *
      (permutation m F w * Iwasawa.diagonalUnits d)⁻¹ ∈ upperUnipotent m F) :
    permutation m F w * g * (permutation m F w)⁻¹ ∈ upperUnipotent m F :=
  (monomial_conj_mem_upperUnipotent_iff w d g).mp h

/-- For upper-unipotent `u`, the common domain is Shalika's `U_w⁺`, constructed in
`Langlands.Group.GL.UpperBruhatCells` as `permutationUnipotentPlus`. -/
theorem monomial_conj_mem_upperUnipotent_iff_mem_permutationUnipotentPlus {m : ℕ}
    (w : Equiv.Perm (Fin m)) (d : Fin m → Fˣ) (u : upperUnipotent m F) :
    permutation m F w * Iwasawa.diagonalUnits d * u.val *
        (permutation m F w * Iwasawa.diagonalUnits d)⁻¹ ∈ upperUnipotent m F ↔
      u.val ∈ permutationUnipotentPlus m F w := by
  rw [monomial_conj_mem_upperUnipotent_iff, mem_permutationUnipotentPlus_iff]
  exact (and_iff_right u.property).symm

variable [TopologicalSpace F]

/-- The diagonal parameters `d` for which `permutation (n + 1) F w * Iwasawa.diagonalUnits d`
is a character-compatible representative. -/
def compatibleTorus (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) : Set (Fin (n + 1) → Fˣ) :=
  {d | IsCharacterCompatibleRepresentative ψ n
    (permutation (n + 1) F w * Iwasawa.diagonalUnits d)}

theorem mem_compatibleTorus_iff (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ) :
    d ∈ compatibleTorus ψ n w ↔
      IsCharacterCompatibleRepresentative ψ n
        (permutation (n + 1) F w * Iwasawa.diagonalUnits d) :=
  Iff.rfl

/-- Membership tested on every `u` with `permutation (n + 1) F w * u * (permutation …)⁻¹`
upper unipotent. -/
theorem mem_compatibleTorus_iff_conj_mem (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ) :
    d ∈ compatibleTorus ψ n w ↔
      ∀ (u : upperUnipotent (n + 1) F)
        (hu : permutation (n + 1) F w * u.val * (permutation (n + 1) F w)⁻¹ ∈
          upperUnipotent (n + 1) F),
        standardCharacter ψ n u =
          standardCharacter ψ n
            ⟨permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val *
              (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹,
              monomial_conj_mem_upperUnipotent w d hu⟩ := by
  rw [mem_compatibleTorus_iff, isCharacterCompatibleRepresentative_iff_conj_mem]
  constructor
  · intro h u hu
    exact h u _
  · intro h u hs
    exact h u (permutation_conj_mem_upperUnipotent_of_monomial w d hs)

/-- Shalika's form: `χ(w h u h⁻¹ w⁻¹) = χ(u)` for every `u` in `U_w⁺`. -/
theorem mem_compatibleTorus_iff_permutationUnipotentPlus (ψ : UnitaryAdditiveCharacter F)
    (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ) :
    d ∈ compatibleTorus ψ n w ↔
      ∀ (u : upperUnipotent (n + 1) F)
        (hu : u.val ∈ permutationUnipotentPlus (n + 1) F w),
        standardCharacter ψ n
            ⟨permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val *
              (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹,
              (monomial_conj_mem_upperUnipotent_iff_mem_permutationUnipotentPlus
                w d u).mpr hu⟩ =
          standardCharacter ψ n u := by
  rw [mem_compatibleTorus_iff_conj_mem]
  constructor
  · intro h u hu
    exact (h u ((mem_permutationUnipotentPlus_iff _ _ _ _).mp hu).2).symm
  · intro h u hu
    exact (h u ((mem_permutationUnipotentPlus_iff _ _ _ _).mpr ⟨u.property, hu⟩)).symm

/-- In rank one every diagonal parameter is compatible. -/
theorem compatibleTorus_rankOne (ψ : UnitaryAdditiveCharacter F) (w : Equiv.Perm (Fin 1)) :
    compatibleTorus ψ 0 w = Set.univ :=
  Set.eq_univ_of_forall fun _ => isCharacterCompatibleRepresentative_rankOne ψ _

/-- The defect of `d` on `u`: the additive character of the first-superdiagonal sum of
the monomial conjugate of `u`, divided by the standard character value of `u`. It is
defined for every `u`; it is a ratio of two character values when `u ∈ U_w⁺`. -/
def compatibilityDefect (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) (u : upperUnipotent (n + 1) F)
    (d : Fin (n + 1) → Fˣ) : ℂ :=
  ψ.complex (∑ i : Fin n,
      (permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val *
        (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹) i.castSucc i.succ) *
    (standardCharacter ψ n u : ℂ)⁻¹

/-- On `U_w⁺` the defect is the ratio of the two actual character values. -/
theorem compatibilityDefect_eq_div (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) {u : upperUnipotent (n + 1) F}
    (hu : permutation (n + 1) F w * u.val * (permutation (n + 1) F w)⁻¹ ∈
      upperUnipotent (n + 1) F) (d : Fin (n + 1) → Fˣ) :
    compatibilityDefect ψ n w u d =
      (standardCharacter ψ n
          ⟨permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val *
            (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹,
            monomial_conj_mem_upperUnipotent w d hu⟩ : ℂ) /
        (standardCharacter ψ n u : ℂ) := by
  rw [div_eq_mul_inv, standardCharacter_apply]
  rfl

theorem compatibilityDefect_eq_one_iff (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) {u : upperUnipotent (n + 1) F}
    (hu : permutation (n + 1) F w * u.val * (permutation (n + 1) F w)⁻¹ ∈
      upperUnipotent (n + 1) F) (d : Fin (n + 1) → Fˣ) :
    compatibilityDefect ψ n w u d = 1 ↔
      standardCharacter ψ n
          ⟨permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val *
            (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹,
            monomial_conj_mem_upperUnipotent w d hu⟩ =
        standardCharacter ψ n u := by
  rw [compatibilityDefect_eq_div ψ n w hu, div_eq_one_iff_eq (Units.ne_zero _),
    Units.val_inj]

/-- A parameter is compatible exactly when all its defects on `U_w⁺` equal one. -/
theorem mem_compatibleTorus_iff_defect (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ) :
    d ∈ compatibleTorus ψ n w ↔
      ∀ u : upperUnipotent (n + 1) F,
        permutation (n + 1) F w * u.val * (permutation (n + 1) F w)⁻¹ ∈
          upperUnipotent (n + 1) F →
        compatibilityDefect ψ n w u d = 1 := by
  rw [mem_compatibleTorus_iff_conj_mem]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  rw [compatibilityDefect_eq_one_iff ψ n w hu, eq_comm]

/-- The compatible locus as an intersection of equalizers of defect functions. -/
theorem compatibleTorus_eq_iInter (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) :
    compatibleTorus ψ n w =
      ⋂ (u : upperUnipotent (n + 1) F)
        (_ : permutation (n + 1) F w * u.val * (permutation (n + 1) F w)⁻¹ ∈
          upperUnipotent (n + 1) F),
        {d | compatibilityDefect ψ n w u d = 1} := by
  ext d
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  exact mem_compatibleTorus_iff_defect ψ n w d

section Topology

variable [IsTopologicalRing F]

/-- Each defect is continuous in the diagonal parameter, for the product topology of the
unit groups. -/
@[fun_prop]
theorem continuous_compatibilityDefect (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) (u : upperUnipotent (n + 1) F) :
    Continuous (compatibilityDefect ψ n w u) := by
  have hs : Continuous fun d : Fin (n + 1) → Fˣ =>
      permutation (n + 1) F w * Iwasawa.diagonalUnits d :=
    continuous_const.mul (continuous_diagonalUnits (n + 1))
  have hc : Continuous fun d : Fin (n + 1) → Fˣ =>
      permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val *
        (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹ :=
    (hs.mul continuous_const).mul hs.inv
  exact (ψ.continuous_complex.comp (continuous_finsetSum _ fun i _ =>
    (GeneralLinear.entry i.castSucc i.succ).continuous.comp hc)).mul continuous_const

/-- The compatible locus is closed. -/
theorem isClosed_compatibleTorus (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) :
    IsClosed (compatibleTorus ψ n w) := by
  rw [compatibleTorus_eq_iInter]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq (continuous_compatibilityDefect ψ n w u) continuous_const

end Topology

end Field

/-- The closedness law applies to the canonical topology of every p-adic field. -/
example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) :
    letI := F.canonicalNormedField
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier, IsClosed (compatibleTorus ψ n w) := by
  let := F.canonicalNormedField
  intro ψ
  exact isClosed_compatibleTorus ψ n w

end Langlands.Whittaker
