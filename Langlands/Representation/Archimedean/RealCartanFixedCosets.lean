import Langlands.Representation.Archimedean.RealLeviCompactChartSupport
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # The fixed compact cosets at equal elliptic rank -/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanFixedCosets

open Langlands.GeneralLinear GramFormula PrincipalSeriesExtension RealLeviChart
  RealLeviCompactChart RealCartanCompactSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "G" n:max => Langlands.GeneralLinear n ℝ

section Permutation

variable {n : ℕ}

/-- An orthogonal permutation matrix taking source coordinate `i` to coordinate `π i`. -/
def permutationFrame (π : Equiv.Perm (Fin n)) : K n :=
  ⟨(π⁻¹).permMatrix ℝ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]⟩

theorem mul_permutationFrame (A : M n) (π : Equiv.Perm (Fin n)) :
    A * (permutationFrame π : M n) = A.submatrix id π := by
  exact PEquiv.mul_toMatrix_toPEquiv A π.symm

theorem permutationFrame_mul (π : Equiv.Perm (Fin n)) (A : M n) :
    (permutationFrame π : M n) * A = A.submatrix π.symm id := by
  exact PEquiv.toMatrix_toPEquiv_mul π.symm A

@[simp]
theorem inv_permutationFrame (π : Equiv.Perm (Fin n)) :
    (permutationFrame π)⁻¹ = permutationFrame π.symm := by
  apply Subtype.ext
  change star ((π⁻¹).permMatrix ℝ) = π.permMatrix ℝ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, inv_inv]

theorem conjugate_permutationFrame_apply (π : Equiv.Perm (Fin n)) (A : M n) (i j : Fin n) :
    ((permutationFrame π : M n) * A * ((permutationFrame π)⁻¹ : K n).val) i j =
      A (π.symm i) (π.symm j) := by
  rw [inv_permutationFrame, mul_permutationFrame, permutationFrame_mul]
  rfl

end Permutation

section Cosets

variable {c t : ℕ} (sz : Fin t → ℕ)
local notation "N" => ∑ i, sz i

/-- An assignment of source Cartan slots to target blocks preserving both dimensions. -/
abbrev Assignment (a : Fin N → Fin c) :=
  {e : Fin c ≃ Fin t // ∀ j, Nat.card (BlockFiber a j) = Nat.card (BlockFiber (cls sz) (e j))}

/-- Choose an identification on the coordinates within each matched pair of blocks. -/
def assignmentPerm {a : Fin N → Fin c} (e : Assignment sz a) : Equiv.Perm (Fin N) :=
  (Equiv.sigmaFiberEquiv a).symm.trans ((Equiv.sigmaCongr e.1 (fun j =>
    Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using e.2 j))).trans
      (Equiv.sigmaFiberEquiv (cls sz)))

theorem cls_assignmentPerm {a : Fin N → Fin c} (e : Assignment sz a) (i : Fin N) :
    cls sz (assignmentPerm sz e i) = e.1 (a i) := by
  let F (j : Fin c) : BlockFiber a j ≃ BlockFiber (cls sz) (e.1 j) :=
    Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using e.2 j)
  change cls sz (F (a i) ⟨i, rfl⟩).val = e.1 (a i)
  exact (F (a i) ⟨i, rfl⟩).2

/-- The compact frames for one placement of the source Cartan slots. -/
def fixedCoset {a : Fin N → Fin c} (e : Assignment sz a) : Set (K N) :=
  range fun k : LeviFrame sz => blockFrame sz k * permutationFrame (assignmentPerm sz e)

theorem isCompact_fixedCoset {a : Fin N → Fin c} (e : Assignment sz a) :
    IsCompact (fixedCoset sz e) := by
  exact isCompact_range ((continuous_blockFrame sz).mul continuous_const)

theorem mem_fixedCoset_iff {a : Fin N → Fin c} (e : Assignment sz a) (y : K N) :
    y ∈ fixedCoset sz e ↔ ∀ p i, cls sz p ≠ e.1 (a i) → (y : M N) p i = 0 := by
  let π := assignmentPerm sz e
  let w := permutationFrame π
  have hmul (k : K N) (p i : Fin N) : ((k * w : K N) : M N) p i = (k : M N) p (π i) := by
    change ((k : M N) * (w : M N)) p i = _
    rw [mul_permutationFrame]
    rfl
  constructor
  · rintro ⟨k, rfl⟩ p i hij
    rw [hmul]
    exact blockZero_blockFrame sz k p (π i) (fun h => hij (h.trans (cls_assignmentPerm sz e i)))
  · intro hy
    let k := y * w⁻¹
    have hkw : k * w = y := by simp [k]
    have hzero : BlockZero sz (k : M N) := by
      intro p q hpq
      obtain ⟨i, rfl⟩ := π.surjective q
      rw [← hmul, hkw]
      exact hy p i (fun h => hpq (h.trans (cls_assignmentPerm sz e i).symm))
    obtain ⟨κ, hκ⟩ := (mem_range_blockFrame_iff sz k).mpr hzero
    exact ⟨κ, by change blockFrame sz κ * w = y; rw [hκ, hkw]⟩

/-- Each compact frame belongs to at most one size-preserving assignment. -/
theorem disjoint_fixedCoset_of_ne {a : Fin N → Fin c} (ha : Function.Surjective a)
    {e f : Assignment sz a} (hef : e ≠ f) : Disjoint (fixedCoset sz e) (fixedCoset sz f) := by
  refine Set.disjoint_left.mpr fun y hye hyf => hef (Subtype.ext (Equiv.ext fun j => ?_))
  obtain ⟨i, hi⟩ := ha j
  have hy : (y : M N)ᵀ * (y : M N) = 1 := by
    apply mul_eq_one_comm.mp
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.mem_unitaryGroup_iff.mp y.2
  have hei (e : Assignment sz a) (hy : y ∈ fixedCoset sz e) := (mem_fixedCoset_iff sz e y).mp hy
  by_contra hne
  have hz (p : Fin N) : (y : M N) p i = 0 := by
    by_cases hp : cls sz p = e.1 j
    · exact hei f hyf p i (by rw [hi, hp]; exact hne)
    · exact hei e hye p i (by rwa [hi])
  have he := congrArg (fun A : M N => A i i) hy
  simp [Matrix.mul_apply, hz] at he

end Cosets

section FixedPairs

variable {c t : ℕ} (sz : Fin t → ℕ)
local notation "N" => ∑ i, sz i

/-- The block radii in a target chart after a placement of the source slots. -/
def placedRadius {a : Fin N → Fin c} (e : Assignment sz a) (d : Fin c → ℝ) (i : Fin N) : ℝ :=
  d (e.1.symm (cls sz i))

/-- The positive diagonal matrix of the placed radii. -/
def placedDiagonal {a : Fin N → Fin c} (e : Assignment sz a) (d : Fin c → ℝ)
    (hd : ∀ j, 0 < d j) : G N :=
  Langlands.GeneralLinear.Iwasawa.diagonalUnits fun i => Units.mk0 (placedRadius sz e d i) (hd _).ne'

theorem placedDiagonal_val {a : Fin N → Fin c} (e : Assignment sz a) (d : Fin c → ℝ)
    (hd : ∀ j, 0 < d j) : (placedDiagonal sz e d hd : M N) = diagonal (placedRadius sz e d) :=
  rfl

/-- The rotation and sign blocks in the placed order. -/
def placedOrthogonal {a : Fin N → Fin c} (e : Assignment sz a) (u : K N) : K N :=
  permutationFrame (assignmentPerm sz e) * u * (permutationFrame (assignmentPerm sz e))⁻¹

theorem blockZero_placedOrthogonal {a : Fin N → Fin c} (e : Assignment sz a) (u : K N)
    (hu : ∀ p q, a p ≠ a q → (u : M N) p q = 0) :
    BlockZero sz (placedOrthogonal sz e u : M N) := by
  intro p q hpq
  let π := assignmentPerm sz e
  change ((permutationFrame π : M N) * (u : M N) * ((permutationFrame π)⁻¹ : K N).val) p q = 0
  rw [conjugate_permutationFrame_apply]
  apply hu
  intro h
  apply hpq
  simpa only [Equiv.apply_symm_apply] using
    (show cls sz (π (π.symm p)) = cls sz (π (π.symm q)) from
      (cls_assignmentPerm sz e (π.symm p)).trans ((congrArg e.1 h).trans
        (cls_assignmentPerm sz e (π.symm q)).symm))

theorem toUnits_permutationFrame_mul {a : Fin N → Fin c} (e : Assignment sz a)
    (d : Fin c → ℝ) (hd : ∀ j, 0 < d j) (u : K N) (g : G N)
    (hg : (g : M N) = diagonal (d ∘ a) * (u : M N)) :
    let w := permutationFrame (assignmentPerm sz e)
    Unitary.toUnits w * g = placedDiagonal sz e d hd * Unitary.toUnits (placedOrthogonal sz e u * w) := by
  intro w
  let π := assignmentPerm sz e
  have hπ (p : Fin N) : cls sz p = e.1 (a (π.symm p)) := by
    simpa only [Equiv.apply_symm_apply] using
      (show cls sz (π (π.symm p)) = _ from cls_assignmentPerm sz e (π.symm p))
  have hdcomm : (w : M N) * diagonal (d ∘ a) = diagonal (placedRadius sz e d) * (w : M N) := by
    ext p q
    rw [permutationFrame_mul, diagonal_mul]
    change diagonal (d ∘ a) (π.symm p) q = placedRadius sz e d p * (w : M N) p q
    simp only [placedRadius, hπ, Equiv.symm_apply_apply, Matrix.diagonal_apply,
      Function.comp_apply]
    change (if π.symm p = q then d (a (π.symm p)) else 0) = _
    rw [show (w : M N) p q = if π.symm p = q then 1 else 0 by
      simp [w, π, permutationFrame, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply, Option.mem_def, eq_comm]]
    split_ifs <;> simp
  have huh : placedOrthogonal sz e u * w = w * u := by
    change (w * u * w⁻¹) * w = w * u
    simp [mul_assoc]
  apply Units.ext
  change (w : M N) * (g : M N) =
    ((placedDiagonal sz e d hd : G N) : M N) * ((placedOrthogonal sz e u * w : K N) : M N)
  rw [huh, Submonoid.coe_mul, placedDiagonal_val, hg, ← mul_assoc, hdcomm, mul_assoc]

theorem blockFrame_commute_placedDiagonal {a : Fin N → Fin c} (e : Assignment sz a)
    (d : Fin c → ℝ) (hd : ∀ j, 0 < d j) (κ : LeviFrame sz) :
    Unitary.toUnits (blockFrame sz κ) * placedDiagonal sz e d hd =
      placedDiagonal sz e d hd * Unitary.toUnits (blockFrame sz κ) := by
  apply Units.ext
  change (blockFrame sz κ : M N) * (placedDiagonal sz e d hd : M N) =
    (placedDiagonal sz e d hd : M N) * (blockFrame sz κ : M N)
  rw [placedDiagonal_val]
  exact commute_diagonal_of_blockZero (blockZero_blockFrame sz κ)
    (fun p q hpq => by rw [placedRadius, placedRadius, hpq])

theorem signedOrthogonalPart_placedDiagonal {a : Fin N → Fin c} (e : Assignment sz a)
    (d : Fin c → ℝ) (hd : ∀ j, 0 < d j) : signedOrthogonalPart (placedDiagonal sz e d hd) = 1 := by
  apply Subtype.ext
  change signedOrthogonal (placedDiagonal sz e d hd : M N) = 1
  rw [placedDiagonal_val]
  have hpos (i : Fin N) : 0 < placedRadius sz e d i := hd _
  have he := signedOrthogonal_mul (b := diagonal (placedRadius sz e d)) (κ := (1 : M N))
    (blockTriangular_diagonal _) (fun i => by simpa using (hpos i).ne') (by simp)
  simpa [signReal, hpos] using he

/-- Over a placed frame, the left compact factor has a unique fixed value. -/
theorem compactArgument_eq_one_placed {a : Fin N → Fin c} (e : Assignment sz a)
    (d : Fin c → ℝ) (hd : ∀ j, 0 < d j) (u h : K N) (g : G N)
    (hg : (g : M N) = diagonal (d ∘ a) * (u : M N)) (κ : LeviFrame sz) :
    let w := permutationFrame (assignmentPerm sz e)
    let k := blockFrame sz κ
    compactArgument g (k * w) h = 1 ↔ h = k * (placedOrthogonal sz e u)⁻¹ * k⁻¹ := by
  intro w k
  have hw := toUnits_permutationFrame_mul sz e d hd u g hg
  let D := placedDiagonal sz e d hd
  let R := placedOrthogonal sz e u
  have hgw : Unitary.toUnits (k * w) * g = D * Unitary.toUnits (k * R * w) := by
    calc
      _ = Unitary.toUnits k * (Unitary.toUnits w * g) := by simp only [map_mul, mul_assoc]
      _ = (Unitary.toUnits k * D) * Unitary.toUnits (R * w) := by rw [hw, mul_assoc]
      _ = _ := by
        rw [blockFrame_commute_placedDiagonal sz e d hd κ]
        simp only [map_mul, mul_assoc, D, k]
  rw [compactArgument, hgw, orthogonalPart_mul_right, signedOrthogonalPart_placedDiagonal,
    one_mul]
  change (k * R * w)⁻¹ * h⁻¹ * (k * w) = 1 ↔ h = k * R⁻¹ * k⁻¹
  constructor
  · intro he
    calc
      h = (k * w) * ((k * R * w)⁻¹ * h⁻¹ * (k * w))⁻¹ * (k * R * w)⁻¹ := by group
      _ = _ := by rw [he, inv_one, mul_one]; group
  · rintro rfl
    group

/-- An identity test argument at equal rank has a unique assignment coset. -/
def RealCartanFixedCosetsStatement : Prop :=
  ∀ (c t : ℕ) (sz : Fin t → ℕ) (a : Fin (∑ i, sz i) → Fin c)
    (d : Fin c → ℝ) (g : G (∑ i, sz i)) (y h : K (∑ i, sz i)),
    let C := (g : M (∑ i, sz i))
    Function.Surjective a → Function.Surjective (cls sz) →
    (∀ j, Nat.card (BlockFiber (cls sz) j) ≤ 2) →
    Nat.card (PairBlock a) = Nat.card (PairBlock (cls sz)) →
    BlockZero sz (h : M (∑ i, sz i)) →
    (∀ ⦃i j k⦄, i ≠ j → a i = a j → a k = a i → k = i ∨ k = j) →
    (∀ ⦃i j⦄, a i ≠ a j → C i j = 0) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j = - C j i) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j ≠ 0) →
    C * Cᵀ = diagonal (d ∘ a) → Function.Injective d → C * Cᵀ = Cᵀ * C →
    compactArgument g y h = 1 → ∃! e : Assignment sz a, y ∈ fixedCoset sz e

theorem realCartanFixedCosets : RealCartanFixedCosetsStatement := by
  intro c t sz a d g y h C ha hb hbsize heq hh hsize hzero hskew hpair hgram hd hnormal hfix
  obtain ⟨π, _, hsupport, _, he⟩ := realCartanCompactSupport _ c t a (cls sz) d g y h
    ha hb (fun _ _ hab => cls_mono sz hab) hbsize hh
    (fun _ _ _ hij hij' hik => hsize hij hij' hik) (fun _ _ hij => hzero hij)
    (fun _ _ hij ha => hskew hij ha) (fun _ _ hij ha => hpair hij ha) hgram hd hnormal hfix
  obtain ⟨e, hπ, he⟩ := he heq
  let f : Assignment sz a := ⟨e, he⟩
  have hf : y ∈ fixedCoset sz f := (mem_fixedCoset_iff sz f y).mpr fun p i hi =>
    hsupport p i (fun h => hi (h.trans (hπ i)))
  refine ⟨f, hf, fun z hz => ?_⟩
  by_contra hzf
  exact Set.disjoint_left.mp (disjoint_fixedCoset_of_ne sz ha hzf) hz hf

end FixedPairs

end Langlands.Archimedean.RealCartanFixedCosets
