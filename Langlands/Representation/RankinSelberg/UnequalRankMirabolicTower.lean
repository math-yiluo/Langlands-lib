import Langlands.Representation.RankinSelberg.UnequalRankBilinearForms
import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.Representation.Parabolic.LeviBridges
import Langlands.Group.GL.BlockIwahoriDefinitions

/-!
# Towers of block embeddings for unequal-rank rigidity

For a representation `η` of `GL_(N+1)` and `j ≤ N`, a *tower datum at level `j`*
is a representation `ρ` of the mirabolic group `P_(j+1) ⊂ GL_(j+1)` together with
a surjective linear map `q` from the carrier of `η` such that `q` intertwines
`η ∘ diag(-, I_(N-j))` with `ρ`, and such that every upper unipotent matrix whose
leading `(j+1)`-square block is the identity acts on `q`-images through the
standard character. The restriction of `η` to `P_(N+1)` is a tower datum at level
`N`, and quotienting a tower datum at level `j+1` by the radical relations of a
character `u(c) ↦ ψ(c_last)` gives a tower datum at level `j`.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnequalRankTower

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uW uA uB

section Matrices

variable {F : Type uF} [Field F]

/-- The block embedding `g ↦ diag(g, I_(N-j))` of `GL_(j+1)` into `GL_(N+1)`. -/
def towerEmbedding {j N : ℕ} (h : j ≤ N) :
    Langlands.GeneralLinear (j + 1) F →* Langlands.GeneralLinear (N + 1) F :=
  (GeneralLinear.reindex (finCongr (show j + (N - j) + 1 = N + 1 by omega))).toMonoidHom.comp
    (appendIdentity j (N - j))

/-- Entrywise, `towerEmbedding h g` is `diag(g, I_(N-j))`. -/
theorem towerEmbedding_entry {j N : ℕ} (h : j ≤ N) (g : Langlands.GeneralLinear (j + 1) F)
    (a b : Fin (N + 1)) :
    towerEmbedding h g a b =
      if ha : a.val < j + 1 then
        if hb : b.val < j + 1 then g ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0
      else if a = b then 1 else 0 := by
  change appendIdentity j (N - j) g
      ((finCongr (show j + (N - j) + 1 = N + 1 by omega)).symm a)
      ((finCongr (show j + (N - j) + 1 = N + 1 by omega)).symm b) = _
  rw [appendIdentity_entry]
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast, Fin.cast_inj]

/-- A uniform entry formula for the radical element `u(v)`. -/
theorem radicalElement_entry {n : ℕ} (v : Fin n → F) (a b : Fin (n + 1)) :
    (Mirabolic.radicalElement v).val.val.val a b =
      (if a = b then 1 else 0) + (if h : a.val < n ∧ b.val = n then v ⟨a.val, h.1⟩ else 0) := by
  refine Fin.lastCases ?_ (fun b => ?_) b
  · refine Fin.lastCases ?_ (fun a => ?_) a
    · simp
    · rw [Mirabolic.radicalElement_last]
      have hne : a.castSucc ≠ Fin.last n := Fin.castSucc_ne_last a
      simp [hne]
  · rw [Mirabolic.radicalElement_first]
    have hb : (b : ℕ) ≠ n := b.isLt.ne
    simp [hb]

/-- A uniform entry formula for the Levi element `diag(g, 1)`. -/
theorem levi_entry {n : ℕ} (g : Langlands.GeneralLinear n F) (a b : Fin (n + 1)) :
    (Mirabolic.levi g).val.val a b =
      if ha : a.val < n then
        if hb : b.val < n then g ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0
      else if a = b then 1 else 0 := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · rw [Mirabolic.levi_bottom]
    simp [eq_comm]
  · refine Fin.lastCases ?_ (fun b => ?_) b
    · rw [Mirabolic.levi_last]
      simp
    · rw [Mirabolic.levi_first]
      simp

/-- At the top level the tower embedding is the identity. -/
theorem towerEmbedding_self {N : ℕ} (g : Langlands.GeneralLinear (N + 1) F) :
    towerEmbedding (le_refl N) g = g := by
  apply Units.ext
  ext a b
  have h := towerEmbedding_entry (le_refl N) g a b
  rw [dite_eq_left a.isLt, dite_eq_left b.isLt] at h
  exact h

/-- Embedding `diag(g, 1)` one level up is the same as embedding `g`. -/
theorem towerEmbedding_levi {j N : ℕ} (h' : j + 1 ≤ N) (h : j ≤ N)
    (g : Langlands.GeneralLinear (j + 1) F) :
    towerEmbedding h' (Mirabolic.levi g).val = towerEmbedding h g := by
  apply Units.ext
  ext a b
  have e1 := towerEmbedding_entry h' (Mirabolic.levi g).val a b
  have e2 := towerEmbedding_entry h g a b
  change towerEmbedding h' (Mirabolic.levi g).val a b = towerEmbedding h g a b
  rw [e1, e2]
  by_cases ha : a.val < j + 1
  · by_cases hb : b.val < j + 1
    · rw [dite_eq_left (by omega : a.val < j + 1 + 1), dite_eq_left (by omega : b.val < j + 1 + 1),
        dite_eq_left ha, dite_eq_left hb]
      rw [levi_entry, dite_eq_left ha, dite_eq_left hb]
    · rw [dite_eq_left ha, dite_eq_right hb]
      by_cases hb' : b.val < j + 1 + 1
      · rw [dite_eq_left (by omega : a.val < j + 1 + 1), dite_eq_left hb']
        rw [levi_entry, dite_eq_left ha, dite_eq_right hb]
      · rw [dite_eq_left (by omega : a.val < j + 1 + 1), dite_eq_right hb']
  · rw [dite_eq_right ha]
    by_cases ha' : a.val < j + 1 + 1
    · rw [dite_eq_left ha']
      by_cases hb' : b.val < j + 1 + 1
      · rw [dite_eq_left hb']
        rw [levi_entry, dite_eq_right ha]
        simp only [Fin.ext_iff]
      · rw [dite_eq_right hb']
        have hab : a ≠ b := by
          intro hab
          subst hab
          exact hb' ha'
        rw [ite_eq_right hab]
    · rw [dite_eq_right ha']

/-- Entries of the embedded radical element `diag(u(c), I_(N-j))`. -/
theorem towerEmbedding_radical_entry {j N : ℕ} (h : j ≤ N) (c : Fin j → F) (a b : Fin (N + 1)) :
    towerEmbedding h (Mirabolic.radicalElement c : mirabolic j F).val a b =
      (if a = b then 1 else 0) +
        (if hx : a.val < j ∧ b.val = j then c ⟨a.val, hx.1⟩ else 0) := by
  rw [towerEmbedding_entry]
  by_cases ha : a.val < j + 1
  · by_cases hb : b.val < j + 1
    · rw [dite_eq_left ha, dite_eq_left hb]
      rw [radicalElement_entry]
      simp only [Fin.ext_iff]
    · rw [dite_eq_left ha, dite_eq_right hb]
      have hab : a ≠ b := by
        intro hab
        subst hab
        exact hb ha
      rw [ite_eq_right hab, dite_eq_right (by omega)]
      simp
  · rw [dite_eq_right ha, dite_eq_right (by omega)]
    simp

/-- Left multiplication by an embedded radical element adds multiples of row `j`. -/
theorem towerEmbedding_radical_mul_entry {j N : ℕ} (h : j ≤ N) (c : Fin j → F)
    (g : Langlands.GeneralLinear (N + 1) F) (a b : Fin (N + 1)) :
    (towerEmbedding h (Mirabolic.radicalElement c : mirabolic j F).val * g) a b =
      g a b + (if ha : a.val < j then c ⟨a.val, ha⟩ * g ⟨j, by omega⟩ b else 0) := by
  change ((towerEmbedding h (Mirabolic.radicalElement c : mirabolic j F).val).val * g.val) a b = _
  rw [Matrix.mul_apply]
  have hentry : ∀ k : Fin (N + 1),
      (towerEmbedding h (Mirabolic.radicalElement c : mirabolic j F).val).val a k * g.val k b =
        (if a = k then g.val k b else 0) +
          (if hx : a.val < j ∧ k.val = j then c ⟨a.val, hx.1⟩ * g.val k b else 0) := by
    intro k
    have e := towerEmbedding_radical_entry h c a k
    change (towerEmbedding h (Mirabolic.radicalElement c : mirabolic j F).val).val a k = _ at e
    rw [e, add_mul]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp
  simp only [hentry, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  by_cases ha : a.val < j
  · rw [dite_eq_left ha]
    rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (N + 1))]
    · rw [dite_eq_left ⟨ha, rfl⟩]
    · intro k _ hk
      rw [dite_eq_right]
      rintro ⟨_, hkj⟩
      exact hk (Fin.ext hkj)
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · rw [dite_eq_right ha]
    apply Finset.sum_eq_zero
    intro k _
    rw [dite_eq_right]
    rintro ⟨ha', _⟩
    exact ha ha'

/-- The embedded radical element is upper unipotent. -/
theorem towerEmbedding_radical_mem {j N : ℕ} (h : j ≤ N) (c : Fin j → F) :
    towerEmbedding h (Mirabolic.radicalElement c : mirabolic j F).val ∈
      upperUnipotent (N + 1) F := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · have e := towerEmbedding_radical_entry h c a b
    have hlt : (b : ℕ) < a := hba
    have hab : a ≠ b := fun hab => by subst hab; exact lt_irrefl _ hlt
    rw [ite_eq_right hab, dite_eq_right (by omega), add_zero] at e
    exact e
  · have e := towerEmbedding_radical_entry h c a a
    rw [ite_eq_left rfl, dite_eq_right (by omega), add_zero] at e
    exact e

/-- The radical element `diag(u(c), I_(N-j))` as an upper unipotent matrix. -/
def towerRadical {j N : ℕ} (h : j ≤ N) (c : Fin j → F) : upperUnipotent (N + 1) F :=
  ⟨_, towerEmbedding_radical_mem h c⟩

@[simp] theorem towerRadical_val {j N : ℕ} (h : j ≤ N) (c : Fin j → F) :
    (towerRadical h c).val = towerEmbedding h (Mirabolic.radicalElement c : mirabolic j F).val :=
  rfl

theorem towerRadical_add {j N : ℕ} (h : j ≤ N) (c d : Fin j → F) :
    towerRadical h (c + d) = towerRadical h c * towerRadical h d := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, towerRadical_val, towerRadical_val, towerRadical_val,
    Mirabolic.radicalElement_add, Subgroup.coe_mul, Subgroup.coe_mul, map_mul]

theorem towerRadical_zero {j N : ℕ} (h : j ≤ N) : towerRadical h (0 : Fin j → F) = 1 := by
  apply Subtype.ext
  rw [towerRadical_val, Mirabolic.radicalElement_zero, Subgroup.coe_one, Subgroup.coe_one,
    map_one, Subgroup.coe_one]

/-- An upper unipotent matrix whose leading `(j+1)`-square block is the identity. -/
def IsLeading {N : ℕ} (j : ℕ) (u : upperUnipotent (N + 1) F) : Prop :=
  ∀ a b : Fin (N + 1), a.val ≤ j → b.val ≤ j → u.val a b = if a = b then 1 else 0

/-- Every upper unipotent matrix is leading at level `0`. -/
theorem isLeading_zero {N : ℕ} (u : upperUnipotent (N + 1) F) : IsLeading 0 u := by
  intro a b ha hb
  have hab : a = b := Fin.ext (by omega)
  subst hab
  rw [ite_eq_left rfl]
  exact UpperUnipotent.entry_diag u a

/-- The entries of column `j+1` above the diagonal. -/
def towerColumn {j N : ℕ} (h : j + 1 ≤ N) (u : upperUnipotent (N + 1) F) : Fin (j + 1) → F :=
  fun a => u.val ⟨a.val, by omega⟩ ⟨j + 1, by omega⟩

/-- A leading matrix at level `j` is an embedded radical element times a leading
matrix at level `j+1`. -/
theorem exists_towerRadical_mul {j N : ℕ} (h : j + 1 ≤ N) (u : upperUnipotent (N + 1) F)
    (hu : IsLeading j u) :
    ∃ u' : upperUnipotent (N + 1) F,
      u = towerRadical h (towerColumn h u) * u' ∧ IsLeading (j + 1) u' := by
  refine ⟨towerRadical h (-towerColumn h u) * u, ?_, ?_⟩
  · rw [← mul_assoc, ← towerRadical_add, add_neg_cancel, towerRadical_zero, one_mul]
  · intro a b ha hb
    have e := towerEmbedding_radical_mul_entry h (-towerColumn h u) u.val a b
    have e' : (towerRadical h (-towerColumn h u) * u).val a b = _ := e
    rw [e']
    have hjj : u.val ⟨j + 1, by omega⟩ ⟨j + 1, by omega⟩ = 1 := UpperUnipotent.entry_diag u _
    by_cases ha' : a.val < j + 1
    · rw [dite_eq_left ha']
      by_cases hb' : b.val < j + 1
      · have hlow : u.val ⟨j + 1, by omega⟩ b = 0 :=
          UpperUnipotent.entry_eq_zero u (show b < ⟨j + 1, by omega⟩ from hb')
        rw [hu a b (by omega) (by omega), hlow, mul_zero, add_zero]
      · have hbj : b = ⟨j + 1, Nat.lt_succ_of_le h⟩ := Fin.ext (show b.val = j + 1 by omega)
        have hab : a ≠ b := fun hab => by rw [hab] at ha'; exact hb' ha'
        subst hbj
        rw [hjj, ite_eq_right hab, mul_one, Pi.neg_apply]
        simp [towerColumn]
    · have haj : a = ⟨j + 1, Nat.lt_succ_of_le h⟩ := Fin.ext (show a.val = j + 1 by omega)
      rw [dite_eq_right ha', add_zero]
      subst haj
      by_cases hb' : b.val < j + 1
      · have hab : (⟨j + 1, by omega⟩ : Fin (N + 1)) ≠ b := fun hab => by
          rw [← hab] at hb'; exact lt_irrefl _ hb'
        rw [ite_eq_right hab]
        exact UpperUnipotent.entry_eq_zero u (show b < ⟨j + 1, by omega⟩ from hb')
      · have hbj : b = ⟨j + 1, Nat.lt_succ_of_le h⟩ := Fin.ext (show b.val = j + 1 by omega)
        subst hbj
        rw [ite_eq_left rfl]
        exact hjj

end Matrices

section Character

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The standard character of an embedded radical element reads the entry `(j, j+1)`. -/
theorem standardCharacter_towerRadical (ψ : UnitaryAdditiveCharacter F) {j N : ℕ}
    (h : j + 1 ≤ N) (c : Fin (j + 1) → F) :
    (standardCharacter ψ N (towerRadical h c) : ℂ) = ψ.complex (c (Fin.last j)) := by
  rw [standardCharacter_apply]
  congr 1
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin N)]
  · change towerEmbedding h _ _ _ = _
    rw [towerEmbedding_radical_entry]
    have hne : (⟨j, by omega⟩ : Fin N).castSucc ≠ (⟨j, by omega⟩ : Fin N).succ := by
      simp [Fin.ext_iff]
    rw [ite_eq_right hne, zero_add, dite_eq_left ⟨by simp, by simp⟩]
    rfl
  · intro i _ hi
    change towerEmbedding h _ _ _ = 0
    rw [towerEmbedding_radical_entry]
    have hne : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
    have hij : (i : ℕ) ≠ j := fun h' => hi (Fin.ext h')
    rw [ite_eq_right hne, zero_add, dite_eq_right]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- The standard character factors through `exists_towerRadical_mul`. -/
theorem standardCharacter_eq_mul (ψ : UnitaryAdditiveCharacter F) {j N : ℕ}
    (h : j + 1 ≤ N) (u u' : upperUnipotent (N + 1) F)
    (hu : u = towerRadical h (towerColumn h u) * u') :
    (standardCharacter ψ N u : ℂ) =
      ψ.complex (towerColumn h u (Fin.last j)) * (standardCharacter ψ N u' : ℂ) := by
  conv_lhs => rw [hu]
  rw [map_mul, Units.val_mul, standardCharacter_towerRadical]

end Character

section Tower

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {B : Type uB} [AddCommGroup B] [Module ℂ B]

/-- A tower datum at level `j` for a representation `η` of `GL_(N+1)`: a
representation `ρ` of `P_(j+1)` and a surjection `q` from the carrier of `η`
intertwining `η ∘ diag(-, I_(N-j))` with `ρ`, on whose images every upper
unipotent matrix with identity leading `(j+1)`-block acts by the standard
character. -/
structure IsTower (ψ : UnitaryAdditiveCharacter F) {N : ℕ}
    (η : Representation ℂ (Langlands.GeneralLinear (N + 1) F) W) {j : ℕ} (h : j ≤ N)
    (ρ : Representation ℂ (mirabolic j F) A) (q : W →ₗ[ℂ] A) : Prop where
  surjective : Function.Surjective q
  levi : ∀ (p : mirabolic j F) (w : W), q (η (towerEmbedding h p.val) w) = ρ p (q w)
  unipotent : ∀ u : upperUnipotent (N + 1) F, IsLeading j u → ∀ w : W,
    q (η u.val w) = (standardCharacter ψ N u : ℂ) • q w

omit [TopologicalSpace F] in
/-- A matrix that is leading at the top level is the identity. -/
theorem eq_one_of_isLeading {N : ℕ} (u : upperUnipotent (N + 1) F) (hu : IsLeading N u) :
    u = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  rw [hu a b (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp b.isLt)]
  change _ = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) F) a b
  rw [Matrix.one_apply]

/-- The restriction of `η` to `P_(N+1)` with the identity map is a tower datum
at the top level `N`. -/
theorem isTower_top (ψ : UnitaryAdditiveCharacter F) {N : ℕ}
    (η : Representation ℂ (Langlands.GeneralLinear (N + 1) F) W) :
    IsTower ψ η (le_refl N) (η.comp (mirabolic N F).subtype) LinearMap.id where
  surjective := Function.surjective_id
  levi p w := by
    rw [towerEmbedding_self]
    rfl
  unipotent u hu w := by
    rw [eq_one_of_isLeading u hu]
    simp

/-- Descent of a tower datum through a quotient on which the successor action
descends and the radical acts through `u(c) ↦ ψ(c_last)`. -/
theorem IsTower.descend {ψ : UnitaryAdditiveCharacter F} {N : ℕ}
    {η : Representation ℂ (Langlands.GeneralLinear (N + 1) F) W} {j : ℕ} (h' : j + 1 ≤ N)
    {ρ : Representation ℂ (mirabolic (j + 1) F) A} {q : W →ₗ[ℂ] A}
    (hT : IsTower ψ η h' ρ q) (ρ' : Representation ℂ (mirabolic j F) B) (π : A →ₗ[ℂ] B)
    (hπ : Function.Surjective π)
    (hsucc : ∀ (p : mirabolic j F) (x : A), π (ρ (Mirabolic.successor p) x) = ρ' p (π x))
    (hrad : ∀ (c : Fin (j + 1) → F) (x : A),
      π (ρ (Mirabolic.radicalElement c : mirabolic (j + 1) F) x) =
        ψ.complex (c (Fin.last j)) • π x) :
    IsTower ψ η (Nat.le_of_succ_le h') ρ' (π ∘ₗ q) where
  surjective := hπ.comp hT.surjective
  levi p w := by
    rw [LinearMap.comp_apply, ← towerEmbedding_levi h' (Nat.le_of_succ_le h') p.val]
    change π (q (η (towerEmbedding h' (Mirabolic.successor p).val) w)) = _
    rw [hT.levi, hsucc]
    rfl
  unipotent u hu w := by
    obtain ⟨u', hu', hl⟩ := exists_towerRadical_mul h' u hu
    have hη : η u.val w = η (towerRadical h' (towerColumn h' u)).val (η u'.val w) := by
      conv_lhs => rw [hu']
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    rw [LinearMap.comp_apply, hη, towerRadical_val, hT.levi, hT.unipotent u' hl, map_smul,
      map_smul, hrad, standardCharacter_eq_mul ψ h' u u' hu', mul_smul]
    exact smul_comm _ _ _

/-- At level `0`, every functional on the tower quotient gives a standard
Whittaker functional on `η`. -/
theorem IsTower.functional_apply {ψ : UnitaryAdditiveCharacter F} {N : ℕ}
    {η : Representation ℂ (Langlands.GeneralLinear (N + 1) F) W} {h : 0 ≤ N}
    {ρ : Representation ℂ (mirabolic 0 F) A} {q : W →ₗ[ℂ] A}
    (hT : IsTower ψ η h ρ q) (ℓ : A →ₗ[ℂ] ℂ) (u : upperUnipotent (N + 1) F) (w : W) :
    ℓ (q (η u.val w)) = (standardCharacter ψ N u : ℂ) * ℓ (q w) := by
  rw [hT.unipotent u (isLeading_zero u), map_smul, smul_eq_mul]

/-- A nonzero functional on a level-`0` tower quotient yields a nonzero standard
Whittaker functional on `η`. -/
theorem IsTower.hasFunctional {ψ : UnitaryAdditiveCharacter F} {N : ℕ}
    {η : Representation ℂ (Langlands.GeneralLinear (N + 1) F) W} {h : 0 ≤ N}
    {ρ : Representation ℂ (mirabolic 0 F) A} {q : W →ₗ[ℂ] A}
    (hT : IsTower ψ η h ρ q) (ℓ : A →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) :
    HasFunctional (N := upperUnipotent (N + 1) F) (θ := standardCharacter ψ N) η := by
  refine ⟨⟨ℓ ∘ₗ q, fun u w => hT.functional_apply ℓ u w⟩, ?_⟩
  intro h0
  apply hℓ
  ext x
  obtain ⟨w, rfl⟩ := hT.surjective x
  exact LinearMap.congr_fun h0 w

end Tower

end Langlands.RankinSelberg.UnequalRankTower
