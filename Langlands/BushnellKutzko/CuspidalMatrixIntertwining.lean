import Langlands.BushnellKutzko.IntertwiningTransport
import Langlands.Group.GL.CartanProof
import Langlands.Group.GL.Transvection
import Langlands.Group.GL.TwoBlockShape
import Langlands.Representation.FiniteGeneralLinear.Cuspidal

/-! # Intertwining of an inflated cuspidal representation of an integral matrix group -/

noncomputable section

open IsLocalRing
open scoped Pointwise

namespace Langlands.BushnellKutzko

namespace IntegralMatrices

open Matrix.GeneralLinearGroup

variable {O K : Type*} [CommRing O] [Field K] [Algebra O K] {n : ℕ}

/-- The integral matrix group inside the general linear group of the field. -/
abbrev subgroup (O K : Type*) [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    Subgroup (GeneralLinear n K) := (map (algebraMap O K)).range

theorem map_injective (h : Function.Injective (algebraMap O K)) :
    Function.Injective (map (n := Fin n) (algebraMap O K)) := by
  intro g g' he
  apply Units.ext
  ext i j
  exact h (congrArg (fun x : GeneralLinear n K => x i j) he)

/-- The integral subgroup is isomorphic to the general linear group over the integer ring. -/
def equivSubgroup (h : Function.Injective (algebraMap O K)) :
    GeneralLinear n O ≃* subgroup O K n :=
  MulEquiv.ofBijective (MonoidHom.rangeRestrict _) ⟨fun _ _ h' => map_injective h
    (congrArg Subtype.val h'), MonoidHom.rangeRestrict_surjective _⟩

@[simp] theorem coe_equivSubgroup (h : Function.Injective (algebraMap O K))
    (g : GeneralLinear n O) : (equivSubgroup h g : GeneralLinear n K) = map (algebraMap O K) g :=
  rfl

/-- Entrywise reduction on the integral subgroup. -/
def reduction [IsLocalRing O] (h : Function.Injective (algebraMap O K)) :
    subgroup O K n →* GeneralLinear n (ResidueField O) :=
  (map (residue O)).comp (equivSubgroup h).symm.toMonoidHom

@[simp] theorem reduction_equivSubgroup [IsLocalRing O] (h : Function.Injective (algebraMap O K))
    (g : GeneralLinear n O) : reduction h (equivSubgroup h g) = map (residue O) g := by
  change map (residue O) ((equivSubgroup h).symm (equivSubgroup h g)) = _
  rw [MulEquiv.symm_apply_apply]

/-- Reduction of invertible matrices over a local ring is surjective. -/
theorem map_residue_surjective [IsLocalRing O] :
    Function.Surjective (map (n := Fin n) (residue O)) := by
  intro g
  choose a ha using fun i j : Fin n => residue_surjective (g i j)
  let A : Matrix (Fin n) (Fin n) O := a
  have hA : A.map (residue O) = g.val := Matrix.ext ha
  have hd : residue O A.det ≠ 0 := by
    have hdet := RingHom.map_det (residue O) A
    change residue O A.det = (A.map (residue O)).det at hdet
    rw [hdet, hA]
    exact (det g).ne_zero
  refine ⟨mk'' A ((residue_ne_zero_iff_isUnit _).1 hd), Units.ext hA⟩

theorem reduction_surjective [IsLocalRing O] (h : Function.Injective (algebraMap O K)) :
    Function.Surjective (reduction (n := n) h) := by
  intro g
  obtain ⟨a, ha⟩ := map_residue_surjective g
  exact ⟨equivSubgroup h a, (reduction_equivSubgroup _ _).trans ha⟩

/-- An invertible matrix is integral when both it and its inverse have integral entries. -/
theorem mem_subgroup_iff (h : Function.Injective (algebraMap O K)) (g : GeneralLinear n K) :
    g ∈ subgroup O K n ↔
      (∀ i j, g i j ∈ (algebraMap O K).range) ∧ (∀ i j, g⁻¹ i j ∈ (algebraMap O K).range) := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun i j => ⟨a i j, rfl⟩, fun i j => ⟨a⁻¹ i j, ?_⟩⟩
    rw [← map_inv]
    rfl
  · rintro ⟨h₁, h₂⟩
    choose a ha using h₁
    choose b hb using h₂
    let A : Matrix (Fin n) (Fin n) O := a
    let B : Matrix (Fin n) (Fin n) O := b
    have hA : A.map (algebraMap O K) = g.val := Matrix.ext ha
    have hB : B.map (algebraMap O K) = g⁻¹.val := Matrix.ext hb
    have hi : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map (algebraMap O K)) :=
      fun _ _ hm => Matrix.ext fun i j => h (congrArg (fun M => M i j) hm)
    refine ⟨⟨A, B, hi ?_, hi ?_⟩, Units.ext hA⟩
    · change (A * B).map (algebraMap O K) = (1 : Matrix _ _ O).map (algebraMap O K)
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.val_inv
    · change (B * A).map (algebraMap O K) = (1 : Matrix _ _ O).map (algebraMap O K)
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_val

end IntegralMatrices

namespace CuspidalMatrixIntertwining

open IntegralMatrices Matrix Matrix.GeneralLinearGroup
open GeneralLinear.Iwasawa Langlands.ProductLeviChamber

variable {O K Γ : Type*} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ} {ϖ : Kˣ}

omit [IsLocalRing O] in
private theorem subgroup_eq_integralRange (hv : v.Integers O) (n : ℕ) :
    subgroup O K n = integralRange v n := by
  ext g
  rw [mem_subgroup_iff hv.hom_inj, integralRange]
  change _ ↔ g ∈ subgroup v.integer K n
  rw [mem_subgroup_iff (Valuation.integer.integers v).hom_inj]
  have he (a : K) : a ∈ (algebraMap O K).range ↔ a ∈ (algebraMap v.integer K).range :=
    ⟨fun ⟨x, hx⟩ => ⟨⟨a, hx ▸ hv.map_le_one x⟩, rfl⟩,
      fun ⟨x, hx⟩ => hv.exists_of_le_one (hx ▸ x.2)⟩
  simp only [he]

private theorem twoBlock_index_lt {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (i : Fin (twoBlock n k hk hkn).length) (a : Fin ((twoBlock n k hk hkn).size i)) :
    (twoBlock n k hk hkn).index i a < k ↔ i.val = 0 := by
  rw [twoBlock_index_val]
  by_cases h₀ : i.val = 0
  · let i₀ : Fin (twoBlock n k hk hkn).length := ⟨0, by change 0 < 2; decide⟩
    have he : i = i₀ := Fin.ext h₀
    subst i
    have ha : a.val < k := a.isLt
    simpa [i₀] using ha
  · simp [h₀]

private theorem twoBlock_proper (k n : ℕ) (hk : 0 < k) (hkn : k < n) (k₀ : Type*) [Field k₀] :
    (twoBlock n k hk hkn).parabolic k₀ ≠ ⊤ := by
  let B := twoBlock n k hk hkn
  let p : Fin B.length := ⟨1, by change 1 < 2; decide⟩
  let q : Fin B.length := ⟨0, by change 0 < 2; decide⟩
  let a : Fin (B.size p) := ⟨0, B.positive p⟩
  let b : Fin (B.size q) := ⟨0, B.positive q⟩
  have hab : B.index p a ≠ B.index q b := by
    intro h
    have he := congrArg Sigma.fst (B.indexEquiv.injective h)
    have he' := congrArg Fin.val he
    contradiction
  let u := GeneralLinear.transvectionUnit _ _ hab (1 : k₀)
  intro h
  have hu : u ∈ B.parabolic k₀ := h.symm ▸ Subgroup.mem_top u
  have hz := (B.mem_parabolic_iff _ u).1 hu p q a b (by change 0 < 1; decide)
  change Matrix.transvection (B.index p a) (B.index q b) 1 _ _ = 0 at hz
  simp [Matrix.transvection, hab] at hz

private theorem radical_entry_eq_one {k₀ : Type*} [Field k₀] {n k : ℕ}
    (hk : 0 < k) (hkn : k < n) {u : GeneralLinear n k₀}
    (hu : u ∈ (twoBlock n k hk hkn).unipotentSubgroup k₀) (i j : Fin n)
    (hij : ¬ (i.val < k ∧ k ≤ j.val)) : u i j = (1 : Matrix (Fin n) (Fin n) k₀) i j := by
  let B := twoBlock n k hk hkn
  obtain ⟨⟨p, a⟩, rfl⟩ := B.indexEquiv.surjective i
  obtain ⟨⟨q, b⟩, rfl⟩ := B.indexEquiv.surjective j
  change ¬ ((B.index p a).val < k ∧ k ≤ (B.index q b).val) at hij
  have hcut : ¬ (p.val = 0 ∧ q.val ≠ 0) := by
    simpa only [← not_lt (a := (B.index q b).val), B, twoBlock_index_lt hk hkn] using hij
  obtain ⟨hp, hd⟩ := (B.mem_unipotentSubgroup_iff _ u).1 hu
  change u (B.index p a) (B.index q b) = _
  by_cases he : p = q
  · subst q
    rw [Matrix.one_apply]
    have hab : (B.indexEquiv ⟨p, a⟩ = B.indexEquiv ⟨p, b⟩) ↔ a = b :=
      (B.index p).injective.eq_iff
    simpa only [hab] using hd p a b
  · have hpq : q < p := by
      have hp' : p.val < 2 := p.isLt
      have hq' : q.val < 2 := q.isLt
      have hne : p.val ≠ q.val := fun h => he (Fin.ext h)
      omega
    rw [(B.mem_parabolic_iff _ u).1 hp p q a b hpq, Matrix.one_apply_ne]
    exact fun h => he (congrArg Sigma.fst (B.indexEquiv.injective h))

private theorem square_zero_of_cross_cut {R : Type*} [CommRing R] {n k : ℕ}
    {X : Matrix (Fin n) (Fin n) R} (hX : ∀ i j, ¬ (i.val < k ∧ k ≤ j.val) → X i j = 0) :
    X * X = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : l.val < k
  · rw [hX i l (fun h => (not_le_of_gt hl) h.2), zero_mul]
  · rw [hX l j (fun h => hl h.1), mul_zero]

private def oneAddUnit {R : Type*} [CommRing R] {n : ℕ} (X : Matrix (Fin n) (Fin n) R)
    (hX : X * X = 0) : GeneralLinear n R :=
  ⟨1 + X, 1 - X, by simp [add_mul, mul_sub, hX], by simp [sub_mul, mul_add, hX]⟩

private theorem cross_cut_lifts (hv : v.Integers O) (hϖ : IsUniformizingElement v ϖ)
    {n k : ℕ} (hk : 0 < k) (hkn : k < n) {a : Fin n → ℤ}
    (hgap : ∀ i j : Fin n, i.val < k → k ≤ j.val → a j < a i)
    {u : GeneralLinear n (ResidueField O)}
    (hu : u ∈ (twoBlock n k hk hkn).unipotentSubgroup (ResidueField O)) :
    ∃ (j : subgroup O K n) (hj : torus ϖ a * j.val * (torus ϖ a)⁻¹ ∈ subgroup O K n),
      reduction hv.hom_inj j = u ∧ reduction hv.hom_inj ⟨_, hj⟩ = 1 := by
  classical
  choose x hx using fun i j : Fin n => residue_surjective ((u.val - 1) i j)
  let X : Matrix (Fin n) (Fin n) O := fun i j => if i.val < k ∧ k ≤ j.val then x i j else 0
  have hX i j (h : ¬ (i.val < k ∧ k ≤ j.val)) : X i j = 0 := by simp [X, h]
  have hval (i j : Fin n) (h : i.val < k ∧ k ≤ j.val) :
      v ((ϖ ^ (a i - a j) : Kˣ) : K) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact zpow_lt_one₀ (valuation_pos v ϖ) hϖ.1 (sub_pos.2 (hgap i j h.1 h.2))
  choose c hc using fun i j h => hv.exists_of_le_one (hval i j h).le
  let Y : Matrix (Fin n) (Fin n) O := fun i j =>
    if h : i.val < k ∧ k ≤ j.val then c i j h * X i j else 0
  have hY i j (h : ¬ (i.val < k ∧ k ≤ j.val)) : Y i j = 0 := by simp [Y, h]
  let z := oneAddUnit X (square_zero_of_cross_cut hX)
  let w := oneAddUnit Y (square_zero_of_cross_cut hY)
  let U := equivSubgroup (n := n) hv.hom_inj
  have he : torus ϖ a * (U z).val * (torus ϖ a)⁻¹ = (U w).val := by
    apply Units.ext
    ext i j
    change (torus ϖ a * (map (algebraMap O K) z) * (torus ϖ a)⁻¹) i j =
      algebraMap O K ((1 + Y) i j)
    rw [torus_inv, torus, diagonalUnits_mul_mul_apply, Matrix.GeneralLinearGroup.map_apply]
    change ((ϖ ^ a i : Kˣ) : K) * algebraMap O K ((1 + X) i j) *
      (((ϖ ^ a j)⁻¹ : Kˣ) : K) = _
    simp only [Matrix.add_apply, map_add, mul_add, add_mul]
    have h₁ : ((ϖ ^ a i : Kˣ) : K) * algebraMap O K ((1 : Matrix (Fin n) (Fin n) O) i j) *
        (((ϖ ^ a j)⁻¹ : Kˣ) : K) = algebraMap O K ((1 : Matrix (Fin n) (Fin n) O) i j) := by
      by_cases h : i = j
      · subst j
        rw [Matrix.one_apply_eq, map_one, mul_one, ← Units.val_mul, mul_inv_cancel]
        rfl
      · simp [Matrix.one_apply_ne h]
    rw [h₁]
    congr 1
    by_cases h : i.val < k ∧ k ≤ j.val
    · rw [show Y i j = c i j h * X i j from by simp [Y, h], map_mul, hc i j h, _root_.zpow_sub]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      ring
    · rw [hX _ _ h, hY _ _ h]
      simp
  refine ⟨U z, he.symm ▸ (U w).2, ?_, ?_⟩
  · rw [reduction_equivSubgroup]
    apply Units.ext
    ext i j
    change residue O ((1 + X) i j) = u i j
    by_cases h : i.val < k ∧ k ≤ j.val
    · have h₁ : i ≠ j := fun hij => (not_le_of_gt h.1) (hij.symm ▸ h.2)
      rw [Matrix.add_apply, Matrix.one_apply_ne h₁, zero_add, show X i j = x i j by simp [X, h],
        hx, Matrix.sub_apply, Matrix.one_apply_ne h₁, sub_zero]
    · rw [Matrix.add_apply, hX _ _ h, add_zero, radical_entry_eq_one hk hkn hu i j h]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · rw [show (⟨_, _⟩ : subgroup O K n) = U w from Subtype.ext he, reduction_equivSubgroup]
    apply Units.ext
    ext i j
    change residue O ((1 + Y) i j) = (1 : Matrix (Fin n) (Fin n) (ResidueField O)) i j
    have hz : residue O (Y i j) = 0 := by
      by_cases h : i.val < k ∧ k ≤ j.val
      · have hc' : residue O (c i j h) = 0 := by
          by_contra! hn
          exact (hval i j h).ne ((hc i j h) ▸ hv.one_of_isUnit ((residue_ne_zero_iff_isUnit _).1 hn))
        simp [Y, h, hc']
      · rw [hY _ _ h, map_zero]
    rw [Matrix.add_apply, map_add, hz, add_zero]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem exists_cross_cut {n : ℕ} {a : Fin n → ℤ} (ha : Antitone a)
    (h : ¬ ∃ z, a = fun _ => z) :
    ∃ k, 0 < k ∧ k < n ∧ ∀ i j : Fin n, i.val < k → k ≤ j.val → a j < a i := by
  classical
  have hn : 0 < n := by
    by_contra! hz
    have hn0 : n = 0 := by omega
    exact h ⟨0, funext fun i => ((show ¬ i.val < n by omega) i.isLt).elim⟩
  let i₀ : Fin n := ⟨0, hn⟩
  have ex : ∃ j : Fin n, a j < a i₀ := by
    by_contra! hn'
    exact h ⟨a i₀, funext fun j => le_antisymm (ha (Nat.zero_le j.val)) (hn' j)⟩
  let p (k : ℕ) := ∃ j : Fin n, j.val = k ∧ a j < a i₀
  have hp : ∃ k, p k := ⟨_, ex.choose, rfl, ex.choose_spec⟩
  obtain ⟨j, hj, hj'⟩ := Nat.find_spec hp
  refine ⟨Nat.find hp, ?_, hj ▸ j.isLt, ?_⟩
  · by_contra! hk
    have he : j = i₀ := Fin.ext (hj.trans (Nat.eq_zero_of_le_zero hk))
    exact (lt_irrefl _) (he ▸ hj')
  · intro r s hr hs
    have hr' : a i₀ ≤ a r := by
      by_contra! hr'
      exact Nat.find_min hp hr ⟨r, rfl, hr'⟩
    have hjs : j ≤ s := show j.val ≤ s.val by rwa [hj]
    exact (ha hjs).trans_lt (hj'.trans_le hr')

/-- An inflated cuspidal representation on a nonzero carrier is
intertwined exactly by products of scalar matrices and integral matrices. -/
theorem selfIntertwining_inflatedCuspidal (hv : v.Integers O) (hϖ : IsUniformizingElement v ϖ)
    {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    (σ : Representation ℂ (GeneralLinear n (ResidueField O)) W)
    (hσ : FiniteGeneralLinear.IsCuspidal σ) :
    representationSelfIntertwining (σ.comp (reduction hv.hom_inj)) =
      Set.range (GeneralLinear.scalar (n := n) (R := K)) * (subgroup O K n : Set _) := by
  let ρ := σ.comp (reduction hv.hom_inj)
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, he⟩ := GeneralLinear.Cartan.exists_cartan hϖ n g
    rw [← subgroup_eq_integralRange hv] at hk₁ hk₂
    have ht : Intertwines ρ ρ (torus ϖ a) :=
      (intertwines_mul_left_right_iff ρ _ ⟨_, hk₁⟩ ⟨_, hk₂⟩).1 (he ▸ hg)
    by_cases hc : ∃ z, a = fun _ => z
    · obtain ⟨z, rfl⟩ := hc
      have hd : torus ϖ (fun _ : Fin n => z) = GeneralLinear.scalar (ϖ ^ z) := rfl
      refine ⟨_, ⟨ϖ ^ z, rfl⟩, k₁ * k₂, mul_mem hk₁ hk₂, ?_⟩
      change GeneralLinear.scalar (ϖ ^ z) * (k₁ * k₂) = g
      rw [he, hd, ← mul_assoc,
        (Matrix.GeneralLinearGroup.scalar_commute (ϖ ^ z) k₁)]
    · exfalso
      obtain ⟨k, hk, hkn, hgap⟩ := exists_cross_cut ha hc
      obtain ⟨T, hT, h⟩ := (selfIntertwines_iff ρ _).1 ht
      apply hT
      ext w
      change T w = 0
      apply hσ (twoBlock n k hk hkn) (twoBlock_proper k n hk hkn _) (T w)
      intro u hu
      obtain ⟨j, hj, hju, hj₀⟩ := cross_cut_lifts hv hϖ hk hkn hgap hu
      have eq := h j hj w
      change T (σ (reduction hv.hom_inj ⟨_, hj⟩) w) = σ (reduction hv.hom_inj j) (T w) at eq
      rwa [hj₀, hju, map_one, Module.End.one_apply, eq_comm] at eq
  · rintro ⟨_, ⟨a, rfl⟩, k, hk, rfl⟩
    have hs : GeneralLinear.scalar (n := n) a ∈ Subgroup.center (GeneralLinear n K) :=
      (GeneralLinear.scalarToCenter a).2
    have ht := (intertwines_mul_left_right_iff ρ _ 1 ⟨k, hk⟩).2
      (selfIntertwines_of_central ρ hs)
    change Intertwines ρ ρ (GeneralLinear.scalar a * k)
    simpa only [Subgroup.coe_one, one_mul] using ht

end CuspidalMatrixIntertwining

end Langlands.BushnellKutzko
