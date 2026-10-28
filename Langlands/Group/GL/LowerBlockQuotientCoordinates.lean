import Langlands.Group.GL.LowerBlockLocalizationCoordinates
import Langlands.Group.GL.RankReindex
import Langlands.Group.GL.UpperUnipotent
import Langlands.Analysis.Local.QuotientTopology

/-! # Lower-block coordinates on the actual left unipotent quotient

The coordinate map `([g], x, h) ↦ [[[g,0],[x,h]]]` from
`N_a \ GL_a × M_{d×a} × B⁻_d` to `N_{a+d} \ GL_{a+d}`, used in JPSS §9.3.
See the paired Markdown for the source derivation and the exact scope.
-/

noncomputable section

namespace Langlands.GeneralLinear

open Langlands.QuotientIntegration

universe u

variable {R : Type u} [CommRing R] {a d : ℕ}

/-! ### Matrix and subgroup laws -/

/-- A matrix that is both upper and lower triangular with unit diagonal is the identity. -/
theorem matrix_eq_one_of_triangular {n : ℕ} {D : Matrix (Fin n) (Fin n) R}
    (hU : D.IsUpperTriangular) (hL : D.IsLowerTriangular) (hd : ∀ i, D i i = 1) :
    D = 1 := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [hL hij, Matrix.one_apply_ne (ne_of_lt hij)]
  · rw [hd, Matrix.one_apply_eq]
  · rw [hU hji, Matrix.one_apply_ne (ne_of_gt hji)]

/-- The four blocks of `lowerBlockPair g x h` in the `Fin a ⊕ Fin d` coordinates. -/
theorem lowerBlockPair_val_submatrix (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    (lowerBlockPair g x h).val.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks g.val 0 x h.val.val := by
  change ((Matrix.fromBlocks g.val 0 x h.val.val).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm).submatrix finSumFinEquiv finSumFinEquiv = _
  simp

/-- The four blocks of `rankInclusion d u` in the `Fin a ⊕ Fin d` coordinates. -/
theorem rankInclusion_val_submatrix (u : Langlands.GeneralLinear a R) :
    (rankInclusion d u).val.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks u.val 0 0 1 := by
  change ((Matrix.fromBlocks u.val 0 0 (1 : Matrix (Fin d) (Fin d) R)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm).submatrix finSumFinEquiv finSumFinEquiv = _
  simp

/-- Standard rank inclusion carries `N_a` into `N_{a+d}`. -/
theorem rankInclusion_mem_upperUnipotent {u : Langlands.GeneralLinear a R}
    (hu : u ∈ upperUnipotent a R) : rankInclusion d u ∈ upperUnipotent (a + d) R := by
  have he (i j : Fin (a + d)) : rankInclusion d u i j =
      Matrix.fromBlocks u.val 0 0 (1 : Matrix (Fin d) (Fin d) R)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
    rw [← rankInclusion_val_submatrix]
    simp
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [he]
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
        exact hu.1 hji
      | right j => simp
    | right i =>
      induction j using Fin.addCases with
      | left j => simp
      | right j =>
        simp only [finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
        exact Matrix.one_apply_ne (by
          rintro rfl
          exact lt_irrefl _ hji)
  · rw [he]
    induction i using Fin.addCases with
    | left i => simpa using hu.2 i
    | right i => simp

/-- Left multiplication by `diag(u, I_d)` acts on the first coordinate only. -/
theorem rankInclusion_mul_lowerBlockPair (u g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    rankInclusion d u * lowerBlockPair g x h = lowerBlockPair (u * g) x h := by
  apply Units.ext
  change (Matrix.fromBlocks u.val 0 0 (1 : Matrix (Fin d) (Fin d) R)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm *
    (Matrix.fromBlocks g.val 0 x h.val.val).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
    (Matrix.fromBlocks (u * g).val 0 x h.val.val).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

/-- Uniqueness of the lower-block display modulo `N_{a+d}`: an upper unipotent
`u` with `u * [[g,0],[x,h]] = [[g',0],[x',h']]` fixes `x` and `h`, the first
blocks differ by the element `g' * g⁻¹` of `N_a`, and `u = diag(g' * g⁻¹, I_d)`. -/
theorem lowerBlockPair_eq_of_upperUnipotent_mul {u : Langlands.GeneralLinear (a + d) R}
    (hu : u ∈ upperUnipotent (a + d) R) {g g' : Langlands.GeneralLinear a R}
    {x x' : Matrix (Fin d) (Fin a) R} {h h' : lowerTriangularSubgroup d R}
    (he : u * lowerBlockPair g x h = lowerBlockPair g' x' h') :
    g' * g⁻¹ ∈ upperUnipotent a R ∧ x' = x ∧ h' = h ∧
      u = rankInclusion d (g' * g⁻¹) := by
  set U := u.val.submatrix finSumFinEquiv finSumFinEquiv with hUdef
  have hUb : U = Matrix.fromBlocks U.toBlocks₁₁ U.toBlocks₁₂ U.toBlocks₂₁ U.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks U).symm
  have hmul : U * Matrix.fromBlocks g.val 0 x h.val.val =
      Matrix.fromBlocks g'.val 0 x' h'.val.val := by
    rw [← lowerBlockPair_val_submatrix, ← lowerBlockPair_val_submatrix, ← he, hUdef,
      Units.val_mul, Matrix.submatrix_mul_equiv]
  rw [hUb, Matrix.fromBlocks_multiply] at hmul
  obtain ⟨h11, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp hmul
  -- The lower-left block of `U` vanishes since `u` is upper triangular.
  have hC : U.toBlocks₂₁ = 0 := by
    ext i j
    change u.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0
    apply hu.1
    change finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
    simp [Fin.lt_def]
    omega
  -- The upper-right block vanishes since `h` is invertible.
  have hB : U.toBlocks₁₂ = 0 := by
    simp only [Matrix.mul_zero, zero_add] at h12
    calc U.toBlocks₁₂ = U.toBlocks₁₂ * h.val.val * (h.val⁻¹).val := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.mul_one]
      _ = 0 := by rw [h12, Matrix.zero_mul]
  -- The lower-right block is upper unipotent and lower triangular, hence trivial.
  have hD : U.toBlocks₂₂ = 1 := by
    simp only [hC, Matrix.mul_zero, zero_add] at h22
    have hDeq : U.toBlocks₂₂ = h'.val.val * (h⁻¹).val.val := by
      calc U.toBlocks₂₂ = U.toBlocks₂₂ * h.val.val * (h.val⁻¹).val := by
            rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.mul_one]
        _ = h'.val.val * (h⁻¹).val.val := by rw [h22]; rfl
    apply matrix_eq_one_of_triangular
    · intro i j hji
      change u.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = 0
      apply hu.1
      change finSumFinEquiv (Sum.inr j) < finSumFinEquiv (Sum.inr i)
      simpa using hji
    · rw [hDeq]
      exact Matrix.BlockTriangular.mul h'.property (h⁻¹).property
    · intro i
      change u (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr i)) = 1
      exact hu.2 _
  simp only [hB, hC, hD, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.one_mul] at h11 h21 h22
  have hA : (g' * g⁻¹).val = U.toBlocks₁₁ := by
    rw [Units.val_mul, ← h11, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one]
  have huA : u = rankInclusion d (g' * g⁻¹) := by
    apply Units.ext
    have hsub : u.val.submatrix finSumFinEquiv finSumFinEquiv =
        (rankInclusion d (g' * g⁻¹)).val.submatrix finSumFinEquiv finSumFinEquiv := by
      rw [rankInclusion_val_submatrix, hA, ← hB, ← hC, ← hD, ← hUb]
    have := congrArg (fun M => M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) hsub
    simpa using this
  refine ⟨⟨fun i j hji => ?_, fun i => ?_⟩, h21.symm, Subtype.ext (Units.ext h22.symm), huA⟩
  · rw [hA]
    change u.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = 0
    apply hu.1
    exact hji
  · rw [hA]
    change u (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl i)) = 1
    exact hu.2 _

/-! ### Representative independence and injectivity -/

/-- Equality of left cosets `N * k`, in the convention of `QuotientIntegration.LeftQuotient`. -/
theorem leftQuotient_mk_eq_iff {G : Type*} [Group G] (H : Subgroup G) (k k' : G) :
    (Quotient.mk _ k : LeftQuotient H) = Quotient.mk _ k' ↔ k' * k⁻¹ ∈ H := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply]

/-- The coset of `[[g,0],[x,h]]` depends only on the coset `N_a * g`. -/
theorem leftQuotient_mk_lowerBlockPair_mul {n : Langlands.GeneralLinear a R}
    (hn : n ∈ upperUnipotent a R) (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    (Quotient.mk _ (lowerBlockPair (n * g) x h) : LeftQuotient (upperUnipotent (a + d) R)) =
      Quotient.mk _ (lowerBlockPair g x h) := by
  rw [leftQuotient_mk_eq_iff, ← rankInclusion_mul_lowerBlockPair, mul_inv_rev,
    ← mul_assoc, mul_inv_cancel, one_mul, ← map_inv]
  exact rankInclusion_mem_upperUnipotent (inv_mem hn)

/-- Two lower-block displays have the same `N_{a+d}` coset exactly when their
first blocks have the same `N_a` coset and their other coordinates agree. -/
theorem leftQuotient_mk_lowerBlockPair_eq_iff (g g' : Langlands.GeneralLinear a R)
    (x x' : Matrix (Fin d) (Fin a) R) (h h' : lowerTriangularSubgroup d R) :
    (Quotient.mk _ (lowerBlockPair g x h) : LeftQuotient (upperUnipotent (a + d) R)) =
        Quotient.mk _ (lowerBlockPair g' x' h') ↔
      (Quotient.mk _ g : LeftQuotient (upperUnipotent a R)) = Quotient.mk _ g' ∧
        x = x' ∧ h = h' := by
  constructor
  · intro he
    rw [leftQuotient_mk_eq_iff] at he
    obtain ⟨hg, hx, hh, -⟩ := lowerBlockPair_eq_of_upperUnipotent_mul he
      (inv_mul_cancel_right (lowerBlockPair g' x' h') (lowerBlockPair g x h))
    exact ⟨(leftQuotient_mk_eq_iff _ _ _).mpr hg, hx.symm, hh.symm⟩
  · rintro ⟨hg, rfl, rfl⟩
    rw [leftQuotient_mk_eq_iff] at hg
    have := leftQuotient_mk_lowerBlockPair_mul hg g x h
    rw [inv_mul_cancel_right] at this
    exact this.symm

/-- The actual parameter space `N_a \ GL_a × M_{d×a} × B⁻_d`, with the
quotient topology on the first factor and the product topology. -/
abbrev LowerBlockQuotientParameters (a d : ℕ) (R : Type u) [CommRing R] :=
  LeftQuotient (upperUnipotent a R) × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R

/-- The descended chart `([g], x, h) ↦ [[[g,0],[x,h]]]` into `N_{a+d} \ GL_{a+d}`. -/
def lowerBlockQuotientChart (p : LowerBlockQuotientParameters a d R) :
    LeftQuotient (upperUnipotent (a + d) R) :=
  descend (upperUnipotent a R)
    (fun g => (Quotient.mk _ (lowerBlockPair g p.2.1 p.2.2) :
      LeftQuotient (upperUnipotent (a + d) R)))
    (fun n g => leftQuotient_mk_lowerBlockPair_mul n.property g p.2.1 p.2.2) p.1

/-- The representative evaluation equation. -/
@[simp] theorem lowerBlockQuotientChart_mk (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    lowerBlockQuotientChart (Quotient.mk _ g, x, h) =
      (Quotient.mk _ (lowerBlockPair g x h) : LeftQuotient (upperUnipotent (a + d) R)) :=
  rfl

/-- The descended chart is injective. -/
theorem lowerBlockQuotientChart_injective :
    Function.Injective (lowerBlockQuotientChart (a := a) (d := d) (R := R)) := by
  rintro ⟨q, x, h⟩ ⟨q', x', h'⟩ he
  induction q using Quotient.inductionOn with
  | h g =>
    induction q' using Quotient.inductionOn with
    | h g' =>
      obtain ⟨hg, rfl, rfl⟩ :=
        (leftQuotient_mk_lowerBlockPair_eq_iff g g' x x' h h').mp he
      rw [hg]

/-- The actual range of the descended chart. No decomposition of the whole
quotient is asserted. -/
def lowerBlockQuotientRange (a d : ℕ) (R : Type u) [CommRing R] :
    Set (LeftQuotient (upperUnipotent (a + d) R)) :=
  Set.range (lowerBlockQuotientChart (a := a) (d := d) (R := R))

/-- A coset is in the range exactly when it is the coset of a lower-block display. -/
theorem mem_lowerBlockQuotientRange_iff (q : LeftQuotient (upperUnipotent (a + d) R)) :
    q ∈ lowerBlockQuotientRange a d R ↔
      ∃ (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R)
        (h : lowerTriangularSubgroup d R), Quotient.mk _ (lowerBlockPair g x h) = q := by
  constructor
  · rintro ⟨⟨p, x, h⟩, rfl⟩
    induction p using Quotient.inductionOn with
    | h g => exact ⟨g, x, h, rfl⟩
  · rintro ⟨g, x, h, rfl⟩
    exact ⟨(Quotient.mk _ g, x, h), rfl⟩

/-- A representative's coset is in the range exactly when some element of `N_{a+d}`
moves the representative to a lower-block display. -/
theorem mk_mem_lowerBlockQuotientRange_iff (k : Langlands.GeneralLinear (a + d) R) :
    (Quotient.mk _ k : LeftQuotient (upperUnipotent (a + d) R)) ∈
        lowerBlockQuotientRange a d R ↔
      ∃ n ∈ upperUnipotent (a + d) R, ∃ (g : Langlands.GeneralLinear a R)
        (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R),
          n * k = lowerBlockPair g x h := by
  rw [mem_lowerBlockQuotientRange_iff]
  constructor
  · rintro ⟨g, x, h, he⟩
    rw [leftQuotient_mk_eq_iff] at he
    refine ⟨_, inv_mem he, g, x, h, ?_⟩
    group
  · rintro ⟨n, hn, g, x, h, he⟩
    refine ⟨g, x, h, ?_⟩
    rw [leftQuotient_mk_eq_iff, ← he]
    simpa using hn

/-- The descended chart as a bijection onto its actual range. The inverse is
determined by the proved injectivity, not by a choice of coset representatives. -/
def lowerBlockQuotientEquivRange :
    LowerBlockQuotientParameters a d R ≃ lowerBlockQuotientRange a d R :=
  Equiv.ofInjective _ lowerBlockQuotientChart_injective

@[simp] theorem lowerBlockQuotientEquivRange_apply (p : LowerBlockQuotientParameters a d R) :
    (lowerBlockQuotientEquivRange p).val = lowerBlockQuotientChart p :=
  rfl

/-- The inverse coordinate map on the actual range. -/
def lowerBlockQuotientInverse (q : lowerBlockQuotientRange a d R) :
    LowerBlockQuotientParameters a d R :=
  lowerBlockQuotientEquivRange.symm q

/-- First inverse law: the inverse undoes the chart. -/
@[simp] theorem lowerBlockQuotientInverse_chart (p : LowerBlockQuotientParameters a d R) :
    lowerBlockQuotientInverse ⟨lowerBlockQuotientChart p, ⟨p, rfl⟩⟩ = p :=
  Equiv.ofInjective_symm_apply _ p

/-- Second inverse law: the chart undoes the inverse on the range. -/
@[simp] theorem lowerBlockQuotientChart_inverse (q : lowerBlockQuotientRange a d R) :
    lowerBlockQuotientChart (lowerBlockQuotientInverse q) = q.val :=
  Equiv.apply_ofInjective_symm _ q

/-- The inverse at the coset of an explicit lower-block display. -/
@[simp] theorem lowerBlockQuotientInverse_mk (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    lowerBlockQuotientInverse
        ⟨Quotient.mk _ (lowerBlockPair g x h), ⟨(Quotient.mk _ g, x, h), rfl⟩⟩ =
      (Quotient.mk _ g, x, h) :=
  lowerBlockQuotientInverse_chart (Quotient.mk _ g, x, h)

/-- The inverse is characterized by the chart. -/
theorem lowerBlockQuotientInverse_eq_iff (q : lowerBlockQuotientRange a d R)
    (p : LowerBlockQuotientParameters a d R) :
    lowerBlockQuotientInverse q = p ↔ lowerBlockQuotientChart p = q.val := by
  constructor
  · rintro rfl
    exact lowerBlockQuotientChart_inverse q
  · intro he
    apply lowerBlockQuotientChart_injective
    rw [lowerBlockQuotientChart_inverse, he]

/-! ### Rank transport -/

section RankTransport

/-- Reindexing along `Fin m = Fin n` preserves upper unipotence. -/
theorem reindex_finCongr_mem_upperUnipotent_iff {m n : ℕ} (hmn : m = n)
    (k : Langlands.GeneralLinear m R) :
    reindex (finCongr hmn) k ∈ upperUnipotent n R ↔ k ∈ upperUnipotent m R := by
  subst hmn
  have : reindex (finCongr (rfl : m = m)) k = k := by
    apply Units.ext
    ext i j
    rfl
  rw [this]

variable [TopologicalSpace R]

/-- The homeomorphism of left unipotent quotients induced by an equality of ranks. -/
def upperUnipotentQuotientCongr {m n : ℕ} (hmn : m = n) :
    LeftQuotient (upperUnipotent m R) ≃ₜ LeftQuotient (upperUnipotent n R) :=
  Homeomorph.Quotient.congr (reindexContinuous (R := R) (finCongr hmn)).toHomeomorph (by
    intro k k'
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change k' * k⁻¹ ∈ upperUnipotent m R ↔
      reindex (finCongr hmn) k' * (reindex (finCongr hmn) k)⁻¹ ∈ upperUnipotent n R
    rw [← map_inv, ← map_mul, reindex_finCongr_mem_upperUnipotent_iff])

@[simp] theorem upperUnipotentQuotientCongr_mk {m n : ℕ} (hmn : m = n)
    (k : Langlands.GeneralLinear m R) :
    upperUnipotentQuotientCongr hmn (Quotient.mk _ k) =
      Quotient.mk _ (reindex (finCongr hmn) k) :=
  rfl

end RankTransport

/-! ### Continuity -/

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The raw lower-block display is jointly continuous. -/
theorem continuous_lowerBlockPair :
    Continuous (fun p : LowerBlockParameters a d R => lowerBlockPair p.1 p.2.1 p.2.2) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun p : LowerBlockParameters a d R =>
      (Matrix.fromBlocks p.1.val 0 p.2.1 p.2.2.val.val).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm)
    exact ((Units.continuous_val.comp continuous_fst).matrix_fromBlocks continuous_const
      (continuous_fst.comp continuous_snd)
      (Units.continuous_val.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).matrix_submatrix
      _ _
  · simp only [lowerBlockPair_inv]
    change Continuous (fun p : LowerBlockParameters a d R =>
      (Matrix.fromBlocks (p.1⁻¹).val 0 (-(p.2.2.val⁻¹).val * p.2.1 * (p.1⁻¹).val)
        (p.2.2.val⁻¹).val).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    exact ((Units.continuous_coe_inv.comp continuous_fst).matrix_fromBlocks continuous_const
      (((Units.continuous_coe_inv.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).neg.matrix_mul
        (continuous_fst.comp continuous_snd)).matrix_mul
        (Units.continuous_coe_inv.comp continuous_fst))
      (Units.continuous_coe_inv.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).matrix_submatrix
      _ _

/-- The descended chart is jointly continuous for the quotient and product topologies. -/
theorem continuous_lowerBlockQuotientChart :
    Continuous (lowerBlockQuotientChart (a := a) (d := d) (R := R)) := by
  have hq : IsOpenQuotientMap (Prod.map (leftQuotientMap (upperUnipotent a R))
      (id : Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R →
        Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R)) :=
    (leftQuotient_isOpenQuotientMap _).prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  exact (leftQuotient_isOpenQuotientMap _).continuous.comp continuous_lowerBlockPair

end Topology

end Langlands.GeneralLinear
