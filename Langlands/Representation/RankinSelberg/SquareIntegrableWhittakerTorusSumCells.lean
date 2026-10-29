import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCoefficient
import Langlands.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.BlockModulusHaarProof
import Langlands.Analysis.CountableCellLpProof
import Langlands.Representation.Classification.Tempered

/-!
# Disjoint cells below the antitone torus cone

Let `K(r)` be a positive principal level of `GL_(m+1)(F)`, `a = ϖ^lam` an antitone torus
element with last exponent zero, and `N` the upper-unipotent group. The subgroup
`H_a = {u ∈ N | a u a⁻¹ ∈ K(r)}` contains `N ∩ K(r)` with index `δ(a)⁻¹`, computed with
Haar measure on `N`. The translates `a h K(r)` for `h ∈ H_a / (N ∩ K(r))` and antitone `lam`
have pairwise disjoint images in `G / Z`. A bi-`K(r)`-invariant matrix coefficient is
constant on each of them, so square-integrability modulo the centre forces the
summability of `δ(a)⁻¹ ‖L (π(a) v)‖²` over the antitone cone.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum

universe uV uF

open GeneralLinear UnequalRankMirabolicUnitTest

/-! ### Disjointness modulo the centre -/

section Algebra

variable {k : Type uF} [Field k] {m : ℕ}

/-- Copied from the published module `Langlands.Group.GL.UpperUnipotent`, where it is
private. -/
private theorem upperTriangular_mul_diag {n : ℕ} {A C : Matrix (Fin n) (Fin n) k}
    (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular) (i : Fin n) :
    (A * C) i i = A i i * C i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hA hji, zero_mul]
  · rw [hC hij, mul_zero]

/-- The diagonal entries of `u ϖ^lam u'`, for upper-unipotent `u` and `u'`, are those
of `ϖ^lam`. -/
theorem unipotent_torus_unipotent_diag (ϖ : kˣ) (lam : Fin (m + 1) → ℤ)
    {u u' : Langlands.GeneralLinear (m + 1) k} (hu : u ∈ upperUnipotent (m + 1) k)
    (hu' : u' ∈ upperUnipotent (m + 1) k) (i : Fin (m + 1)) :
    (u * Iwasawa.torus ϖ lam * u').val i i = ((ϖ ^ lam i : kˣ) : k) := by
  have hD : (Iwasawa.torus ϖ lam).val.IsUpperTriangular := by
    rw [Iwasawa.torus_val]
    exact Matrix.blockTriangular_diagonal _
  rw [Units.val_mul, Units.val_mul, upperTriangular_mul_diag (hu.1.mul hD) hu'.1,
    upperTriangular_mul_diag hu.1 hD, Iwasawa.torus_val, Matrix.diagonal_apply_eq,
    show u.val i i = 1 from hu.2 i, show u'.val i i = 1 from hu'.2 i, one_mul, mul_one]

theorem torus_neg (ϖ : kˣ) (lam : Fin (m + 1) → ℤ) :
    (Iwasawa.torus ϖ lam)⁻¹ = Iwasawa.torus ϖ (-lam) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← torus_add, add_neg_cancel, torus_zero]

variable [ValuativeRel k]

/-- **Disjointness.** Let `r > 0` and `ϖ` be uniformizing. If `ϖ^lam h k₁` and
`ϖ^lam' h' k₂` agree modulo the centre, where `lam` and `lam'` have the same last
exponent, `h, h'` are upper unipotent and `k₁, k₂ ∈ K(r)`, then `lam = lam'` and
`h⁻¹ h' ∈ K(r)`. -/
theorem eq_of_mem_center {r : ℕ} (hr : 0 < r) {ϖ : kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ)
    {lam lam' : Fin (m + 1) → ℤ} (hlast : lam (Fin.last m) = lam' (Fin.last m))
    {h h' k₁ k₂ : Langlands.GeneralLinear (m + 1) k}
    (hh : h ∈ upperUnipotent (m + 1) k) (hh' : h' ∈ upperUnipotent (m + 1) k)
    (hk₁ : k₁ ∈ Conductor.principalLevelSubgroup k m r)
    (hk₂ : k₂ ∈ Conductor.principalLevelSubgroup k m r)
    (hz : (Iwasawa.torus ϖ lam * h * k₁)⁻¹ * (Iwasawa.torus ϖ lam' * h' * k₂) ∈
      Subgroup.center (Langlands.GeneralLinear (m + 1) k)) :
    lam = lam' ∧ h⁻¹ * h' ∈ Conductor.principalLevelSubgroup k m r := by
  classical
  set P := Conductor.principalLevelSubgroup k m r
  set v := ValuativeRel.valuation k
  generalize hZ : (Iwasawa.torus ϖ lam * h * k₁)⁻¹ * (Iwasawa.torus ϖ lam' * h' * k₂) = Z
    at hz
  set d := lam' - lam with hd
  set x := h⁻¹ * Iwasawa.torus ϖ d * h' with hxdef
  have htor : (Iwasawa.torus ϖ lam)⁻¹ * Iwasawa.torus ϖ lam' = Iwasawa.torus ϖ d := by
    rw [inv_mul_eq_iff_eq_mul, ← torus_add, hd, add_sub_cancel]
  have hZx : Z = k₁⁻¹ * x * k₂ := by
    rw [← hZ, hxdef, ← htor]
    group
  have hzc := Subgroup.mem_center_iff.mp hz
  have hx : x = (k₁ * k₂⁻¹) * Z := by
    have h1 : k₂⁻¹ * Z = Z * k₂⁻¹ := hzc k₂⁻¹
    calc x = k₁ * (k₁⁻¹ * x * k₂) * k₂⁻¹ := by group
      _ = k₁ * (Z * k₂⁻¹) := by rw [← hZx]; group
      _ = k₁ * (k₂⁻¹ * Z) := by rw [h1]
      _ = (k₁ * k₂⁻¹) * Z := by group
  have he : k₁ * k₂⁻¹ ∈ P := mul_mem hk₁ (inv_mem hk₂)
  have heinv : (k₁ * k₂⁻¹)⁻¹ = x⁻¹ * Z := by
    rw [hx, mul_inv_rev (k₁ * k₂⁻¹) Z, mul_assoc, hzc (k₁ * k₂⁻¹)⁻¹, inv_mul_cancel_left]
  have hxinv : x⁻¹ = h'⁻¹ * Iwasawa.torus ϖ (-d) * h := by
    rw [hxdef, mul_inv_rev, mul_inv_rev, inv_inv, torus_neg, mul_assoc]
  have hdiag : ∀ i, x.val i i = ((ϖ ^ d i : kˣ) : k) := fun i =>
    unipotent_torus_unipotent_diag ϖ d (inv_mem hh) hh' i
  have hdiaginv : ∀ i, (x⁻¹).val i i = ((ϖ ^ (-d) i : kˣ) : k) := fun i => by
    rw [hxinv]
    exact unipotent_torus_unipotent_diag ϖ (-d) (inv_mem hh') hh i
  -- The centre element is a scalar `c`, and `c ≡ 1` modulo `𝔪^r`.
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hz
  have hdl : d (Fin.last m) = 0 := by
    rw [hd, Pi.sub_apply, hlast, sub_self]
  have hcl : ((k₁ * k₂⁻¹)⁻¹).val (Fin.last m) (Fin.last m) = c := by
    rw [heinv, Units.val_mul, ← hc, Matrix.scalar_apply, Matrix.mul_diagonal, hdiaginv,
      Pi.neg_apply, hdl, neg_zero, zpow_zero, Units.val_one, one_mul]
  have hc1 : c - 1 ∈ levelSet k r := by
    have := ((mem_principalLevelSubgroup_iff _).mp (inv_mem he)).1 (Fin.last m) (Fin.last m)
    rwa [Matrix.one_apply_eq, hcl] at this
  have hZP : Z ∈ P := by
    obtain ⟨E, hE, hEv⟩ := exists_mem_principalLevelSubgroup hr
      (Matrix.scalar (Fin (m + 1)) c) (fun i l => by
        by_cases hil : i = l
        · subst hil
          simpa [Matrix.scalar_apply, Matrix.one_apply_eq] using hc1
        · simpa [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hil,
            Matrix.one_apply_ne hil] using zero_mem_levelSet (F := k) r)
    have : E = Z := Units.ext (hEv.trans hc)
    rwa [← this]
  have hxP : x ∈ P := by
    rw [hx]
    exact mul_mem he hZP
  -- The exponents agree.
  have hϖpos : 0 < v (ϖ : k) := (Valuation.pos_iff v).mpr ϖ.ne_zero
  have hval : ∀ n : ℤ, v ((ϖ ^ n : kˣ) : k) = v (ϖ : k) ^ n := fun n => by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  have hnonneg : ∀ n : ℤ, ((ϖ ^ n : kˣ) : k) ∈ v.integer → 0 ≤ n := by
    intro n hn
    by_contra hneg
    have h1 := one_lt_zpow_of_neg₀ hϖpos hϖ.1 (lt_of_not_ge hneg)
    rw [← hval] at h1
    exact absurd ((Valuation.mem_integer_iff _ _).mp hn) (not_le.mpr h1)
  have hd0 : d = 0 := by
    funext i
    have h1 := hnonneg (d i) (by
      rw [← hdiag i]
      exact mem_integer_of_sub_one_mem_levelSet
        (((mem_principalLevelSubgroup_iff x).mp hxP).1 i i))
    have h2 := hnonneg ((-d) i) (by
      rw [← hdiaginv i]
      exact mem_integer_of_sub_one_mem_levelSet
        (((mem_principalLevelSubgroup_iff x).mp hxP).2 i i))
    rw [Pi.neg_apply] at h2
    rw [Pi.zero_apply]
    omega
  refine ⟨?_, ?_⟩
  · funext i
    have := congrFun hd0 i
    rw [hd, Pi.sub_apply, Pi.zero_apply] at this
    omega
  · have : x = h⁻¹ * h' := by
      rw [hxdef, hd0, torus_zero, mul_one]
    rwa [← this]

end Algebra

/-! ### The index of `N ∩ K(r)` in `H_a` -/

section Index

open GeneralLinear.BlockShape

/-- The upper-unipotent elements of the principal level `K(r)`. -/
def unipotentLevel (k : Type uF) [Field k] [ValuativeRel k] (m r : ℕ) :
    Subgroup (upperUnipotent (m + 1) k) :=
  (Conductor.principalLevelSubgroup k m r).comap (upperUnipotent (m + 1) k).subtype

/-- The subgroup `H_a = {u ∈ N | a u a⁻¹ ∈ K(r)}` for the diagonal element `a`. -/
def conjLevel {k : Type uF} [Field k] [ValuativeRel k] (m r : ℕ) (a : Fin (m + 1) → kˣ) :
    Subgroup (upperUnipotent (m + 1) k) :=
  (unipotentLevel k m r).comap (diagonalConj a).toMonoidHom

variable {k : Type uF} [Field k] [ValuativeRel k] {m r : ℕ}

theorem mem_unipotentLevel {u : upperUnipotent (m + 1) k} :
    u ∈ unipotentLevel k m r ↔
      (u : Langlands.GeneralLinear (m + 1) k) ∈ Conductor.principalLevelSubgroup k m r :=
  Iff.rfl

theorem mem_conjLevel {a : Fin (m + 1) → kˣ} {u : upperUnipotent (m + 1) k} :
    u ∈ conjLevel m r a ↔
      Iwasawa.diagonalUnits a * u * (Iwasawa.diagonalUnits a)⁻¹ ∈
        Conductor.principalLevelSubgroup k m r := by
  change ((diagonalConj a u : upperUnipotent (m + 1) k) :
    Langlands.GeneralLinear (m + 1) k) ∈ Conductor.principalLevelSubgroup k m r ↔ _
  rw [diagonalConj_val]

/-- For antitone exponents, `N ∩ K(r) ≤ H_a`. -/
theorem unipotentLevel_le_conjLevel {ϖ : kˣ} (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1)
    {lam : Fin (m + 1) → ℤ} (hlam : Antitone lam) :
    unipotentLevel k m r ≤ conjLevel m r (fun i => ϖ ^ lam i) := by
  intro u hu
  rw [mem_conjLevel]
  exact torus_conj_upper_mem hϖ hlam u.property hu

/-- **The index count.** For antitone exponents, `N ∩ K(r)` has finite index `δ(a)⁻¹` in
`H_a`, where `δ` is the upper-Borel modulus. -/
theorem index_conjLevel {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (m r : ℕ) (ϖ : F.Carrierˣ) (lam : Fin (m + 1) → ℤ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ValuativeRel.valuation F.Carrier (ϖ : F.Carrier) ≤ 1 → Antitone lam →
      ((unipotentLevel F.Carrier m r).subgroupOf
          (conjLevel m r fun i => ϖ ^ lam i)).FiniteIndex ∧
      (((unipotentLevel F.Carrier m r).subgroupOf
          (conjLevel m r fun i => ϖ ^ lam i)).index : ℝ≥0∞) =
        (((T.leviModulus (singletons (m + 1))
          (singletonLevi F.Carrier fun i => ϖ ^ lam i) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hϖ hlam
  have := T.generalLinearTopologicalGroup (m + 1)
  have := localField_t2 F.Carrier
  let := borel (upperUnipotent (m + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (m + 1) F.Carrier) := ⟨rfl⟩
  set a : Fin (m + 1) → F.Carrierˣ := fun i => ϖ ^ lam i
  set NK := unipotentLevel F.Carrier m r
  set H := conjLevel m r a
  set ν := unipotentHaar F.Carrier m
  set δ : ℝ≥0 := (T.leviModulus (singletons (m + 1)) (singletonLevi F.Carrier a) : ℝ≥0)
  have hle : NK ≤ H := unipotentLevel_le_conjLevel hϖ hlam
  have hNKopen : IsOpen (NK : Set (upperUnipotent (m + 1) F.Carrier)) :=
    (Conductor.principalLevelOpenSubgroup F.Carrier m r).isOpen.preimage
      continuous_subtype_val
  have hNKcompact : IsCompact (NK : Set (upperUnipotent (m + 1) F.Carrier)) :=
    (UpperUnipotent.isClosed (R := F.Carrier) (n := m + 1)).isClosedEmbedding_subtypeVal
      |>.isCompact_preimage (Conductor.isCompact_principalLevelOpenSubgroup F.Carrier m r)
  have hNK0 : ν NK ≠ 0 := (hNKopen.measure_pos ν ⟨1, NK.one_mem⟩).ne'
  have hNKtop : ν NK ≠ ⊤ := hNKcompact.measure_lt_top.ne
  have hconj : ∀ w : upperUnipotent (m + 1) F.Carrier, diagonalConj a (diagonalConj a⁻¹ w) = w := fun w => by
    apply Subtype.ext
    rw [diagonalConj_val, diagonalConj_val, map_inv]
    group
  have hconj' : ∀ w : upperUnipotent (m + 1) F.Carrier, diagonalConj a⁻¹ (diagonalConj a w) = w := fun w => by
    apply Subtype.ext
    rw [diagonalConj_val, diagonalConj_val, map_inv]
    group
  have hHimage : (H : Set (upperUnipotent (m + 1) F.Carrier)) = diagonalConj a⁻¹ '' (NK : Set (upperUnipotent (m + 1) F.Carrier)) := by
    ext u
    constructor
    · intro hu
      exact ⟨diagonalConj a u, hu, hconj' u⟩
    · rintro ⟨w, hw, rfl⟩
      change diagonalConj a (diagonalConj a⁻¹ w) ∈ NK
      rw [hconj]
      exact hw
  have hHcompact : IsCompact (H : Set (upperUnipotent (m + 1) F.Carrier)) := by
    rw [hHimage]
    exact hNKcompact.image (continuous_diagonalConj a⁻¹)
  have hHopen : IsOpen (H : Set (upperUnipotent (m + 1) F.Carrier)) := hNKopen.preimage (continuous_diagonalConj a)
  have : CompactSpace H := isCompact_iff_compactSpace.mp hHcompact
  have hopen' : IsOpen ((NK.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.subgroupOf_isOpen H NK hNKopen
  have : Finite (H ⧸ NK.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hopen'
  have hfi : (NK.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨hfi, ?_⟩
  have hme : MeasurableEmbedding (Subtype.val : H → upperUnipotent (m + 1) F.Carrier) :=
    MeasurableEmbedding.subtype_coe hHopen.measurableSet
  let νH := ν.comap H.subtype
  have : νH.IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap ν (f := H.subtype) hme
  have hidx := (NK.subgroupOf H).index_mul_measure hopen'.measurableSet νH
  have h1 : νH (NK.subgroupOf H : Set H) = ν NK := by
    change (ν.comap Subtype.val) _ = _
    rw [hme.comap_apply]
    congr 1
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hu
      exact ⟨⟨u, hle hu⟩, hu, rfl⟩
  have h2 : νH Set.univ = ν H := by
    change (ν.comap Subtype.val) _ = _
    rw [hme.comap_apply, Set.image_univ, Subtype.range_coe]
  have h3 : ν H = ((δ⁻¹ : ℝ≥0) : ℝ≥0∞) * ν NK := by
    have hmap := diagonalConj_map F T m a
    have hm : Measurable (diagonalConj a) := (continuous_diagonalConj a).measurable
    calc ν H = ν (diagonalConj a ⁻¹' (NK : Set (upperUnipotent (m + 1) F.Carrier))) := rfl
      _ = (ν.map (diagonalConj a)) NK := (Measure.map_apply hm hNKopen.measurableSet).symm
      _ = _ := by
        rw [hmap, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [h1, h2, h3] at hidx
  exact (ENNReal.mul_left_inj hNK0 hNKtop).mp hidx

end Index

/-! ### Cells and square-summability on the antitone cone -/

section Cells

open GeneralLinear.BlockShape

/-- **Square-summability on the antitone cone.** Let `r > 0`, let `ϖ` be uniformizing, let
`L` be a functional invariant under `K(r)` and `v` a vector fixed by `K(r)`, and suppose the
absolute matrix coefficient of `L` and `v` is square-integrable modulo the centre for a Haar
measure. Then `δ(ϖ^μ)⁻¹ ‖L (π(ϖ^μ) v)‖²` is summable over the exponent vectors
`μ = (lam, 0)` that are antitone. -/
theorem summable_antitone {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (m r : ℕ) (hr : 0 < r) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ϖ : F.Carrierˣ), Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V)
      (c : UnitaryCentralCharacter π) (L : Module.Dual ℂ V) (v : V),
      (∀ g ∈ Conductor.principalLevelSubgroup F.Carrier m r, ∀ w, L (π g w) = L w) →
      (∀ g ∈ Conductor.principalLevelSubgroup F.Carrier m r, π g v = v) →
      ∀ [MeasurableSpace (Langlands.GeneralLinear (m + 1) F.Carrier ⧸
          Subgroup.center (Langlands.GeneralLinear (m + 1) F.Carrier))]
        [BorelSpace (Langlands.GeneralLinear (m + 1) F.Carrier ⧸
          Subgroup.center (Langlands.GeneralLinear (m + 1) F.Carrier))]
        (μ : Measure (Langlands.GeneralLinear (m + 1) F.Carrier ⧸
          Subgroup.center (Langlands.GeneralLinear (m + 1) F.Carrier)))
        [μ.IsHaarMeasure],
        MemLp (c.coefficientNorm L v) 2 μ →
        Summable (fun lam : {lam : Fin m → ℤ //
            Antitone (Fin.snoc lam 0 : Fin (m + 1) → ℤ)} =>
          (∏ i : Fin (m + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (m + 1) => i < j),
            T.normalizedAbs ((ϖ ^ (Fin.snoc lam.1 0 : Fin (m + 1) → ℤ) i /
              ϖ ^ (Fin.snoc lam.1 0 : Fin (m + 1) → ℤ) j : F.Carrierˣ) : F.Carrier))⁻¹ *
            ‖L (π (Iwasawa.torus ϖ (Fin.snoc lam.1 0)) v)‖ ^ 2) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ϖ hϖ V _ _ π c L v hL hv _ _ μ _ hf
  have := T.generalLinearTopologicalGroup (m + 1)
  have hϖ1 : ValuativeRel.valuation F.Carrier (ϖ : F.Carrier) ≤ 1 := hϖ.1.le
  let S := {lam : Fin m → ℤ // Antitone (Fin.snoc lam 0 : Fin (m + 1) → ℤ)}
  let ex : S → Fin (m + 1) → ℤ := fun lam => Fin.snoc lam.1 0
  let A : S → Fin (m + 1) → F.Carrierˣ := fun lam i => ϖ ^ ex lam i
  let NK := unipotentLevel F.Carrier m r
  let H : S → Subgroup (upperUnipotent (m + 1) F.Carrier) := fun lam => conjLevel m r (A lam)
  have hidx := fun lam : S => index_conjLevel F T m r ϖ (ex lam) hϖ1 lam.2
  have : ∀ lam : S, Finite (H lam ⧸ NK.subgroupOf (H lam)) := fun lam => by
    have := (hidx lam).1
    exact Subgroup.finite_quotient_of_finiteIndex
  have : ∀ lam : S, Countable (H lam ⧸ NK.subgroupOf (H lam)) := fun lam =>
    Finite.to_countable
  let I := Σ lam : S, H lam ⧸ NK.subgroupOf (H lam)
  let g : I → Langlands.GeneralLinear (m + 1) F.Carrier := fun i =>
    Iwasawa.torus ϖ (ex i.1) * i.2.out.val.val
  let K := Conductor.principalLevelOpenSubgroup F.Carrier m r
  let Z := Subgroup.center (Langlands.GeneralLinear (m + 1) F.Carrier)
  let K' : Set (Langlands.GeneralLinear (m + 1) F.Carrier ⧸ Z) :=
    (↑) '' (K : Set (Langlands.GeneralLinear (m + 1) F.Carrier))
  let s : I → Set (Langlands.GeneralLinear (m + 1) F.Carrier ⧸ Z) := fun i =>
    (fun q => (g i : Langlands.GeneralLinear (m + 1) F.Carrier ⧸ Z) * q) '' K'
  have hopen0 : IsOpen K' :=
    QuotientGroup.isOpenMap_coe (N := Z) (K : Set (Langlands.GeneralLinear (m + 1) F.Carrier))
      K.isOpen
  have hopen : ∀ i, IsOpen (s i) := fun i => isOpenMap_mul_left _ _ hopen0
  have hmeas : ∀ i, μ (s i) = μ K' := by
    intro i
    simp only [s, Set.image_mul_left]
    exact measure_preimage_mul μ _ _
  have hdisj : Pairwise fun i i' => Disjoint (s i) (s i') := by
    rintro ⟨lam, q⟩ ⟨lam', q'⟩ hne
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨k₁, hk₁, rfl⟩, rfl⟩ ⟨_, ⟨k₂, hk₂, rfl⟩, he⟩
    apply hne
    have heq : ((g ⟨lam, q⟩ * k₁ : Langlands.GeneralLinear (m + 1) F.Carrier) :
        Langlands.GeneralLinear (m + 1) F.Carrier ⧸ Z) =
        ((g ⟨lam', q'⟩ * k₂ : Langlands.GeneralLinear (m + 1) F.Carrier) :
          Langlands.GeneralLinear (m + 1) F.Carrier ⧸ Z) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact he.symm
    rw [QuotientGroup.eq] at heq
    obtain ⟨hlam, hu⟩ := eq_of_mem_center hr hϖ
      (by simp only [ex, Fin.snoc_last]) q.out.val.property q'.out.val.property hk₁ hk₂ heq
    have hl : lam = lam' := by
      apply Subtype.ext
      funext i
      simpa only [ex, Fin.snoc_castSucc] using congrFun hlam i.castSucc
    subst hl
    have hq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      exact hu
    rw [hq]
  have hlow : ∀ i, ∀ y ∈ s i,
      ‖L (π (Iwasawa.torus ϖ (ex i.1)) v)‖ₑ ≤ ‖c.coefficientNorm L v y‖ₑ := by
    rintro ⟨lam, q⟩ _ ⟨_, ⟨k₁, hk₁, rfl⟩, rfl⟩
    have hu : Iwasawa.torus ϖ (ex lam) * q.out.val.val * (Iwasawa.torus ϖ (ex lam))⁻¹ ∈
        Conductor.principalLevelSubgroup F.Carrier m r :=
      mem_conjLevel.mp q.out.property
    beta_reduce
    rw [← QuotientGroup.mk_mul, UnitaryCentralCharacter.coefficientNorm_mk, enorm_norm]
    apply le_of_eq
    congr 1
    symm
    change L (π (Iwasawa.torus ϖ (ex lam) * q.out.val.val * k₁) v) = _
    rw [show Iwasawa.torus ϖ (ex lam) * q.out.val.val * k₁ =
        (Iwasawa.torus ϖ (ex lam) * q.out.val.val * (Iwasawa.torus ϖ (ex lam))⁻¹) *
          (Iwasawa.torus ϖ (ex lam) * k₁) by group,
      map_mul, Module.End.mul_apply, hL _ hu, map_mul, Module.End.mul_apply, hv _ hk₁]
  have hfin := countableCellLpLower _ I μ (c.coefficientNorm L v) 2 two_ne_zero
    ENNReal.ofNat_ne_top hf s (fun i => (hopen i).measurableSet) hdisj
    (fun i => ‖L (π (Iwasawa.torus ϖ (ex i.1)) v)‖ₑ) hlow
  rw [ENNReal.tsum_sigma'] at hfin
  simp only [hmeas] at hfin
  let δ : S → ℝ≥0 := fun lam =>
    (T.leviModulus (singletons (m + 1)) (singletonLevi F.Carrier (A lam)) : ℝ≥0)
  let b : S → ℝ≥0 := fun lam => ‖L (π (Iwasawa.torus ϖ (ex lam)) v)‖₊
  have hinner : ∀ lam : S,
      ∑' _ : H lam ⧸ NK.subgroupOf (H lam),
        ‖L (π (Iwasawa.torus ϖ (ex lam)) v)‖ₑ ^ (2 : ℝ≥0∞).toReal * μ K' =
      (((δ lam)⁻¹ * b lam ^ 2 : ℝ≥0) : ℝ≥0∞) * μ K' := by
    intro lam
    rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe, ← mul_assoc]
    congr 1
    have h2 : (Nat.card (H lam ⧸ NK.subgroupOf (H lam)) : ℝ≥0∞) =
        (((δ lam)⁻¹ : ℝ≥0) : ℝ≥0∞) := (hidx lam).2
    rw [h2, ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm, ENNReal.coe_mul,
      ENNReal.coe_pow]
  rw [tsum_congr hinner, ENNReal.tsum_mul_right] at hfin
  have hK'0 : μ K' ≠ 0 :=
    (hopen0.measure_pos μ ⟨_, ⟨1, K.one_mem, rfl⟩⟩).ne'
  have hfin2 := ENNReal.lt_top_of_mul_ne_top_left hfin.ne hK'0
  have hsum := ENNReal.tsum_coe_ne_top_iff_summable.mp hfin2.ne
  refine (NNReal.summable_coe.mpr hsum).congr fun lam => ?_
  rw [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm,
    singleton_modulus_real F T (A lam)]

end Cells

end Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum
