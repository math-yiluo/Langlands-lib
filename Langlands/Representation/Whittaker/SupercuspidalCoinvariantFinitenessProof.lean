import Langlands.Representation.OrbitSpan
import Langlands.Representation.Whittaker.SupercuspidalCoinvariantFinitenessStatement
import Langlands.Representation.Whittaker.UpperUnipotentCoinvariantReduction
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Int.Interval

/-!
# Finite twisted upper-unipotent coinvariants of irreducible supercuspidal representations

Proof of `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`. Degenerate
characters give zero coinvariants. For a nondegenerate character the quotient is spanned by
the classes of finitely many torus translates of a finite-dimensional space of fixed vectors:
nondegeneracy kills translates by torus elements that expand a simple root too much, and the
vanishing of the Jacquet quotients kills those that contract one too much.
-/

noncomputable section

namespace Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof

open GeneralLinear UpperUnipotentCharacter UpperUnipotentCoinvariant
open Classification.SupercuspidalDerivativeVanishing (IsBlockUnipotent
  mem_upperUnipotent_of_isBlockUnipotent)

universe uF uV

/-! ## Diagonal conjugation of elementary and block matrices -/

section Algebra

variable {K : Type uF} [Field K]

/-- Conjugating `1 + x E_(i,i+1)` by `diag(d)` gives `1 + d_i x d_(i+1)⁻¹ E_(i,i+1)`. -/
theorem diagonalConj_adjacentUnit {n : ℕ} (d : Fin (n + 1) → Kˣ) (i : Fin n) (x : K) :
    diagonalConj d (adjacentUnit i x) =
      adjacentUnit i ((d i.castSucc : K) * x * (((d i.succ)⁻¹ : Kˣ) : K)) := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  rw [diagonalConj_val, diagonalUnit_conj_apply]
  change (d a : K) * Matrix.transvection i.castSucc i.succ x a b * _ =
    Matrix.transvection i.castSucc i.succ _ a b
  rw [transvection_apply, transvection_apply]
  by_cases hab : a = b
  · subst hab
    have h2 : ¬ (i.castSucc = a ∧ i.succ = a) := fun h =>
      (ne_of_lt Fin.castSucc_lt_succ) (h.1.trans h.2.symm)
    simp [h2]
  · by_cases h : i.castSucc = a ∧ i.succ = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab]
    · simp [hab, h]

/-- On a block unipotent matrix with cut `k + 1`, a character of the diagonal conjugate only
sees the conjugated entry `(k, k+1)`. -/
theorem character_diagonalConj_of_isBlockUnipotent {M : Type*} [CommGroup M] {n : ℕ}
    (η : upperUnipotent (n + 1) K →* M) (d : Fin (n + 1) → Kˣ) (k : Fin n)
    (u : upperUnipotent (n + 1) K) (hu : IsBlockUnipotent (k.val + 1) u.val) :
    η (diagonalConj d u) = η (adjacentUnit k
      ((d k.castSucc : K) * u.val.val k.castSucc k.succ * (((d k.succ)⁻¹ : Kˣ) : K))) := by
  rw [eq_prod_adjacentUnit n η (diagonalConj d u), Finset.prod_eq_single k]
  · rw [diagonalConj_val, diagonalUnit_conj_apply]
  · intro j _ hjk
    rw [diagonalConj_val, diagonalUnit_conj_apply,
      isBlockUnipotent_adjacent_eq_zero hu j (fun h => hjk (Fin.ext h)), mul_zero, zero_mul,
      adjacentUnit_zero, map_one]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The diagonal matrix of a product is the product of the diagonal matrices. -/
theorem diagonalUnit_mul {m : ℕ} (d e : Fin m → Kˣ) :
    diagonalUnit (d * e) = diagonalUnit d * diagonalUnit e := by
  apply Units.ext
  change Matrix.diagonal (fun i => ((d i * e i : Kˣ) : K)) =
    Matrix.diagonal (fun i => (d i : K)) * Matrix.diagonal (fun i => (e i : K))
  rw [Matrix.diagonal_mul_diagonal]
  simp

/-- A constant diagonal matrix is central. -/
theorem diagonalUnit_const_commute {m : ℕ} (c : Kˣ) (g : GeneralLinear m K) :
    diagonalUnit (fun _ : Fin m => c) * g = g * diagonalUnit (fun _ : Fin m => c) := by
  apply Units.ext
  change Matrix.diagonal (fun _ => (c : K)) * g.val = g.val * Matrix.diagonal (fun _ => (c : K))
  rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

end Algebra

/-! ## Coinvariant classes of torus translates -/

section Representation

variable {K : Type uF} [Field K] {V : Type uV} [AddCommGroup V] [Module ℂ V] {n : ℕ}
variable (ρ : Representation ℂ (GeneralLinear (n + 1) K) V)
  (η : upperUnipotent (n + 1) K →* ℂˣ)

/-- Moving an upper unipotent element across a diagonal translate. -/
theorem mk_diagonal_apply (d : Fin (n + 1) → Kˣ) (u : upperUnipotent (n + 1) K) (w : V) :
    Jacquet.Localization.mk ρ (upperUnipotent (n + 1) K) η
        (ρ (diagonalUnit d) (ρ u.val w)) =
      (η (diagonalConj d u) : ℂ) •
        Jacquet.Localization.mk ρ (upperUnipotent (n + 1) K) η (ρ (diagonalUnit d) w) := by
  have h : ρ (diagonalUnit d) (ρ u.val w) =
      ρ (diagonalConj d u).val (ρ (diagonalUnit d) w) := by
    rw [diagonalConj_val, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel_right]
  rw [h]
  exact Jacquet.Localization.mk_apply_subgroup ρ _ η _ _

/-- A translate of a vector fixed by `1 + x E_(i,i+1)` has zero class when the conjugated
elementary matrix has a nontrivial character value. -/
theorem mk_diagonal_eq_zero_of_adjacent (d : Fin (n + 1) → Kˣ) (w : V) (i : Fin n) (x : K)
    (hw : ρ (adjacentUnit i x).val w = w)
    (hne : η (adjacentUnit i ((d i.castSucc : K) * x * (((d i.succ)⁻¹ : Kˣ) : K))) ≠ 1) :
    Jacquet.Localization.mk ρ (upperUnipotent (n + 1) K) η (ρ (diagonalUnit d) w) = 0 := by
  have h := mk_diagonal_apply ρ η d (adjacentUnit i x) w
  rw [hw, diagonalConj_adjacentUnit] at h
  have hc : ((η (adjacentUnit i ((d i.castSucc : K) * x * (((d i.succ)⁻¹ : Kˣ) : K))) : ℂ)
      - 1) • Jacquet.Localization.mk ρ (upperUnipotent (n + 1) K) η
        (ρ (diagonalUnit d) w) = 0 := by
    rw [sub_smul, ← h, one_smul, sub_self]
  rcases smul_eq_zero.mp hc with h0 | h0
  · exact absurd (Units.val_eq_one.mp (sub_eq_zero.mp h0)) hne
  · exact h0

/-- A translate of a Jacquet relation `ρ(u)x - x` for a block unipotent `u` has zero class
when the conjugated cut entry has trivial character value. -/
theorem mk_diagonal_sub_eq_zero (d : Fin (n + 1) → Kˣ) (k : Fin n)
    (u : upperUnipotent (n + 1) K) (hu : IsBlockUnipotent (k.val + 1) u.val) (x : V)
    (h1 : η (adjacentUnit k ((d k.castSucc : K) * u.val.val k.castSucc k.succ *
      (((d k.succ)⁻¹ : Kˣ) : K))) = 1) :
    Jacquet.Localization.mk ρ (upperUnipotent (n + 1) K) η
      (ρ (diagonalUnit d) (ρ u.val x - x)) = 0 := by
  rw [map_sub, map_sub, mk_diagonal_apply, character_diagonalConj_of_isBlockUnipotent η d k u hu,
    h1, Units.val_one, one_smul, sub_self]

end Representation

/-! ## The p-adic field -/

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem uniformizer_ne_zero : T.uniformizer ≠ 0 := by
  apply T.discreteValuation.ne_zero_iff.mp
  rw [T.discreteValuation_uniformizer]
  exact WithZero.exp_ne_zero

/-- The chosen uniformizer as a unit. -/
def uniformizerUnit : F.Carrierˣ := Units.mk0 T.uniformizer (uniformizer_ne_zero T)

/-- The chosen uniformizer is a uniformizing element for the actual valuation. -/
theorem isUniformizingElement :
    letI := T.topology
    letI := T.valuativeRel
    Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) (uniformizerUnit T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hex : e (ValuativeRel.valuation F.Carrier T.uniformizer) = WithZero.exp (-1) :=
    T.discreteValuation_uniformizer
  refine ⟨?_, fun y hy => ?_⟩
  · change ValuativeRel.valuation F.Carrier T.uniformizer < 1
    rw [← e.strictMono.lt_iff_lt, hex, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · have hy0 : e (ValuativeRel.valuation F.Carrier y) ≠ 0 := by
      simpa using hy
    refine ⟨-WithZero.log (e (ValuativeRel.valuation F.Carrier y)), ?_⟩
    apply e.injective
    change e (ValuativeRel.valuation F.Carrier y) =
      e (ValuativeRel.valuation F.Carrier T.uniformizer ^
        (-WithZero.log (e (ValuativeRel.valuation F.Carrier y))))
    rw [map_zpow₀, hex, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
      WithZero.exp_log hy0]

theorem uniformizerUnit_zpow_val (e : ℤ) :
    ((uniformizerUnit T ^ e : F.Carrierˣ) : F.Carrier) = T.uniformizer ^ e := by
  rw [Units.val_zpow_eq_zpow_val]
  rfl

/-- Large powers of the uniformizer move any element into any lattice. -/
theorem exists_zpow_mul_mem (c : F.Carrier) (s : ℤ) :
    ∃ D : ℤ, ∀ e : ℤ, D ≤ e →
      ((uniformizerUnit T ^ e : F.Carrierˣ) : F.Carrier) * c ∈ T.additiveLattice s := by
  refine ⟨WithZero.log (T.discreteValuation c) - s, fun e he => ?_⟩
  have hπe : T.uniformizer ^ e ≠ 0 := zpow_ne_zero e (uniformizer_ne_zero T)
  rw [uniformizerUnit_zpow_val, T.mul_mem_additiveLattice_iff hπe, T.ord_zpow,
    T.ord_uniformizer, mul_one]
  rw [PadicField.TopologicalData.mem_additiveLattice]
  apply WithZero.le_exp_of_log_le
  omega

theorem isTopologicalRing : letI := T.topology; IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  infer_instance

theorem continuous_adjacentUnit {n : ℕ} (i : Fin n) :
    letI := T.topology
    Continuous (fun x : F.Carrier => adjacentUnit i x) := by
  let := T.topology
  have := isTopologicalRing T
  have hm : ∀ s : F.Carrier → F.Carrier, Continuous s →
      Continuous fun t => Matrix.transvection i.castSucc i.succ (s t) := by
    intro s hs
    refine continuous_matrix fun r c => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : i.castSucc = r ∧ i.succ = c
    · simp only [h, and_self, ↓reduceIte]
      exact continuous_const.add hs
    · simp only [h, ↓reduceIte]
      exact continuous_const
  refine Continuous.subtype_mk ?_ _
  exact Units.continuous_iff.mpr ⟨hm id continuous_id, hm (fun t => -t) continuous_neg⟩

/-- A principal congruence subgroup is normalized by the integral group. -/
theorem conj_mem_principalLevelSubgroup (n a : ℕ)
    {k h : GeneralLinear (n + 1) F.Carrier}
    (hk : letI := T.valuativeRel
      k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n)
    (hh : letI := T.valuativeRel; h ∈ Conductor.principalLevelSubgroup F.Carrier n a) :
    letI := T.valuativeRel
    k⁻¹ * h * k ∈ Conductor.principalLevelSubgroup F.Carrier n a := by
  let := T.valuativeRel
  obtain ⟨g0, rfl⟩ := hk
  obtain ⟨h0, hh0, rfl⟩ := hh
  refine ⟨g0⁻¹ * h0 * g0, ?_, by simp [map_mul, map_inv]⟩
  have hn := (MonoidHom.normal_ker (Matrix.GeneralLinearGroup.map (n := Fin (n + 1))
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation F.Carrier).integer ^ a)))).conj_mem h0 hh0 g0⁻¹
  rw [inv_inv] at hn
  exact hn

end Padic

/-! ## Nondegenerate characters -/

/-- For a nondegenerate character, the twisted coinvariants of an irreducible supercuspidal
representation of `GL_(n+1)` are finite dimensional. -/
theorem finite_of_nondegenerate {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      σ.IsIrreducible → GeneralLinear.IsSupercuspidal σ.representation →
      ∀ η : upperUnipotent (n + 1) F.Carrier →* ℂˣ,
        IsLocallyConstant (fun u => (η u : ℂ)) →
        (∀ i : Fin n, ∃ y : F.Carrier, η (adjacentUnit i y) ≠ 1) →
        FiniteDimensional ℂ
          (Jacquet.Localization.Coinvariants σ.representation
            (upperUnipotent (n + 1) F.Carrier) η) := by
  let _ := T.topology
  let _ := T.valuativeRel
  have _ := T.localField
  have _ := isTopologicalRing T
  intro σ hirr hsc η hη hnd
  set ρ := σ.representation with hρ
  set Q := Jacquet.Localization.mk ρ (upperUnipotent (n + 1) F.Carrier) η with hQ
  -- The trivial carrier.
  by_cases hV : Subsingleton σ
  · have : Subsingleton (Jacquet.Localization.Coinvariants ρ
        (upperUnipotent (n + 1) F.Carrier) η) :=
      ⟨fun x y => by
        obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ρ _ η x
        obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective ρ _ η y
        rw [Subsingleton.elim v w]⟩
    infer_instance
  rw [not_subsingleton_iff_nontrivial] at hV
  obtain ⟨v0, hv0⟩ := exists_ne (0 : σ)
  -- A principal congruence subgroup fixing `v0`, and its finite-dimensional fixed space.
  obtain ⟨K0, hK0⟩ := hsc.1.1 v0
  obtain ⟨a, -, hKa⟩ := Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier n
    K0.mem_nhds_one
  let Ka := Conductor.principalLevelOpenSubgroup F.Carrier n a
  let V'' := fixedVectors ρ Ka.toSubgroup
  have hfin : Module.Finite ℂ V'' := hsc.1.2 Ka
  have mem_V'' : ∀ w : σ, w ∈ V'' ↔ ∀ h : GeneralLinear (n + 1) F.Carrier, h ∈ Ka →
      ρ h w = w := by
    intro w
    constructor
    · intro hw h hh
      exact (Representation.mem_invariants _ w).mp hw ⟨h, hh⟩
    · intro hw
      exact (Representation.mem_invariants _ w).mpr fun h => hw h.val h.property
  have hv0V : v0 ∈ V'' := by
    rw [mem_V'']
    intro h hh
    exact (Representation.mem_invariants _ v0).mp hK0 ⟨h, hKa hh⟩
  have hint : ∀ k : GeneralLinear (n + 1) F.Carrier,
      k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
      ∀ w ∈ V'', ρ k w ∈ V'' := by
    intro k hk w hw
    rw [mem_V''] at hw ⊢
    intro h hh
    have hc := hw _ (conj_mem_principalLevelSubgroup T n a hk hh)
    have hhk : h * k = k * (k⁻¹ * h * k) := by group
    calc ρ h (ρ k w) = ρ (h * k) w := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (k * (k⁻¹ * h * k)) w := by rw [hhk]
      _ = ρ k (ρ (k⁻¹ * h * k) w) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ k w := by rw [hc]
  have hcentral : ∀ c : F.Carrierˣ, ∀ w ∈ V'',
      ρ (diagonalUnit (fun _ : Fin (n + 1) => c)) w ∈ V'' := by
    intro c w hw
    rw [mem_V''] at hw ⊢
    intro h hh
    calc ρ h (ρ (diagonalUnit (fun _ : Fin (n + 1) => c)) w)
        = ρ (h * diagonalUnit (fun _ : Fin (n + 1) => c)) w := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (diagonalUnit (fun _ : Fin (n + 1) => c) * h) w := by
          rw [diagonalUnit_const_commute]
      _ = ρ (diagonalUnit (fun _ : Fin (n + 1) => c)) w := by
          rw [map_mul, Module.End.mul_apply, hw h hh]
  -- A finite spanning set of the fixed space.
  obtain ⟨s'', hs''⟩ := (Module.Finite.fg_top (R := ℂ) (M := V''))
  have hspan : ∀ w ∈ V'', w ∈ Submodule.span ℂ (V''.subtype '' (s'' : Set V'')) := by
    intro w hw
    have h1 : (⟨w, hw⟩ : V'') ∈ Submodule.span ℂ (s'' : Set V'') := by
      rw [hs'']
      trivial
    exact Submodule.apply_mem_span_image_of_mem_span V''.subtype h1
  -- The torus.
  let ϖ := uniformizerUnit T
  let t : (Fin (n + 1) → ℤ) → GeneralLinear (n + 1) F.Carrier :=
    fun lam => diagonalUnit (fun j => ϖ ^ lam j)
  have ht_entry : ∀ (lam : Fin (n + 1) → ℤ) (i : Fin n) (x : F.Carrier),
      ((ϖ ^ lam i.castSucc : F.Carrierˣ) : F.Carrier) * x *
          ((((ϖ ^ lam i.succ)⁻¹ : F.Carrierˣ)) : F.Carrier) =
        ((ϖ ^ (lam i.castSucc - lam i.succ) : F.Carrierˣ) : F.Carrier) * x := by
    intro lam i x
    rw [zpow_sub, Units.val_mul]
    ring
  -- Lower bounds from nondegeneracy.
  have hlower : ∀ i : Fin n, ∃ lo : ℤ, ∀ lam : Fin (n + 1) → ℤ,
      lam i.castSucc - lam i.succ ≤ lo → ∀ w ∈ V'', Q (ρ (t lam) w) = 0 := by
    intro i
    obtain ⟨y, hy⟩ := hnd i
    have hopen : IsOpen {x : F.Carrier | (adjacentUnit i x).val ∈ Ka} :=
      Ka.isOpen.preimage (continuous_subtype_val.comp (continuous_adjacentUnit T i))
    have h0 : (0 : F.Carrier) ∈ {x : F.Carrier | (adjacentUnit i x).val ∈ Ka} := by
      change (adjacentUnit i (0 : F.Carrier)).val ∈ Ka
      rw [adjacentUnit_zero]
      exact Ka.one_mem
    obtain ⟨s, hs⟩ := T.exists_additiveLattice_subset (hopen.mem_nhds h0)
    obtain ⟨D, hD⟩ := exists_zpow_mul_mem T y s
    refine ⟨-D, fun lam hlam w hw => ?_⟩
    set dd := lam i.castSucc - lam i.succ with hdd
    let x : F.Carrier := ((ϖ ^ (-dd) : F.Carrierˣ) : F.Carrier) * y
    have hx : (adjacentUnit i x).val ∈ Ka := hs (hD (-dd) (by omega))
    apply mk_diagonal_eq_zero_of_adjacent ρ η _ w i x ((mem_V'' w).mp hw _ hx)
    show η (adjacentUnit i (((ϖ ^ lam i.castSucc : F.Carrierˣ) : F.Carrier) * x *
      ((((ϖ ^ lam i.succ)⁻¹ : F.Carrierˣ)) : F.Carrier))) ≠ 1
    rw [ht_entry, ← hdd]
    have hxy : ((ϖ ^ dd : F.Carrierˣ) : F.Carrier) * x = y := by
      change ((ϖ ^ dd : F.Carrierˣ) : F.Carrier) *
        (((ϖ ^ (-dd) : F.Carrierˣ) : F.Carrier) * y) = y
      rw [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
        one_mul]
    rw [hxy]
    exact hy
  choose lo hlo using hlower
  -- Upper bounds from the vanishing of the Jacquet quotients.
  have hupper : ∀ k : Fin n, ∃ hi : ℤ, ∀ lam : Fin (n + 1) → ℤ,
      hi ≤ lam k.castSucc - lam k.succ → ∀ w ∈ V'', Q (ρ (t lam) w) = 0 := by
    intro k
    have hk1 : k.val + 1 < n + 1 := by omega
    let B := ProductLeviChamber.twoBlock (n + 1) (k.val + 1) (Nat.succ_pos _) hk1
    have hJ := hsc.2 B (cutShape_parabolic_ne_top (F := F.Carrier) (n + 1) (k.val + 1)
      (Nat.succ_pos _) hk1) 1
    let Z : ℤ → Submodule ℂ σ := fun D =>
      ⨅ (lam : Fin (n + 1) → ℤ) (_ : D ≤ lam k.castSucc - lam k.succ),
        LinearMap.ker (Q ∘ₗ ρ (t lam))
    have mem_Z : ∀ D w, w ∈ Z D ↔ ∀ lam : Fin (n + 1) → ℤ,
        D ≤ lam k.castSucc - lam k.succ → Q (ρ (t lam) w) = 0 := by
      intro D w
      simp only [Z, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp,
        Function.comp_apply]
    have Z_mono : Monotone Z := by
      intro D D' hDD' w hw
      rw [mem_Z] at hw ⊢
      exact fun lam hlam => hw lam (hDD'.trans hlam)
    have hloc : IsLocallyConstant (fun x : F.Carrier => (η (adjacentUnit k x) : ℂ)) :=
      hη.comp_continuous (continuous_adjacentUnit T k)
    obtain ⟨s, hs⟩ := T.exists_additiveLattice_subset
      ((hloc.isOpen_fiber 1).mem_nhds (by simp [adjacentUnit_zero]))
    have hall : ∀ w : σ, ∃ D, w ∈ Z D := by
      intro w
      have hw : w ∈ Jacquet.relations ρ (B.conjugateUnipotent 1) := by
        rw [← Jacquet.mk_eq_zero]
        exact Subsingleton.elim _ _
      rw [Jacquet.relations_eq_span] at hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨⟨u, hu⟩, x'⟩, rfl⟩ := hx
        have hu' : u ∈ B.unipotentSubgroup F.Carrier := by
          obtain ⟨u', hu', rfl⟩ := hu
          simpa using hu'
        have hb := isBlockUnipotent_of_mem_cutShape (Nat.succ_pos _) hk1 hu'
        have hU := mem_upperUnipotent_of_isBlockUnipotent hb
        obtain ⟨D, hD⟩ := exists_zpow_mul_mem T (u.val k.castSucc k.succ) s
        refine ⟨D, (mem_Z D _).mpr fun lam hlam => ?_⟩
        apply mk_diagonal_sub_eq_zero ρ η _ k ⟨u, hU⟩ hb x'
        show η (adjacentUnit k (((ϖ ^ lam k.castSucc : F.Carrierˣ) : F.Carrier) *
          u.val k.castSucc k.succ * ((((ϖ ^ lam k.succ)⁻¹ : F.Carrierˣ)) : F.Carrier))) = 1
        rw [ht_entry]
        exact Units.val_eq_one.mp (hs (hD _ hlam))
      | zero => exact ⟨0, (Z 0).zero_mem⟩
      | add x y _ _ hx hy =>
        obtain ⟨D, hD⟩ := hx
        obtain ⟨D', hD'⟩ := hy
        exact ⟨max D D', (Z _).add_mem (Z_mono (le_max_left _ _) hD)
          (Z_mono (le_max_right _ _) hD')⟩
      | smul c x _ hx =>
        obtain ⟨D, hD⟩ := hx
        exact ⟨D, (Z D).smul_mem c hD⟩
    choose D hD using hall
    obtain ⟨M, hM⟩ := Finset.exists_le (s''.image fun b : V'' => D b.val)
    refine ⟨M, fun lam hlam w hw => ?_⟩
    have hspanZ : Submodule.span ℂ (V''.subtype '' (s'' : Set V'')) ≤ Z M := by
      rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      exact Z_mono (hM _ (Finset.mem_image_of_mem _ hb)) (hD b.val)
    exact (mem_Z M w).mp (hspanZ (hspan w hw)) lam hlam
  choose hi hhi using hupper
  -- The finite set of normalized exponents in the box.
  let dmap : (Fin (n + 1) → ℤ) → (Fin n → ℤ) := fun lam i => lam i.castSucc - lam i.succ
  let Λ : Set (Fin (n + 1) → ℤ) := {lam | lam (Fin.last n) = 0 ∧
      ∀ i, lo i < dmap lam i ∧ dmap lam i < hi i}
  have hΛ : Λ.Finite := by
    apply Set.Finite.of_finite_image (f := dmap)
    · apply (Set.finite_Icc (fun i => lo i + 1) (fun i => hi i - 1)).subset
      rintro _ ⟨lam, ⟨-, hlam⟩, rfl⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := (hlam i).1
        show lo i + 1 ≤ dmap lam i
        omega
      · have := (hlam i).2
        show dmap lam i ≤ hi i - 1
        omega
    · intro lam hlam lam' hlam' heq
      funext j
      induction j using Fin.reverseInduction with
      | last => rw [hlam.1, hlam'.1]
      | cast i ih =>
        have := congrFun heq i
        simp only [dmap] at this
        omega
  let S : Set (Jacquet.Localization.Coinvariants ρ (upperUnipotent (n + 1) F.Carrier) η) :=
    ⋃ lam ∈ Λ, (Q ∘ₗ ρ (t lam)) '' (V''.subtype '' (s'' : Set V''))
  have hS : S.Finite := hΛ.biUnion fun lam _ => (s''.finite_toSet.image _).image _
  -- Every translate class of a fixed vector lies in the span of `S`.
  have htrans : ∀ lam : Fin (n + 1) → ℤ, ∀ w ∈ V'',
      Q (ρ (t lam) w) ∈ Submodule.span ℂ S := by
    intro lam w hw
    set c := lam (Fin.last n) with hc
    let lam' : Fin (n + 1) → ℤ := fun j => lam j - c
    have hsplit : t lam = t lam' * diagonalUnit (fun _ : Fin (n + 1) => ϖ ^ c) := by
      show diagonalUnit (fun j => ϖ ^ lam j) =
        diagonalUnit (fun j => ϖ ^ lam' j) * diagonalUnit (fun _ : Fin (n + 1) => ϖ ^ c)
      rw [← diagonalUnit_mul]
      congr 1
      funext j
      simp only [Pi.mul_apply, lam', ← zpow_add, sub_add_cancel]
    have hw' := hcentral (ϖ ^ c) w hw
    rw [hsplit, map_mul, Module.End.mul_apply]
    have hd : ∀ i, dmap lam' i = dmap lam i := fun i => by
      simp only [dmap, lam']
      omega
    by_cases hbox : ∀ i, lo i < dmap lam' i ∧ dmap lam' i < hi i
    · have hmem : lam' ∈ Λ := ⟨by simp [lam', c], hbox⟩
      have h1 := Submodule.apply_mem_span_image_of_mem_span (Q ∘ₗ ρ (t lam')) (hspan _ hw')
      exact Submodule.span_mono
        (Set.subset_biUnion_of_mem (u := fun l => (Q ∘ₗ ρ (t l)) '' (V''.subtype '' (s'' : Set V''))) hmem) h1
    · push Not at hbox
      obtain ⟨i, hi'⟩ := hbox
      by_cases hlt : lo i < dmap lam' i
      · rw [hhi i lam' (hi' hlt) _ hw']
        exact Submodule.zero_mem _
      · rw [hlo i lam' (by simp only [dmap] at hlt; omega) _ hw']
        exact Submodule.zero_mem _
  -- The classes of the orbit of `v0` span the quotient.
  have hmap : Submodule.map Q (Submodule.span ℂ (Set.range fun g => ρ g v0)) = ⊤ := by
    rw [span_range_orbit_eq_top hirr hv0, Submodule.map_top, LinearMap.range_eq_top]
    exact Jacquet.Localization.mk_surjective ρ _ η
  have htop : Submodule.span ℂ S = ⊤ := by
    rw [eq_top_iff, ← hmap, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    obtain ⟨u, hu, lam, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (isUniformizingElement T) g
    have htor : Iwasawa.torus ϖ lam = t lam := Units.ext rfl
    show Q (ρ (u * Iwasawa.torus ϖ lam * k) v0) ∈ (Submodule.span ℂ S : Set _)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, htor]
    have hQu : Q (ρ u (ρ (t lam) (ρ k v0))) =
        (η ⟨u, hu⟩ : ℂ) • Q (ρ (t lam) (ρ k v0)) :=
      Jacquet.Localization.mk_apply_subgroup ρ _ η ⟨u, hu⟩ _
    rw [SetLike.mem_coe, hQu]
    exact Submodule.smul_mem _ _ (htrans lam _ (hint k hk v0 hv0V))
  exact Module.finite_def.mpr (Submodule.fg_def.mpr ⟨S, hS, htop⟩)

end SupercuspidalCoinvariantFinitenessProof

universe uF uV

/-- The finite-dimensionality part of BZ76 §5.18 for the actual twisted upper-unipotent
coinvariants of an irreducible supercuspidal representation, for every locally constant
character. -/
theorem supercuspidalCoinvariantFiniteness :
    SupercuspidalCoinvariantFinitenessStatement.{uF, uV} := by
  intro p _ F T m hm
  let _ := T.topology
  intro σ hirr hsc η hη
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  by_cases hdeg : ∃ i : Fin n, ∀ x : F.Carrier, η (UpperUnipotentCharacter.adjacentUnit i x) = 1
  · obtain ⟨i, hi⟩ := hdeg
    have := UpperUnipotentCoinvariant.subsingleton_coinvariants_of_adjacentUnit
      σ.representation hsc η i hi
    infer_instance
  · push Not at hdeg
    exact SupercuspidalCoinvariantFinitenessProof.finite_of_nondegenerate F T n σ hirr hsc η hη
      hdeg

end Langlands.Whittaker
