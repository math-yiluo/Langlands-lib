import Langlands.Representation.Whittaker.SupercuspidalCoinvariantFinitenessProof
import Langlands.AllField.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.AllField.Representation.Derivative.MirabolicMinus
import Langlands.AllField.Representation.Whittaker.SupercuspidalCoinvariantFinitenessStatement
/-!
# Finite twisted upper-unipotent coinvariants of irreducible supercuspidal representations

Proof of `Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessStatement`. Degenerate
characters give zero coinvariants. For a nondegenerate character the quotient is spanned by
the classes of finitely many torus translates of a finite-dimensional space of fixed vectors:
nondegeneracy kills translates by torus elements that expand a simple root too much, and the
vanishing of the Jacquet quotients kills those that contract one too much.
-/

noncomputable section

namespace Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof
open Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof hiding conj_mem_principalLevelSubgroup continuous_adjacentUnit exists_zpow_mul_mem finite_of_nondegenerate isTopologicalRing isUniformizingElement uniformizerUnit uniformizerUnit_zpow_val uniformizer_ne_zero
open Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof
open Langlands.Whittaker hiding SupercuspidalCoinvariantFinitenessStatement supercuspidalCoinvariantFiniteness
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.Whittaker.UpperUnipotentCharacter
open Langlands.Whittaker.UpperUnipotentCoinvariant
open Langlands.Classification.SupercuspidalDerivativeVanishing (IsBlockUnipotent mem_upperUnipotent_of_isBlockUnipotent)

universe uF uV

/-! ## Diagonal conjugation of elementary and block matrices -/

section Algebra

variable {K : Type uF} [Field K]

end Algebra

/-! ## Coinvariant classes of torus translates -/

section Representation

variable {K : Type uF} [Field K] {V : Type uV} [AddCommGroup V] [Module ℂ V] {n : ℕ}
variable (ρ : Representation ℂ (GeneralLinear (n + 1) K) V)
  (η : upperUnipotent (n + 1) K →* ℂˣ)

end Representation

/-! ## The local field -/

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

theorem uniformizer_ne_zero : T.uniformizer ≠ 0 := by
  apply T.discreteValuation.ne_zero_iff.mp
  rw [T.discreteValuation_uniformizer]
  exact WithZero.exp_ne_zero

/-- The chosen uniformizer as a unit. -/
def uniformizerUnit : Fˣ := Units.mk0 T.uniformizer (uniformizer_ne_zero T)

/-- The chosen uniformizer is a uniformizing element for the actual valuation. -/
theorem isUniformizingElement :
    letI := T.topology
    letI := T.valuativeRel
    Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) (uniformizerUnit T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hex : e (ValuativeRel.valuation F T.uniformizer) = WithZero.exp (-1) :=
    T.discreteValuation_uniformizer
  refine ⟨?_, fun y hy => ?_⟩
  · change ValuativeRel.valuation F T.uniformizer < 1
    rw [← e.strictMono.lt_iff_lt, hex, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · have hy0 : e (ValuativeRel.valuation F y) ≠ 0 := by
      simpa using hy
    refine ⟨-WithZero.log (e (ValuativeRel.valuation F y)), ?_⟩
    apply e.injective
    change e (ValuativeRel.valuation F y) =
      e (ValuativeRel.valuation F T.uniformizer ^
        (-WithZero.log (e (ValuativeRel.valuation F y))))
    rw [map_zpow₀, hex, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
      WithZero.exp_log hy0]

theorem uniformizerUnit_zpow_val (e : ℤ) :
    ((uniformizerUnit T ^ e : Fˣ) : F) = T.uniformizer ^ e := by
  rw [Units.val_zpow_eq_zpow_val]
  rfl

/-- Large powers of the uniformizer move any element into any lattice. -/
theorem exists_zpow_mul_mem (c : F) (s : ℤ) :
    ∃ D : ℤ, ∀ e : ℤ, D ≤ e →
      ((uniformizerUnit T ^ e : Fˣ) : F) * c ∈ T.additiveLattice s := by
  refine ⟨WithZero.log (T.discreteValuation c) - s, fun e he => ?_⟩
  have hπe : T.uniformizer ^ e ≠ 0 := zpow_ne_zero e (uniformizer_ne_zero T)
  rw [uniformizerUnit_zpow_val, T.mul_mem_additiveLattice_iff hπe, T.ord_zpow,
    T.ord_uniformizer, mul_one]
  rw [Langlands.LocalFieldData.mem_additiveLattice]
  apply WithZero.le_exp_of_log_le
  omega

theorem isTopologicalRing : letI := T.topology; IsTopologicalRing F := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  infer_instance

theorem continuous_adjacentUnit {n : ℕ} (i : Fin n) :
    letI := T.topology
    Continuous (fun x : F => adjacentUnit i x) := by
  let := T.topology
  have := isTopologicalRing T
  have hm : ∀ s : F → F, Continuous s →
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
    {k h : GeneralLinear (n + 1) F}
    (hk : letI := T.valuativeRel
      k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer n)
    (hh : letI := T.valuativeRel; h ∈ Conductor.principalLevelSubgroup F n a) :
    letI := T.valuativeRel
    k⁻¹ * h * k ∈ Conductor.principalLevelSubgroup F n a := by
  let := T.valuativeRel
  obtain ⟨g0, rfl⟩ := hk
  obtain ⟨h0, hh0, rfl⟩ := hh
  refine ⟨g0⁻¹ * h0 * g0, ?_, by simp [map_mul, map_inv]⟩
  have hn := (MonoidHom.normal_ker (Matrix.GeneralLinearGroup.map (n := Fin (n + 1))
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation F).integer ^ a)))).conj_mem h0 hh0 g0⁻¹
  rw [inv_inv] at hn
  exact hn

end Padic

/-! ## Nondegenerate characters -/

/-- For a nondegenerate character, the twisted coinvariants of an irreducible supercuspidal
representation of `GL_(n+1)` are finite dimensional. -/
theorem finite_of_nondegenerate (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F),
      σ.IsIrreducible → GeneralLinear.IsSupercuspidal σ.representation →
      ∀ η : upperUnipotent (n + 1) F →* ℂˣ,
        IsLocallyConstant (fun u => (η u : ℂ)) →
        (∀ i : Fin n, ∃ y : F, η (adjacentUnit i y) ≠ 1) →
        FiniteDimensional ℂ
          (Jacquet.Localization.Coinvariants σ.representation
            (upperUnipotent (n + 1) F) η) := by
  let _ := T.topology
  let _ := T.valuativeRel
  have _ := T.localField
  have _ := isTopologicalRing T
  intro σ hirr hsc η hη hnd
  set ρ := σ.representation with hρ
  set Q := Jacquet.Localization.mk ρ (upperUnipotent (n + 1) F) η with hQ
  -- The trivial carrier.
  by_cases hV : Subsingleton σ
  · have : Subsingleton (Jacquet.Localization.Coinvariants ρ
        (upperUnipotent (n + 1) F) η) :=
      ⟨fun x y => by
        obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ρ _ η x
        obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective ρ _ η y
        rw [Subsingleton.elim v w]⟩
    infer_instance
  rw [not_subsingleton_iff_nontrivial] at hV
  obtain ⟨v0, hv0⟩ := exists_ne (0 : σ)
  -- A principal congruence subgroup fixing `v0`, and its finite-dimensional fixed space.
  obtain ⟨K0, hK0⟩ := hsc.1.1 v0
  obtain ⟨a, -, hKa⟩ := Conductor.exists_pos_principalLevelOpenSubgroup_subset F n
    K0.mem_nhds_one
  let Ka := Conductor.principalLevelOpenSubgroup F n a
  let V'' := fixedVectors ρ Ka.toSubgroup
  have hfin : Module.Finite ℂ V'' := hsc.1.2 Ka
  have mem_V'' : ∀ w : σ, w ∈ V'' ↔ ∀ h : GeneralLinear (n + 1) F, h ∈ Ka →
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
  have hint : ∀ k : GeneralLinear (n + 1) F,
      k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer n →
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
  have hcentral : ∀ c : Fˣ, ∀ w ∈ V'',
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
  let t : (Fin (n + 1) → ℤ) → GeneralLinear (n + 1) F :=
    fun lam => diagonalUnit (fun j => ϖ ^ lam j)
  have ht_entry : ∀ (lam : Fin (n + 1) → ℤ) (i : Fin n) (x : F),
      ((ϖ ^ lam i.castSucc : Fˣ) : F) * x *
          ((((ϖ ^ lam i.succ)⁻¹ : Fˣ)) : F) =
        ((ϖ ^ (lam i.castSucc - lam i.succ) : Fˣ) : F) * x := by
    intro lam i x
    rw [zpow_sub, Units.val_mul]
    ring
  -- Lower bounds from nondegeneracy.
  have hlower : ∀ i : Fin n, ∃ lo : ℤ, ∀ lam : Fin (n + 1) → ℤ,
      lam i.castSucc - lam i.succ ≤ lo → ∀ w ∈ V'', Q (ρ (t lam) w) = 0 := by
    intro i
    obtain ⟨y, hy⟩ := hnd i
    have hopen : IsOpen {x : F | (adjacentUnit i x).val ∈ Ka} :=
      Ka.isOpen.preimage (continuous_subtype_val.comp (continuous_adjacentUnit T i))
    have h0 : (0 : F) ∈ {x : F | (adjacentUnit i x).val ∈ Ka} := by
      change (adjacentUnit i (0 : F)).val ∈ Ka
      rw [adjacentUnit_zero]
      exact Ka.one_mem
    obtain ⟨s, hs⟩ := T.exists_additiveLattice_subset (hopen.mem_nhds h0)
    obtain ⟨D, hD⟩ := exists_zpow_mul_mem T y s
    refine ⟨-D, fun lam hlam w hw => ?_⟩
    set dd := lam i.castSucc - lam i.succ with hdd
    let x : F := ((ϖ ^ (-dd) : Fˣ) : F) * y
    have hx : (adjacentUnit i x).val ∈ Ka := hs (hD (-dd) (by omega))
    apply mk_diagonal_eq_zero_of_adjacent ρ η _ w i x ((mem_V'' w).mp hw _ hx)
    show η (adjacentUnit i (((ϖ ^ lam i.castSucc : Fˣ) : F) * x *
      ((((ϖ ^ lam i.succ)⁻¹ : Fˣ)) : F))) ≠ 1
    rw [ht_entry, ← hdd]
    have hxy : ((ϖ ^ dd : Fˣ) : F) * x = y := by
      change ((ϖ ^ dd : Fˣ) : F) *
        (((ϖ ^ (-dd) : Fˣ) : F) * y) = y
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
    have hJ := hsc.2 B (cutShape_parabolic_ne_top (F := F) (n + 1) (k.val + 1)
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
    have hloc : IsLocallyConstant (fun x : F => (η (adjacentUnit k x) : ℂ)) :=
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
        have hu' : u ∈ B.unipotentSubgroup F := by
          obtain ⟨u', hu', rfl⟩ := hu
          simpa using hu'
        have hb := isBlockUnipotent_of_mem_cutShape (Nat.succ_pos _) hk1 hu'
        have hU := mem_upperUnipotent_of_isBlockUnipotent hb
        obtain ⟨D, hD⟩ := exists_zpow_mul_mem T (u.val k.castSucc k.succ) s
        refine ⟨D, (mem_Z D _).mpr fun lam hlam => ?_⟩
        apply mk_diagonal_sub_eq_zero ρ η _ k ⟨u, hU⟩ hb x'
        show η (adjacentUnit k (((ϖ ^ lam k.castSucc : Fˣ) : F) *
          u.val k.castSucc k.succ * ((((ϖ ^ lam k.succ)⁻¹ : Fˣ)) : F))) = 1
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
  let S : Set (Jacquet.Localization.Coinvariants ρ (upperUnipotent (n + 1) F) η) :=
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
open Langlands.Whittaker hiding SupercuspidalCoinvariantFinitenessStatement supercuspidalCoinvariantFiniteness
open Langlands.AllField.Whittaker

universe uF uV

/-- The finite-dimensionality part of BZ76 §5.18 for the actual twisted upper-unipotent
coinvariants of an irreducible supercuspidal representation, for every locally constant
character. -/
theorem supercuspidalCoinvariantFiniteness :
    SupercuspidalCoinvariantFinitenessStatement.{uF, uV} := by
  intro F _ T m hm
  let _ := T.topology
  intro σ hirr hsc η hη
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  by_cases hdeg : ∃ i : Fin n, ∀ x : F, η (UpperUnipotentCharacter.adjacentUnit i x) = 1
  · obtain ⟨i, hi⟩ := hdeg
    have := UpperUnipotentCoinvariant.subsingleton_coinvariants_of_adjacentUnit
      σ.representation hsc η i hi
    infer_instance
  · push Not at hdeg
    exact Langlands.AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.finite_of_nondegenerate F T n σ hirr hsc η hη
      hdeg

end Langlands.AllField.Whittaker
