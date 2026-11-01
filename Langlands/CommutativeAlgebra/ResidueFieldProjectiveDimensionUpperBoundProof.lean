import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Langlands.CommutativeAlgebra.MinimalFiniteFreeCover
import Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionUpperBoundStatement

/-! # Finite residue-field projective dimension is bounded by Krull dimension -/

universe u

namespace Langlands.CommutativeAlgebra

open CategoryTheory Abelian IsLocalRing

namespace ResidueFieldProjectiveDimensionUpperBound

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Every element of the maximal ideal acts by zero on `Ext κ X i`. -/
lemma smul_ext_eq_zero {a : R} (ha : a ∈ maximalIdeal R) {X : ModuleCat.{u} R} {i : ℕ}
    (e : Ext (ModuleCat.of R (ResidueField R)) X i) : a • e = 0 := by
  have h0 : a • 𝟙 (ModuleCat.of R (ResidueField R)) = 0 := by
    ext x
    simp [Algebra.smul_def, (residue_eq_zero_iff a).mpr ha]
  calc a • e = a • (Ext.mk₀ (𝟙 _)).comp e (zero_add i) := by rw [Ext.mk₀_id_comp]
    _ = (Ext.mk₀ (a • 𝟙 _)).comp e (zero_add i) := by rw [Ext.mk₀_smul, Ext.smul_comp]
    _ = 0 := by rw [h0, Ext.mk₀_zero, Ext.zero_comp]

/-- A morphism from a projective module whose image lies in `𝔪 • F` induces the zero map
on `Ext κ (-) i`. -/
lemma comp_mk₀_eq_zero_of_range_le [IsNoetherianRing R] {K F : ModuleCat.{u} R}
    [Module.Projective R K] (ι : K ⟶ F)
    (hι : LinearMap.range ι.hom ≤ maximalIdeal R • (⊤ : Submodule R F)) {i : ℕ}
    (e : Ext (ModuleCat.of R (ResidueField R)) K i) :
    e.comp (Ext.mk₀ ι) (add_zero i) = 0 := by
  classical
  obtain ⟨s, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (maximalIdeal R))
  have ha' : ∀ j, a j ∈ maximalIdeal R := fun j => ha ▸ Submodule.subset_span ⟨j, rfl⟩
  let σ : (Fin s → F) →ₗ[R] F := ∑ j, a j • LinearMap.proj j
  have hσ : maximalIdeal R • (⊤ : Submodule R F) ≤ LinearMap.range σ := by
    rw [Submodule.smul_le]
    intro r hr y _
    rw [← ha] at hr
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hr
    refine ⟨fun j => c j • y, ?_⟩
    simp [σ, Finset.sum_smul, mul_smul, smul_comm (a _) (c _)]
  obtain ⟨h, hh⟩ := Module.projective_lifting_property (LinearMap.rangeRestrict σ)
    ((ι.hom).codRestrict (LinearMap.range σ) (fun x => hσ (hι ⟨x, rfl⟩)))
    (LinearMap.surjective_rangeRestrict σ)
  have hι' : ι = ∑ j, a j • ModuleCat.ofHom (LinearMap.proj j ∘ₗ h) := by
    ext x
    have := congrArg (fun g => ((g x : LinearMap.range σ) : F)) hh
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply] at this
    rw [← this]
    simp [σ]
  rw [hι', Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Ext.mk₀_smul, Ext.comp_smul, smul_ext_eq_zero (ha' j)]

/-- A finite free module has vanishing `Ext κ (-) i` when `R` does. -/
lemma subsingleton_ext_of_free {F : ModuleCat.{u} R} [Module.Free R F] [Module.Finite R F]
    {i : ℕ} (h : Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) i)) :
    Subsingleton (Ext (ModuleCat.of R (ResidueField R)) F i) := by
  classical
  let b := Module.Free.chooseBasis R F
  have hid : 𝟙 F = ∑ β, ModuleCat.ofHom (b.coord β) ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b β)) := by
    ext x
    simp [b.sum_repr x]
  refine ⟨fun e₁ e₂ => ?_⟩
  suffices hz : ∀ e : Ext (ModuleCat.of R (ResidueField R)) F i, e = 0 by
    rw [hz e₁, hz e₂]
  intro e
  rw [← Ext.comp_mk₀_id e, hid, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero (fun β _ => ?_)
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    Subsingleton.elim (e.comp (Ext.mk₀ (ModuleCat.ofHom (b.coord β))) (add_zero i)) 0,
    Ext.zero_comp]

/-- A nonzero finite free module has `R` as a retract, so vanishing of its `Ext κ (-) i`
forces vanishing for `R`. -/
lemma subsingleton_ext_self_of_free {F : ModuleCat.{u} R} [Module.Free R F]
    [Nontrivial F] {i : ℕ} (h : Subsingleton (Ext (ModuleCat.of R (ResidueField R)) F i)) :
    Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) i) := by
  classical
  let b := Module.Free.chooseBasis R F
  obtain ⟨β⟩ := b.index_nonempty
  have hid : 𝟙 (ModuleCat.of R R) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b β)) ≫ ModuleCat.ofHom (b.coord β) := by
    ext
    simp
  refine ⟨fun e₁ e₂ => ?_⟩
  suffices hz : ∀ e : Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) i, e = 0 by
    rw [hz e₁, hz e₂]
  intro e
  rw [← Ext.comp_mk₀_id e, hid, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    Subsingleton.elim (e.comp (Ext.mk₀ (ModuleCat.ofHom
      (LinearMap.toSpanSingleton R F (b β)))) (add_zero i)) 0, Ext.zero_comp]

omit [IsLocalRing R] in
/-- In a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, if postcomposition with `X₁ → X₂`
kills `Ext X X₁ i` and `Ext X X₃ (i - 1)` vanishes (when `i ≥ 1`), then `Ext X X₁ i`
vanishes. -/
lemma subsingleton_ext_X₁ {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (X : ModuleCat.{u} R) (i : ℕ)
    (hf : ∀ x₁ : Ext X S.X₁ i, x₁.comp (Ext.mk₀ S.f) (add_zero i) = 0)
    (h₃ : ∀ j, j + 1 = i → Subsingleton (Ext X S.X₃ j)) :
    Subsingleton (Ext X S.X₁ i) := by
  refine ⟨fun e₁ e₂ => ?_⟩
  suffices hz : ∀ x : Ext X S.X₁ i, x = 0 by rw [hz e₁, hz e₂]
  intro x
  cases i with
  | zero =>
    have := hS.mono_f
    apply Ext.postcomp_mk₀_injective_of_mono X S.f
    simpa using hf x
  | succ j =>
    have := h₃ j rfl
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X hS x (hf x) rfl
    rw [← hx₃, Subsingleton.elim x₃ 0, Ext.zero_comp]

variable [IsNoetherianRing R]

/-- The Ext-only direction of Auslander–Buchsbaum used here: if `M` has projective dimension
exactly `h ≥ 1` and `Ext κ M i = 0` for `i < k`, then `Ext κ R i = 0` for `i < k + h`. -/
theorem ext_self_vanish_of_projectiveDimension (h : ℕ) (hh : 1 ≤ h) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLT M (h + 1) →
      ¬ HasProjectiveDimensionLT M h → ∀ k : ℕ,
      (∀ i < k, Subsingleton (Ext (ModuleCat.of R (ResidueField R)) M i)) →
      ∀ i < k + h, Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) i) := by
  induction h, hh using Nat.le_induction with
  | base =>
    intro M _ hM hM' k hk
    let C := minimalFiniteFreeCover R M
    let S := C.map.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer C.surjective
    have hproj : Projective S.X₁ := by
      rw [projective_iff_hasProjectiveDimensionLT_one]
      exact hS.hasProjectiveDimensionLT_X₁ 1 (by
        rw [← projective_iff_hasProjectiveDimensionLT_one]
        exact (IsProjective.iff_projective _).mp inferInstance) hM
    have : Module.Projective R S.X₁ := (IsProjective.iff_projective _).mpr hproj
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker C.map))
    have : Module.Free R S.X₁ := Module.free_of_flat_of_isLocalRing (R := R) (P := S.X₁)
    have hntr : Nontrivial S.X₁ := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      apply hM'
      have hinj : Function.Injective C.map := by
        rw [← LinearMap.ker_eq_bot]
        exact Submodule.eq_bot_of_subsingleton
      let e := LinearEquiv.ofBijective C.map ⟨hinj, C.surjective⟩
      have : Projective (ModuleCat.of R (Fin C.rank →₀ R)) :=
        (IsProjective.iff_projective _).mp inferInstance
      have : Projective M := Projective.of_iso e.toModuleIso this
      exact projective_iff_hasProjectiveDimensionLT_one.mp this
    have hzero : ∀ (j : ℕ) (x₁ : Ext (ModuleCat.of R (ResidueField R)) S.X₁ j),
        x₁.comp (Ext.mk₀ S.f) (add_zero j) = 0 := by
      intro j x₁
      apply comp_mk₀_eq_zero_of_range_le
      rintro _ ⟨x, rfl⟩
      exact C.minimal x.2
    have hK : ∀ i < k + 1, Subsingleton (Ext (ModuleCat.of R (ResidueField R)) S.X₁ i) := by
      intro i hi
      exact subsingleton_ext_X₁ hS _ i (hzero i) (fun j hj => hk j (by omega))
    intro i hi
    exact subsingleton_ext_self_of_free (F := S.X₁) (hK i hi)
  | succ h hh ih =>
    intro M _ hM hM' k hk
    obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    have hP : Projective S.X₂ := (IsProjective.iff_projective _).mp inferInstance
    have hN : HasProjectiveDimensionLT S.X₁ (h + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff h hP).mp hM
    have hN' : ¬ HasProjectiveDimensionLT S.X₁ h := by
      intro hcon
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      exact hM' ((hS.hasProjectiveDimensionLT_X₃_iff h' hP).mpr hcon)
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker f))
    have hNk : ∀ i < k + 1, Subsingleton (Ext (ModuleCat.of R (ResidueField R)) S.X₁ i) := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ihi =>
        intro hi
        have hR : Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) i) :=
          ih S.X₁ hN hN' i (fun j hj => ihi j hj (by omega)) i (by omega)
        have hF : Subsingleton (Ext (ModuleCat.of R (ResidueField R)) S.X₂ i) :=
          subsingleton_ext_of_free (F := S.X₂) hR
        exact subsingleton_ext_X₁ hS _ i (fun x₁ => Subsingleton.elim _ _)
          (fun j hj => hk j (by omega))
    intro i hi
    exact ih S.X₁ hN hN' (k + 1) hNk i (by omega)

end ResidueFieldProjectiveDimensionUpperBound

open ResidueFieldProjectiveDimensionUpperBound in
/-- **Stacks Project, Tag 00OB.** If the residue field of a Noetherian local ring has finite
projective dimension, then that projective dimension is at most the Krull dimension. -/
theorem residueFieldProjectiveDimensionUpperBound :
    ResidueFieldProjectiveDimensionUpperBoundStatement.{u} := by
  intro R _ _ _ hfin
  classical
  have : Module.Finite R (ResidueField R) :=
    Module.Finite.of_surjective (Algebra.linearMap R (ResidueField R)) residue_surjective
  let n := Nat.find hfin
  have hn : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n := Nat.find_spec hfin
  have hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) ≤ n :=
    (projectiveDimension_le_iff _ _).mpr hn
  refine hpd.trans ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0]
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial
  have hmin : ¬ HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) n := by
    have := Nat.find_min hfin (show n - 1 < n by omega)
    unfold HasProjectiveDimensionLE at this
    rwa [show n - 1 + 1 = n by omega] at this
  have hvan := ext_self_vanish_of_projectiveDimension n hpos
    (ModuleCat.of R (ResidueField R)) hn hmin 0 (by simp)
  have hsmul : (maximalIdeal R) • (⊤ : Submodule R R) = maximalIdeal R := by
    rw [smul_eq_mul, Ideal.mul_top]
  have hann : Module.annihilator R (ResidueField R) = maximalIdeal R := by
    ext a
    rw [Module.mem_annihilator]
    constructor
    · intro ha
      have := ha 1
      rwa [Algebra.smul_def, mul_one, ResidueField.algebraMap_eq, residue_eq_zero_iff] at this
    · intro ha x
      rw [Algebra.smul_def, ResidueField.algebraMap_eq, (residue_eq_zero_iff a).mpr ha, zero_mul]
  obtain ⟨rs, hlen, -, hreg⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext
    (maximalIdeal R) n (ModuleCat.of R R)
    (by
      change (maximalIdeal R) • (⊤ : Submodule R R) < ⊤
      rw [hsmul]
      exact lt_top_iff_ne_top.mpr (maximalIdeal.isMaximal R).ne_top)
    (ModuleCat.of R (ResidueField R))
    (by
      change Module.support R (ResidueField R) = _
      rw [Module.support_eq_zeroLocus, hann])
    (fun i hi => hvan i (by simpa using hi))
  have hreg' : RingTheory.Sequence.IsRegular R rs := hreg
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg'
  have hne : Ideal.ofList rs ≠ ⊤ := by
    intro htop
    apply hreg'.top_ne_smul
    rw [htop, smul_eq_mul, Ideal.mul_top]
  have : Nontrivial (R ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.mpr hne
  rw [← hdim, hlen]
  exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial

end Langlands.CommutativeAlgebra
