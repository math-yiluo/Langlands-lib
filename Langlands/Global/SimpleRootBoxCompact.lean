import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.GroupScheme.Rational.RelativeCentralDirectionsStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasis
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction

/-! # Compact simple-root boxes in the positive torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set Topology TensorProduct
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan

section RationalExtension

variable {M : Type*} [AddCommGroup M]

/-- The `ℚ`-linear extension of an additive map to `ℝ`, as an additive map on
`ℚ ⊗[ℤ] M`. -/
def ratExtend (ℓ : M →+ ℝ) : ℚ ⊗[ℤ] M →+ ℝ :=
  (TensorProduct.lift (LinearMap.mk₂ ℤ (fun (q : ℚ) (m : M) => (q : ℝ) * ℓ m)
    (fun q q' m => by push_cast; ring)
    (fun n q m => by simp only [zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast]; ring)
    (fun q m m' => by rw [map_add]; ring)
    (fun n q m => by simp only [map_zsmul, zsmul_eq_mul]; ring))).toAddMonoidHom

@[simp] theorem ratExtend_toRat (ℓ : M →+ ℝ) (m : M) : ratExtend ℓ (toRat m) = ℓ m := by
  simp [ratExtend]

/-- A character in the rational span of `S` is controlled by `S`: there is `C ≥ 0` such that
every additive map bounded by `B` on `S` is bounded by `C B` at `c`. -/
theorem exists_abs_le_of_toRat_mem_ratSpan {S : Set M} {c : M} (hc : toRat c ∈ ratSpan S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : M →+ ℝ) (B : ℝ), (∀ χ ∈ S, |ℓ χ| ≤ B) → |ℓ c| ≤ C * B := by
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hc
  refine ⟨∑ k, |(f k : ℝ)|, Finset.sum_nonneg fun k _ => abs_nonneg _, fun ℓ B hB => ?_⟩
  have hg : ∀ k, ∃ χ ∈ S, toRat χ = (g k : ℚ ⊗[ℤ] M) := fun k => (g k).2
  choose χ hχS hχ using hg
  have hℓ : ℓ c = ∑ k, (f k : ℝ) * ℓ (χ k) := by
    rw [← ratExtend_toRat ℓ c, ← hfg, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_rat_smul, ← hχ k, ratExtend_toRat, Rat.smul_def]
  rw [hℓ, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB _ (hχS k)) (abs_nonneg _)

end RationalExtension

section Units

/-- Bounded boxes in the positive reals, read in `ℝ≥0ˣ`, are compact. -/
theorem isCompact_unitsBox (a b : ℝ) (ha : 0 < a) :
    IsCompact {u : ℝ≥0ˣ | a ≤ ((u : ℝ≥0) : ℝ) ∧ ((u : ℝ≥0) : ℝ) ≤ b} := by
  let K : Set ℝ≥0 := {r | a ≤ (r : ℝ) ∧ (r : ℝ) ≤ b}
  have hKc : IsCompact K := by
    refine (isCompact_Icc (a := Real.toNNReal a) (b := Real.toNNReal (max a b))).of_isClosed_subset
      ?_ ?_
    · exact (isClosed_le continuous_const NNReal.continuous_coe).inter
        (isClosed_le NNReal.continuous_coe continuous_const)
    · intro r hr
      refine ⟨Real.toNNReal_le_iff_le_coe.mpr hr.1, ?_⟩
      rw [Real.le_toNNReal_iff_coe_le (le_trans ha.le (le_max_left a b))]
      exact hr.2.trans (le_max_right a b)
  have hK : K ⊆ Set.range (Units.val : ℝ≥0ˣ → ℝ≥0) := by
    intro r hr
    have hr0 : r ≠ 0 := by
      intro h
      have := hr.1
      rw [h, NNReal.coe_zero] at this
      linarith
    exact ⟨Units.mk0 r hr0, rfl⟩
  exact (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff hK).mpr hKc

end Units

variable (F : Type u) [Field F] [NumberField F] (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- The logarithm of the normalized norm of a character at a point, additive in the
character. -/
def logNormHom (x : Lie.AffinePoints T.toGrp (Adeles F)) : characterLattice T →+ ℝ where
  toFun χ := Real.log ((normCharacter F T χ x : ℝ≥0) : ℝ)
  map_zero' := by
    rw [normCharacter_apply, AdelicSiegelFactors.characterValue_zero', map_one, Units.val_one,
      NNReal.coe_one, Real.log_one]
  map_add' χ ψ := by
    rw [normCharacter_apply, normCharacter_apply, normCharacter_apply,
      AdelicSiegelFactors.characterValue_add', map_mul, Units.val_mul, NNReal.coe_mul,
      Real.log_mul]
    · exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))).ne'
    · exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))).ne'

theorem abs_log_le_of_mem_Icc {s v : ℝ≥0} (hv : v ≠ 0) (h1 : s⁻¹ ≤ v) (h2 : v ≤ s) :
    |Real.log (v : ℝ)| ≤ |Real.log (s : ℝ)| := by
  have hv0 : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs0 : 0 < (s : ℝ) := lt_of_lt_of_le hv0 (NNReal.coe_le_coe.mpr h2)
  have hup : Real.log v ≤ Real.log s := Real.log_le_log hv0 (NNReal.coe_le_coe.mpr h2)
  have hlow : Real.log ((s : ℝ)⁻¹) ≤ Real.log v := by
    refine Real.log_le_log (inv_pos.mpr hs0) ?_
    have := NNReal.coe_le_coe.mpr h1
    rwa [NNReal.coe_inv] at this
  rw [Real.log_inv] at hlow
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (s : ℝ)), neg_abs_le (Real.log (s : ℝ))]

/-- **Compact character boxes.** If the rational span of a set `S` of characters of a split
torus `T` is everything, every box `s⁻¹ ≤ |χ| ≤ s` (`χ ∈ S`) in the positive torus is
compact. -/
theorem isCompact_characterBox (hT : IsSplitTorus T.toGrp) {S : Set (characterLattice T)}
    (hS : ratSpan S = ⊤) (s : ℝ≥0) :
    IsCompact {x : intrinsicSubgroup F T | ∀ χ ∈ S,
      s⁻¹ ≤ (normCharacter F T χ x : ℝ≥0) ∧ (normCharacter F T χ x : ℝ≥0) ≤ s} := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ : Fintype I := Fintype.ofFinite I
  set box := {x : intrinsicSubgroup F T | ∀ χ ∈ S,
    s⁻¹ ≤ (normCharacter F T χ x : ℝ≥0) ∧ (normCharacter F T χ x : ℝ≥0) ≤ s}
  have hcoef : ∀ i : I, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : characterLattice T →+ ℝ) (B : ℝ),
      (∀ χ ∈ S, |ℓ χ| ≤ B) → |ℓ (coordinateCharacter F I T e i)| ≤ C * B := fun i =>
    exists_abs_le_of_toRat_mem_ratSpan (hS ▸ Submodule.mem_top)
  choose C hC0 hC using hcoef
  have hd : 0 < (Module.finrank ℚ F : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  let b : I → ℝ := fun i => C i * |Real.log (s : ℝ)| / Module.finrank ℚ F
  let R : Set (I → ℝ≥0ˣ) := Set.pi univ fun i =>
    {u | Real.exp (-b i) ≤ ((u : ℝ≥0) : ℝ) ∧ ((u : ℝ≥0) : ℝ) ≤ Real.exp (b i)}
  have hRc : IsCompact R := isCompact_univ_pi fun i => isCompact_unitsBox _ _ (Real.exp_pos _)
  have hΦc : Continuous (fullIntrinsic F T I e) :=
    (isClosedEmbedding_full F I T e).continuous.subtype_mk _
  have hboxc : IsClosed box := by
    have h : box = ⋂ χ ∈ S, ({x : intrinsicSubgroup F T |
        s⁻¹ ≤ (normCharacter F T χ x : ℝ≥0)} ∩ {x | (normCharacter F T χ x : ℝ≥0) ≤ s}) := by
      ext x
      simp [box]
    rw [h]
    refine isClosed_biInter fun χ _ => ?_
    have hf : Continuous fun x : intrinsicSubgroup F T => (normCharacter F T χ x : ℝ≥0) :=
      Units.continuous_val.comp ((normCharacter F T χ).continuous.comp continuous_subtype_val)
    exact (isClosed_le continuous_const hf).inter (isClosed_le hf continuous_const)
  have hcoord : ∀ (x : I → ℝ≥0ˣ) (i : I),
      positiveCharacter F I T e (coordinateCharacter F I T e i) x = x i := by
    intro x i
    have h := characterValue_full F I T e (coordinateCharacter F I T e i) x
    rw [characterValue_coordinateCharacter, coordinates_full] at h
    exact (PositiveRealIdeles.full_injective F h).symm
  have hpre : fullIntrinsic F T I e ⁻¹' box ⊆ R := by
    intro x hx i _
    let ℓ := logNormHom F T (full F I T e x)
    have hB : ∀ χ ∈ S, |ℓ χ| ≤ |Real.log (s : ℝ)| := fun χ hχ =>
      abs_log_le_of_mem_Icc (Units.ne_zero _) (hx χ hχ).1 (hx χ hχ).2
    have hbound := hC i ℓ _ hB
    have hℓ : ℓ (coordinateCharacter F I T e i) =
        (Module.finrank ℚ F : ℝ) * Real.log ((x i : ℝ≥0) : ℝ) := by
      change Real.log ((normCharacter F T (coordinateCharacter F I T e i)
        (full F I T e x) : ℝ≥0) : ℝ) = _
      rw [normCharacter_apply, absoluteValue_characterValue_full, hcoord, Units.val_pow_eq_pow_val,
        NNReal.coe_pow, Real.log_pow]
    rw [hℓ, abs_mul, abs_of_pos hd] at hbound
    have hlog : |Real.log ((x i : ℝ≥0) : ℝ)| ≤ b i := by
      rw [le_div_iff₀ hd]
      linarith
    have hx0 : 0 < ((x i : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    rw [abs_le] at hlog
    constructor
    · calc Real.exp (-b i) ≤ Real.exp (Real.log ((x i : ℝ≥0) : ℝ)) := Real.exp_le_exp.mpr hlog.1
        _ = _ := Real.exp_log hx0
    · calc ((x i : ℝ≥0) : ℝ) = Real.exp (Real.log ((x i : ℝ≥0) : ℝ)) := (Real.exp_log hx0).symm
        _ ≤ Real.exp (b i) := Real.exp_le_exp.mpr hlog.2
  have hcpt : IsCompact (fullIntrinsic F T I e ⁻¹' box) :=
    hRc.of_isClosed_subset (hboxc.preimage hΦc) hpre
  have himage : fullIntrinsic F T I e '' (fullIntrinsic F T I e ⁻¹' box) = box :=
    Set.image_preimage_eq _ (fullIntrinsic_surjective F T I e)
  rw [← himage]
  exact hcpt.image hΦc

end Langlands.Global.PositiveRealTorus

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan AdelicGroupPoints

/-- Under an actual algebraic Siegel setup, negation stability of the relative roots and the
root/character complement give that the restrictions to `T₀` of the simple roots span
`X*(T₀) ⊗ ℚ`. -/
theorem ratSpan_restrict_simpleRelativeRoots_eq_top
    (hneg : RelativeRootNegationStatement.{u})
    (hcompl : RelativeCharacterRootComplementStatement.{u})
    {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    ratSpan ((fun α : characterLattice T => j ≫ α) '' simpleRelativeRoots i ν) = ⊤ := by
  obtain ⟨hTmax, hν, -, -, -, -, -, ⟨D, d, t₀, hd, ht₀max, ht₀⟩, -⟩ := hsetup
  have hT : IsSplitTorus T.toGrp := hTmax.1.1
  have hT₀ : IsSplitTorus T₀.toGrp := ht₀max.1.1
  have hmono : Mono (CommGroupScheme.groupHom j).hom.hom.left := by
    have : IsClosedImmersion t₀.hom.hom.left := ht₀max.1.2
    have : IsClosedImmersion d.hom.hom.left := hd.1
    have h3 : Mono ((CommGroupScheme.groupHom j ≫ i).hom.hom.left) := by
      rw [← ht₀]
      simp only [Grp.comp_hom_hom, Over.comp_left]
      infer_instance
    simp only [Grp.comp_hom_hom, Over.comp_left] at h3
    exact mono_of_mono _ i.hom.hom.left
  have hTd : SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G := by
    rw [← ht₀, ← hd.2]
    intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ t₀.hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  let ρ := rationalCharacterRestrictRat (CommGroupScheme.groupHom j)
  have hρ : Function.Surjective ρ :=
    hT₀.rationalCharacterRestrictRat_surjective_of_mono hT _
  have hkill : ∀ x ∈ (rationalCharacterRestrictRat i).range, ρ x = 0 := by
    rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.inductionOn with
    | tmul q χ =>
      have h1 : characterRestrict (CommGroupScheme.groupHom j) (characterRestrict i χ) = 0 := by
        have h := charactersTrivialAlong_of_range_le_derived F T₀.toGrp G
          (CommGroupScheme.groupHom j ≫ i) hTd χ.toMul
        rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp]
        change Additive.ofMul ((CommGroupScheme.groupHom j ≫ i) ≫ χ.toMul) = 0
        rw [h]
        rfl
      change ρ (q ⊗ₜ[ℤ] characterRestrict i χ) = 0
      rw [rationalCharacterRestrictRat_tmul, h1, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have hspan : ratSpan (simpleRelativeRoots i ν) = relativeRootSpan i :=
    ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν (hneg F G hG T i hTmax)
  have hc := (hcompl F G hG T i hTmax).1
  have hmap : (ratSpan (simpleRelativeRoots i ν)).map ρ =
      ratSpan ((fun α : characterLattice T => j ≫ α) '' simpleRelativeRoots i ν) := by
    rw [ratSpan, ratSpan, Submodule.map_span, Set.image_image, Set.image_image]
    rfl
  rw [← hmap, hspan, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hρ y
  have hx : x ∈ relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, hkill b hb, add_zero]
  exact Submodule.mem_map_of_mem ha

/-- **Compact simple-root boxes from root theory.** Negation stability of the relative roots
and the root/character complement imply `SimpleRootBoxCompactStatement`. -/
theorem simpleRootBoxCompactStatement_of_rootComplement
    (hneg : RelativeRootNegationStatement.{u})
    (hcompl : RelativeCharacterRootComplementStatement.{u}) :
    SimpleRootBoxCompactStatement.{u} := by
  intro F _ _ G _ _ hG T i ν T₀ j hsetup s
  have hspan := ratSpan_restrict_simpleRelativeRoots_eq_top hneg hcompl hG hsetup
  obtain ⟨-, -, -, -, -, -, -, ⟨D, d, t₀, hd, ht₀max, ht₀⟩, -⟩ := hsetup
  have hbox := PositiveRealTorus.isCompact_characterBox F T₀ ht₀max.1.1 hspan s
  convert hbox using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.forall_mem_image]

end Langlands.Global.AdelicSiegelFactors
