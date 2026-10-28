import Langlands.Representation.Whittaker.MirabolicModels
import Langlands.Representation.Whittaker.Algebraic
import Langlands.Group.GL.MirabolicProjection
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Analysis.Local.QuotientTopology
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.Representation.Twist.ContinuousCharacterProof

/-!
# Uniqueness of Whittaker functionals on the actual compact mirabolic model

Restriction along the successor embedding `P_n → P_(n+1)` maps the compact
model of `P_(n+1)` onto that of `P_n`, and every Whittaker functional of rank
`n + 1` vanishes on its kernel. Induction on `n` then gives a test vector on
which every Whittaker functional of the compact model is determined.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Induction Topology

universe uF

namespace MirabolicWhittaker

section Algebra

variable {F : Type uF} [Field F] {n : ℕ}

/-- Upper unipotent mirabolic matrices of rank `n + 2` lie in the plus subgroup. -/
theorem upperUnipotent_le_plusSubgroup :
    Mirabolic.upperUnipotent (n + 1) F ≤ plusSubgroup n F := by
  intro u hu j
  change u.val.val (Fin.last n).castSucc j.castSucc = _
  by_cases hj : j = Fin.last n
  · subst hj
    simpa using hu.2 (Fin.last n).castSucc
  · rw [ite_eq_right hj]
    rcases lt_or_gt_of_ne hj with h | h
    · exact hu.1 (Fin.castSucc_lt_castSucc_iff.mpr h)
    · exact absurd h (not_lt.mpr (Fin.le_last j))

/-- The plus projection of an upper unipotent matrix is upper unipotent. -/
theorem plusProjection_mem_upperUnipotent (u : plusSubgroup n F)
    (hu : u.val ∈ Mirabolic.upperUnipotent (n + 1) F) :
    plusProjection u ∈ Mirabolic.upperUnipotent n F := by
  constructor
  · intro i j hij
    exact hu.1 (Fin.castSucc_lt_castSucc_iff.mpr hij)
  · intro i
    exact hu.2 i.castSucc

/-- The successor of an upper unipotent matrix is upper unipotent. -/
theorem successor_mem_upperUnipotent {u : mirabolic n F}
    (hu : u ∈ Mirabolic.upperUnipotent n F) :
    successor u ∈ Mirabolic.upperUnipotent (n + 1) F := by
  constructor
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      change (levi u.val).val.val (Fin.last (n + 1)) j = 0
      rw [levi_bottom]
      exact ite_eq_right (Fin.ne_last_of_lt hij)
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
      | cast j =>
        change (successor u).val.val i.castSucc j.castSucc = 0
        rw [successor_first]
        exact hu.1 (Fin.castSucc_lt_castSucc_iff.mp hij)
  · intro i
    induction i using Fin.lastCases with
    | last =>
      change (levi u.val).val.val (Fin.last (n + 1)) (Fin.last (n + 1)) = 1
      rw [levi_bottom]
      exact ite_eq_left rfl
    | cast i =>
      change (successor u).val.val i.castSucc i.castSucc = 1
      rw [successor_first]
      exact hu.2 i

/-- Right multiplication by a radical matrix is left multiplication by the
radical matrix of the transformed column. -/
theorem mul_radicalElement (g : mirabolic n F) (x : Fin n → F) :
    g * (radicalElement x).val =
      (radicalElement ((projection g).val.mulVec x)).val * g := by
  obtain ⟨v, a, rfl⟩ : ∃ v a, g = (radicalElement v).val * levi a :=
    ⟨_, _, eq_radicalElement_mul_levi g⟩
  rw [projection_radicalElement_mul_levi, mul_assoc, levi_mul_radicalElement, ← mul_assoc,
    ← mul_assoc, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← radicalElement_add,
    ← radicalElement_add, add_comm v]

variable [TopologicalSpace F]

/-- The rank-`n + 2` character splits off the final adjacent entry. -/
theorem mirabolicCharacter_succ (ψ : UnitaryAdditiveCharacter F)
    (u : Mirabolic.upperUnipotent (n + 1) F) :
    (mirabolicCharacter ψ (n + 1) u : ℂ) =
      ψ.complex (lastColumn u.val (Fin.last n)) *
        (mirabolicCharacter ψ n
          ⟨plusProjection ⟨u.val, upperUnipotent_le_plusSubgroup u.property⟩,
            plusProjection_mem_upperUnipotent _ u.property⟩ : ℂ) := by
  rw [mirabolicCharacter_eq_product, mirabolicCharacter_eq_product, Fin.prod_univ_castSucc,
    mul_comm]
  congr 1

/-- The successor embedding preserves the standard character. -/
theorem mirabolicCharacter_successor (ψ : UnitaryAdditiveCharacter F)
    (u : Mirabolic.upperUnipotent n F) :
    mirabolicCharacter ψ (n + 1) ⟨successor u.val, successor_mem_upperUnipotent u.property⟩ =
      mirabolicCharacter ψ n u := by
  apply Units.ext
  rw [mirabolicCharacter_succ]
  have h1 : lastColumn (successor u.val) = 0 := lastColumn_levi _
  have h2 : plusProjection ⟨successor u.val, upperUnipotent_le_plusSubgroup
      (successor_mem_upperUnipotent u.property)⟩ = u.val :=
    plusProjection_plusSuccessor u.val
  simp only [h1, Pi.zero_apply, AddChar.map_zero_eq_one, one_mul]
  congr 2
  exact Subtype.ext h2

/-- On the radical only the final coordinate is seen by the standard character. -/
theorem mirabolicCharacter_radicalElement (ψ : UnitaryAdditiveCharacter F)
    (x : Fin (n + 1) → F) :
    (mirabolicCharacter ψ (n + 1)
        ⟨(radicalElement x).val, radical_le_upperUnipotent (radicalElement x).property⟩ : ℂ) =
      ψ.complex (x (Fin.last n)) := by
  rw [mirabolicCharacter_succ]
  have h1 : plusProjection ⟨(radicalElement x).val, upperUnipotent_le_plusSubgroup
      (radical_le_upperUnipotent (radicalElement x).property)⟩ = 1 :=
    plusProjection_plusRadical (radicalElement x)
  have h2 : (⟨plusProjection ⟨(radicalElement x).val, upperUnipotent_le_plusSubgroup
      (radical_le_upperUnipotent (radicalElement x).property)⟩,
      plusProjection_mem_upperUnipotent _
        (radical_le_upperUnipotent (radicalElement x).property)⟩ :
      Mirabolic.upperUnipotent n F) = 1 := Subtype.ext h1
  rw [h2, map_one, Units.val_one, mul_one, lastColumn_radicalElement]

end Algebra

section Restriction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
variable (ψ : UnitaryAdditiveCharacter F)

/-- Compactly induced functions are determined by their values. -/
theorem compactFunctions_ext {f h : MirabolicCompactFunctions ψ n}
    (hfh : ∀ g, mirabolicCompactEval ψ n f g = mirabolicCompactEval ψ n h g) : f = h :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext hfh)))

/-- Every compactly induced function has an open subgroup of right periods. -/
theorem exists_openSubgroup_eval_mul (f : MirabolicCompactFunctions ψ n) :
    ∃ K : OpenSubgroup (mirabolic n F), ∀ (k : K) (x : mirabolic n F),
      mirabolicCompactEval ψ n f (x * k) = mirabolicCompactEval ψ n f x := by
  obtain ⟨K, hK⟩ := mirabolicCompactInduced_smooth ψ n f
  exact ⟨K, fun k x => congrArg (fun h => mirabolicCompactEval ψ n h x) (hK k)⟩

/-- Restriction of a function along the successor embedding. -/
def restrictFun (f : MirabolicCompactFunctions ψ (n + 1)) (g : mirabolic n F) : ℂ :=
  mirabolicCompactEval ψ (n + 1) f (successor g)

theorem restrictFun_covariance (f : MirabolicCompactFunctions ψ (n + 1))
    (u : Mirabolic.upperUnipotent n F) (g : mirabolic n F) :
    restrictFun ψ f (u.val * g) =
      mirabolicCharacterRepresentation ψ n u (restrictFun ψ f g) := by
  rw [mirabolicCharacterRepresentation_apply, restrictFun, map_mul,
    ← mirabolicCharacter_successor ψ u]
  exact mirabolicCompactEval_covariance ψ (n + 1) f
    ⟨successor u.val, successor_mem_upperUnipotent u.property⟩ (successor g)

/-- The projected support of the restriction lies in the image of the plus
subgroup part of any compact set covering the projected support. -/
theorem quotientSupport_restrictFun_subset (f : MirabolicCompactFunctions ψ (n + 1))
    {C : Set (mirabolic (n + 1) F)}
    (hC : Induction.quotientMap _ '' C = Induction.quotientSupport
      (Mirabolic.upperUnipotent (n + 1) F) (mirabolicCompactEval ψ (n + 1) f)) :
    Induction.quotientSupport (Mirabolic.upperUnipotent n F) (restrictFun ψ f) ⊆
      (fun q : plusSubgroup n F =>
        Induction.quotientMap (Mirabolic.upperUnipotent n F) (plusProjection q)) ''
        (Subtype.val ⁻¹' C) := by
  rintro _ ⟨p, hp, rfl⟩
  have hmem : Induction.quotientMap _ (successor p) ∈ Induction.quotientSupport
      (Mirabolic.upperUnipotent (n + 1) F) (mirabolicCompactEval ψ (n + 1) f) :=
    ⟨successor p, hp, rfl⟩
  rw [← hC] at hmem
  obtain ⟨c, hc, hcp⟩ := hmem
  have hu : successor p * c⁻¹ ∈ Mirabolic.upperUnipotent (n + 1) F :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hcp)
  have hcQ : c ∈ plusSubgroup n F := by
    have he : c = (successor p * c⁻¹)⁻¹ * successor p := by group
    rw [he]
    exact (plusSubgroup n F).mul_mem
      ((plusSubgroup n F).inv_mem (upperUnipotent_le_plusSubgroup hu))
      (successor_mem_plusSubgroup p)
  refine ⟨⟨c, hcQ⟩, hc, Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
  have h := plusProjection_mem_upperUnipotent ⟨_, upperUnipotent_le_plusSubgroup hu⟩ hu
  convert h using 1
  apply Subtype.ext
  rw [plusProjection_val, map_mul, map_inv, projection_successor]
  rfl

/-- The restriction as a smooth induced function of rank `n + 1`. -/
def restrictSmooth (f : MirabolicCompactFunctions ψ (n + 1)) : MirabolicSmoothFunctions ψ n :=
  Induction.smoothFunctionOf _ _ (restrictFun ψ f) (restrictFun_covariance ψ f)
    ((exists_openSubgroup_eval_mul ψ f).choose.comap successor continuous_successor)
    (fun k x => by
      rw [restrictFun, restrictFun, map_mul]
      exact (exists_openSubgroup_eval_mul ψ f).choose_spec
        ⟨successor k.val, OpenSubgroup.mem_comap.mp k.property⟩ _)

variable [T2Space F] [LocallyCompactSpace (Langlands.GeneralLinear (n + 2) F)]

/-- Restriction preserves compact support modulo the unipotent subgroup. -/
theorem isCompact_quotientSupport_restrictFun (f : MirabolicCompactFunctions ψ (n + 1)) :
    IsCompact (Induction.quotientSupport (Mirabolic.upperUnipotent n F) (restrictFun ψ f)) := by
  have : LocallyCompactSpace (mirabolic (n + 1) F) := Mirabolic.locallyCompactSpace
  obtain ⟨C, hC, hCimg⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (Mirabolic.upperUnipotent (n + 1) F) Mirabolic.upperUnipotent_isClosed f.property
  have hC' : IsCompact (Subtype.val ⁻¹' C : Set (plusSubgroup n F)) :=
    plusSubgroup_isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  exact (hC'.image ((QuotientIntegration.leftQuotient_isOpenQuotientMap _).continuous.comp
    continuous_plusProjection)).of_isClosed_subset
    (Induction.isClosed_quotientSupport _ _ (restrictSmooth ψ f))
    (quotientSupport_restrictFun_subset ψ f hCimg)

/-- Restriction along the successor embedding, as a linear map of compact models. -/
def restriction : MirabolicCompactFunctions ψ (n + 1) →ₗ[ℂ] MirabolicCompactFunctions ψ n where
  toFun f := ⟨restrictSmooth ψ f, isCompact_quotientSupport_restrictFun ψ f⟩
  map_add' _ _ := compactFunctions_ext ψ fun _ => rfl
  map_smul' _ _ := compactFunctions_ext ψ fun _ => rfl

@[simp] theorem restriction_eval (f : MirabolicCompactFunctions ψ (n + 1)) (g : mirabolic n F) :
    mirabolicCompactEval ψ n (restriction ψ f) g =
      mirabolicCompactEval ψ (n + 1) f (successor g) := rfl

/-- Restriction intertwines translation by the successor embedding. -/
theorem restriction_translate (f : MirabolicCompactFunctions ψ (n + 1)) (p : mirabolic n F) :
    restriction ψ (mirabolicCompactInduced ψ (n + 1) (successor p) f) =
      mirabolicCompactInduced ψ n p (restriction ψ f) :=
  compactFunctions_ext ψ fun g => by
    rw [restriction_eval, mirabolicCompactEval_translate, mirabolicCompactEval_translate,
      restriction_eval, map_mul]

end Restriction

section Extension

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
variable (ψ : UnitaryAdditiveCharacter F)

/-- Values on the plus subgroup: the radical character times the given function
of the plus projection. -/
def plusValue (f : MirabolicCompactFunctions ψ n) (q : plusSubgroup n F) : ℂ :=
  ψ.complex (lastColumn q.val (Fin.last n)) * mirabolicCompactEval ψ n f (plusProjection q)

/-- Left covariance of the plus-subgroup values. -/
theorem plusValue_left (f : MirabolicCompactFunctions ψ n)
    (u : Mirabolic.upperUnipotent (n + 1) F) (q : plusSubgroup n F) :
    plusValue ψ f (⟨u.val, upperUnipotent_le_plusSubgroup u.property⟩ * q) =
      (mirabolicCharacter ψ (n + 1) u : ℂ) * plusValue ψ f q := by
  have h := mirabolicCompactEval_covariance ψ n f
    ⟨_, plusProjection_mem_upperUnipotent ⟨u.val, upperUnipotent_le_plusSubgroup u.property⟩
      u.property⟩ (plusProjection q)
  rw [plusValue, plusValue, lastColumn_mul_last, AddChar.map_add_eq_mul, map_mul, h,
    mirabolicCharacter_succ]
  ring

/-- Right invariance of the plus-subgroup values under a suitable element. -/
theorem plusValue_mul_right (f : MirabolicCompactFunctions ψ n) {q k : plusSubgroup n F}
    (hk₁ : ψ.complex (lastColumn k.val (Fin.last n)) = 1)
    (hk₂ : ∀ x, mirabolicCompactEval ψ n f (x * plusProjection k) =
      mirabolicCompactEval ψ n f x) :
    plusValue ψ f (q * k) = plusValue ψ f q := by
  rw [plusValue, plusValue, lastColumn_mul_last, AddChar.map_add_eq_mul, hk₁, mul_one, map_mul,
    hk₂]

/-- On successor matrices the plus-subgroup values are the given function. -/
theorem plusValue_successor (f : MirabolicCompactFunctions ψ n) (p : mirabolic n F) :
    plusValue ψ f (plusSuccessor p) = mirabolicCompactEval ψ n f p := by
  rw [plusValue, plusProjection_plusSuccessor,
    show lastColumn (plusSuccessor p).val = 0 from lastColumn_levi _]
  simp

open Classical in
/-- Extension by zero from `Q * H`, where `Q` is the plus subgroup and `H` a subgroup. -/
def extendFun (H : Subgroup (mirabolic (n + 1) F)) (f : MirabolicCompactFunctions ψ n)
    (g : mirabolic (n + 1) F) : ℂ :=
  if h : ∃ k ∈ H, g * k⁻¹ ∈ plusSubgroup n F then
    plusValue ψ f ⟨g * h.choose⁻¹, h.choose_spec.2⟩ else 0

variable {ψ} {H : Subgroup (mirabolic (n + 1) F)} {f : MirabolicCompactFunctions ψ n}

/-- The compatibility of a subgroup with the given function needed for extension. -/
def IsExtensionGroup (H : Subgroup (mirabolic (n + 1) F)) (f : MirabolicCompactFunctions ψ n) :
    Prop :=
  ∀ k ∈ H, ∀ hk : k ∈ plusSubgroup n F, ψ.complex (lastColumn k (Fin.last n)) = 1 ∧
    ∀ x, mirabolicCompactEval ψ n f (x * plusProjection ⟨k, hk⟩) = mirabolicCompactEval ψ n f x

theorem extendFun_eq (hH : IsExtensionGroup H f) {g k : mirabolic (n + 1) F} (hk : k ∈ H)
    (hq : g * k⁻¹ ∈ plusSubgroup n F) :
    extendFun ψ H f g = plusValue ψ f ⟨g * k⁻¹, hq⟩ := by
  have h : ∃ k ∈ H, g * k⁻¹ ∈ plusSubgroup n F := ⟨k, hk, hq⟩
  rw [extendFun, dite_eq_left h]
  obtain ⟨hk₁, hq₁⟩ := h.choose_spec
  have hm : k * h.choose⁻¹ ∈ plusSubgroup n F := by
    have he : k * h.choose⁻¹ = (g * k⁻¹)⁻¹ * (g * h.choose⁻¹) := by group
    rw [he]
    exact mul_mem (inv_mem hq) hq₁
  have he : (⟨g * h.choose⁻¹, hq₁⟩ : plusSubgroup n F) =
      ⟨g * k⁻¹, hq⟩ * ⟨k * h.choose⁻¹, hm⟩ :=
    Subtype.ext (by simp [mul_assoc])
  obtain ⟨h₁, h₂⟩ := hH _ (H.mul_mem hk (H.inv_mem hk₁)) hm
  rw [he, plusValue_mul_right ψ f h₁ h₂]

theorem extendFun_left (hH : IsExtensionGroup H f) (u : Mirabolic.upperUnipotent (n + 1) F)
    (g : mirabolic (n + 1) F) :
    extendFun ψ H f (u.val * g) = (mirabolicCharacter ψ (n + 1) u : ℂ) * extendFun ψ H f g := by
  have huQ := upperUnipotent_le_plusSubgroup u.property
  by_cases h : ∃ k ∈ H, g * k⁻¹ ∈ plusSubgroup n F
  · obtain ⟨k, hk, hq⟩ := h
    have hq' : u.val * g * k⁻¹ ∈ plusSubgroup n F := by
      rw [mul_assoc]
      exact mul_mem huQ hq
    rw [extendFun_eq hH hk hq', extendFun_eq hH hk hq, ← plusValue_left]
    congr 1
    exact Subtype.ext (mul_assoc _ _ _)
  · have h' : ¬ ∃ k ∈ H, u.val * g * k⁻¹ ∈ plusSubgroup n F := by
      rintro ⟨k, hk, hq⟩
      refine h ⟨k, hk, ?_⟩
      have he : g * k⁻¹ = u.val⁻¹ * (u.val * g * k⁻¹) := by group
      rw [he]
      exact mul_mem (inv_mem huQ) hq
    rw [extendFun, dite_eq_right h', extendFun, dite_eq_right h, mul_zero]

theorem extendFun_right (hH : IsExtensionGroup H f) (g : mirabolic (n + 1) F)
    {k : mirabolic (n + 1) F} (hk : k ∈ H) :
    extendFun ψ H f (g * k) = extendFun ψ H f g := by
  by_cases h : ∃ k ∈ H, g * k⁻¹ ∈ plusSubgroup n F
  · obtain ⟨k₁, hk₁, hq⟩ := h
    have hq' : g * k * (k₁ * k)⁻¹ ∈ plusSubgroup n F := by
      convert hq using 1
      group
    rw [extendFun_eq hH (H.mul_mem hk₁ hk) hq', extendFun_eq hH hk₁ hq]
    congr 1
    exact Subtype.ext (by group)
  · have h' : ¬ ∃ k' ∈ H, g * k * k'⁻¹ ∈ plusSubgroup n F := by
      rintro ⟨k', hk', hq⟩
      exact h ⟨k' * k⁻¹, H.mul_mem hk' (H.inv_mem hk), by convert hq using 1; group⟩
    rw [extendFun, dite_eq_right h', extendFun, dite_eq_right h]

theorem extendFun_successor (hH : IsExtensionGroup H f) (p : mirabolic n F) :
    extendFun ψ H f (successor p) = mirabolicCompactEval ψ n f p := by
  have hq : successor p * 1⁻¹ ∈ plusSubgroup n F := by
    simp [successor_mem_plusSubgroup p]
  rw [extendFun_eq hH H.one_mem hq, ← plusValue_successor ψ f p]
  congr 1
  exact Subtype.ext (by simp)

theorem extendFun_ne_zero {g : mirabolic (n + 1) F} (hg : extendFun ψ H f g ≠ 0) :
    ∃ k ∈ H, ∃ hq : g * k⁻¹ ∈ plusSubgroup n F,
      mirabolicCompactEval ψ n f (plusProjection ⟨g * k⁻¹, hq⟩) ≠ 0 := by
  by_cases h : ∃ k ∈ H, g * k⁻¹ ∈ plusSubgroup n F
  · rw [extendFun, dite_eq_left h, plusValue] at hg
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, right_ne_zero_of_mul hg⟩
  · rw [extendFun, dite_eq_right h] at hg
    exact absurd rfl hg

variable (ψ)

/-- The extension as a smooth induced function, with the open subgroup as stabilizer. -/
def extendSmooth (H : OpenSubgroup (mirabolic (n + 1) F)) (f : MirabolicCompactFunctions ψ n)
    (hH : IsExtensionGroup H.toSubgroup f) : MirabolicSmoothFunctions ψ (n + 1) :=
  Induction.smoothFunctionOf _ _ (extendFun ψ H.toSubgroup f) (extendFun_left hH) H
    (fun k x => extendFun_right hH x k.property)

variable [T2Space F] [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F)]

/-- With a compact stabilizer, the extension has compact support modulo the unipotent group. -/
theorem isCompact_quotientSupport_extendFun (H : OpenSubgroup (mirabolic (n + 1) F))
    (hHc : IsCompact (H : Set (mirabolic (n + 1) F))) (f : MirabolicCompactFunctions ψ n)
    (hH : IsExtensionGroup H.toSubgroup f) :
    IsCompact (Induction.quotientSupport (Mirabolic.upperUnipotent (n + 1) F)
      (extendFun ψ H.toSubgroup f)) := by
  have : LocallyCompactSpace (mirabolic n F) := Mirabolic.locallyCompactSpace
  obtain ⟨C, hC, hCimg⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (Mirabolic.upperUnipotent n F) Mirabolic.upperUnipotent_isClosed f.property
  refine ((hC.prod hHc).image ((QuotientIntegration.leftQuotient_isOpenQuotientMap _).continuous.comp
    ((continuous_successor.comp continuous_fst).mul continuous_snd))).of_isClosed_subset
    (Induction.isClosed_quotientSupport _ _ (extendSmooth ψ H f hH)) ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨k, hk, hq, hne⟩ := extendFun_ne_zero hg
  have hmem : Induction.quotientMap _ (plusProjection ⟨g * k⁻¹, hq⟩) ∈
      Induction.quotientSupport (Mirabolic.upperUnipotent n F)
        (Induction.eval _ (mirabolicCharacterRepresentation ψ n) f.val) :=
    ⟨_, hne, rfl⟩
  rw [← hCimg] at hmem
  obtain ⟨c, hc, hcq⟩ := hmem
  refine ⟨(c, k), ⟨hc, hk⟩, ?_⟩
  change Induction.quotientMap _ (successor c * k) = Induction.quotientMap _ g
  refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
  have hu : plusProjection ⟨g * k⁻¹, hq⟩ * c⁻¹ ∈ Mirabolic.upperUnipotent n F :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hcq)
  have hp := plus_eq_radicalElement_mul_successor (⟨g * k⁻¹, hq⟩ : plusSubgroup n F)
  have he : g * (successor c * k)⁻¹ = (radicalElement (lastColumn (g * k⁻¹))).val *
      successor (plusProjection ⟨g * k⁻¹, hq⟩ * c⁻¹) := by
    rw [map_mul, map_inv, ← mul_assoc, ← hp]
    group
  rw [he]
  exact mul_mem (radical_le_upperUnipotent (radicalElement _).property)
    (successor_mem_upperUnipotent hu)

/-- The extension as a compactly induced function. -/
def extendCompact (H : OpenSubgroup (mirabolic (n + 1) F))
    (hHc : IsCompact (H : Set (mirabolic (n + 1) F))) (f : MirabolicCompactFunctions ψ n)
    (hH : IsExtensionGroup H.toSubgroup f) : MirabolicCompactFunctions ψ (n + 1) :=
  ⟨extendSmooth ψ H f hH, isCompact_quotientSupport_extendFun ψ H hHc f hH⟩

theorem restriction_extendCompact [LocallyCompactSpace (Langlands.GeneralLinear (n + 2) F)]
    (H : OpenSubgroup (mirabolic (n + 1) F))
    (hHc : IsCompact (H : Set (mirabolic (n + 1) F))) (f : MirabolicCompactFunctions ψ n)
    (hH : IsExtensionGroup H.toSubgroup f) :
    restriction ψ (extendCompact ψ H hHc f hH) = f :=
  compactFunctions_ext ψ fun p => extendFun_successor hH p

omit [T2Space F] in
/-- A subgroup of a nonarchimedean group is nonarchimedean. -/
theorem mirabolic_nonarchimedean {m : ℕ} [NonarchimedeanGroup (Langlands.GeneralLinear (m + 1) F)] :
    NonarchimedeanGroup (mirabolic m F) where
  is_nonarchimedean U hU := by
    rw [IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean V (by simpa using hV)
    exact ⟨OpenSubgroup.comap (mirabolic m F).subtype continuous_subtype_val L,
      fun x hx => hVU (hL hx)⟩

variable [NonarchimedeanGroup (Langlands.GeneralLinear (n + 2) F)]
  [LocallyCompactSpace (Langlands.GeneralLinear (n + 2) F)]

omit [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F)] in
/-- Every compactly induced function of rank `n + 1` admits a compact open
extension subgroup of rank `n + 2`, provided the kernel of `ψ` is open. -/
theorem exists_extensionGroup (hψ : IsOpen {t : F | ψ.complex t = 1})
    (f : MirabolicCompactFunctions ψ n) :
    ∃ H : OpenSubgroup (mirabolic (n + 1) F),
      IsCompact (H : Set (mirabolic (n + 1) F)) ∧ IsExtensionGroup H.toSubgroup f := by
  obtain ⟨K, hK⟩ := exists_openSubgroup_eval_mul ψ f
  obtain ⟨O, hO, hOK⟩ := isOpen_induced_iff.mp K.isOpen
  let W : Set (mirabolic (n + 1) F) :=
    {g | projection g ∈ O ∧ ψ.complex (lastColumn g (Fin.last n)) = 1}
  have hW : IsOpen W := (hO.preimage continuous_projection).inter
    (hψ.preimage ((continuous_apply _).comp continuous_lastColumn))
  have h1 : (1 : mirabolic (n + 1) F) ∈ W := by
    refine ⟨?_, by simp⟩
    have : (1 : mirabolic n F) ∈ Subtype.val ⁻¹' O := by rw [hOK]; exact K.one_mem
    simpa using this
  have := mirabolic_nonarchimedean (F := F) (m := n + 1)
  have : LocallyCompactSpace (mirabolic (n + 1) F) := Mirabolic.locallyCompactSpace
  obtain ⟨H, hHc, hHW⟩ := Langlands.compactOpenSubgroupBasis _ W (hW.mem_nhds h1)
  refine ⟨H, hHc, fun k hk hkQ => ⟨(hHW hk).2, fun x => ?_⟩⟩
  have hmem : plusProjection ⟨k, hkQ⟩ ∈ (K : Set (mirabolic n F)) := by
    rw [← hOK]
    exact (hHW hk).1
  exact hK ⟨_, hmem⟩ x

/-- Restriction along the successor embedding is surjective. -/
theorem restriction_surjective (hψ : IsOpen {t : F | ψ.complex t = 1}) :
    Function.Surjective (restriction ψ (n := n)) := by
  intro f
  obtain ⟨H, hHc, hH⟩ := exists_extensionGroup ψ hψ f
  exact ⟨extendCompact ψ H hHc f hH, restriction_extendCompact ψ H hHc f hH⟩

end Extension

section Kernel

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
variable (ψ : UnitaryAdditiveCharacter F)

/-- Whittaker functionals on the compact model, for its own character. -/
abbrev compactFunctionals (ψ : UnitaryAdditiveCharacter F) (n : ℕ) [IsTopologicalRing F] :
    Submodule ℂ (Module.Dual ℂ (MirabolicCompactFunctions ψ n)) :=
  functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) (mirabolicCompactInduced ψ n)

/-- The last row of the Levi projection. -/
def rowOf (g : mirabolic (n + 1) F) : Fin (n + 1) → F :=
  RankinSelberg.lastRow (projection g)

omit [TopologicalSpace F] in
theorem rowOf_upperUnipotent_mul (u : Mirabolic.upperUnipotent (n + 1) F)
    (g : mirabolic (n + 1) F) : rowOf (u.val * g) = rowOf g := by
  have hu : projection u.val ∈ mirabolic n F :=
    (plusProjection ⟨u.val, upperUnipotent_le_plusSubgroup u.property⟩).property
  rw [rowOf, map_mul, RankinSelberg.lastRow_mul_eq_vecMul,
    (RankinSelberg.mem_mirabolic_iff_lastRow _).mp hu, ← RankinSelberg.lastRow_mul_eq_vecMul,
    one_mul, rowOf]

omit [TopologicalSpace F] in
theorem lastRow_one_dotProduct (x : Fin (n + 1) → F) :
    RankinSelberg.lastRow (1 : Langlands.GeneralLinear (n + 1) F) ⬝ᵥ x = x (Fin.last n) := by
  simp [RankinSelberg.lastRow, dotProduct, Matrix.one_apply]

/-- Two values of `ψ` agree exactly when `ψ` is trivial on the difference. -/
theorem complex_eq_iff (a b : F) : ψ.complex a = ψ.complex b ↔ ψ.complex (a - b) = 1 := by
  have hb : ψ.complex b ≠ 0 := by
    intro h
    simpa [h] using ψ.norm_complex b
  conv_lhs => rw [show a = (a - b) + b by ring, AddChar.map_add_eq_mul]
  constructor
  · intro h
    exact mul_right_cancel₀ hb (h.trans (one_mul _).symm)
  · intro h
    rw [h, one_mul]

theorem exists_complex_ne_one : ∃ t, ψ.complex t ≠ 1 := by
  by_contra! h
  apply ψ.nontrivial
  apply AddChar.ext
  intro t
  apply Subtype.ext
  simpa using h t

variable [IsTopologicalRing F]

/-- Right translation by a radical matrix multiplies by a character of the row. -/
theorem eval_mul_radicalElement
    (f : MirabolicCompactFunctions ψ (n + 1)) (g : mirabolic (n + 1) F) (x : Fin (n + 1) → F) :
    mirabolicCompactEval ψ (n + 1) f (g * (radicalElement x).val) =
      ψ.complex (rowOf g ⬝ᵥ x) * mirabolicCompactEval ψ (n + 1) f g := by
  have h := mirabolicCompactEval_covariance ψ (n + 1) f
    ⟨(radicalElement ((projection g).val.mulVec x)).val,
      radical_le_upperUnipotent (radicalElement _).property⟩ g
  rw [mirabolicCharacter_radicalElement] at h
  rw [mul_radicalElement]
  exact h

/-- Whittaker functionals see radical translations through the final coordinate. -/
theorem functional_radicalElement
    {ℓ : Module.Dual ℂ (MirabolicCompactFunctions ψ (n + 1))}
    (hℓ : ℓ ∈ compactFunctionals ψ (n + 1)) (x : Fin (n + 1) → F)
    (f : MirabolicCompactFunctions ψ (n + 1)) :
    ℓ (mirabolicCompactInduced ψ (n + 1) (radicalElement x).val f) =
      ψ.complex (x (Fin.last n)) * ℓ f := by
  have h := hℓ ⟨_, radical_le_upperUnipotent (radicalElement x).property⟩ f
  rw [mirabolicCharacter_radicalElement] at h
  exact h

variable [T2Space F] [LocallyCompactSpace (Langlands.GeneralLinear (n + 2) F)]

/-- A function killed by restriction vanishes wherever the row lies in the row
image of the Levi part of its stabilizer. -/
theorem eval_eq_zero_of_rowOf_mem {f : MirabolicCompactFunctions ψ (n + 1)}
    (hf : restriction ψ f = 0) {K : OpenSubgroup (mirabolic (n + 1) F)}
    (hK : ∀ (k : K) (x : mirabolic (n + 1) F),
      mirabolicCompactEval ψ (n + 1) f (x * k) = mirabolicCompactEval ψ (n + 1) f x)
    {g : mirabolic (n + 1) F}
    (hg : rowOf g ∈ RankinSelberg.lastRow ''
      ((K.comap levi continuous_levi : OpenSubgroup (Langlands.GeneralLinear (n + 1) F)) :
        Set (Langlands.GeneralLinear (n + 1) F))) :
    mirabolicCompactEval ψ (n + 1) f g = 0 := by
  obtain ⟨a, j, hj⟩ := (RankinSelberg.lastRow_mem_image_iff
    (K.comap levi continuous_levi).toSubgroup (projection g)).mp hg
  have hg' : g = (radicalElement (lastColumn g)).val * successor a * levi j.val := by
    conv_lhs => rw [eq_radicalElement_mul_levi g, hj, map_mul]
    rw [mul_assoc]
    rfl
  have hj' : levi j.val ∈ K := j.property
  rw [hg', hK ⟨_, hj'⟩]
  have h := mirabolicCompactEval_covariance ψ (n + 1) f
    ⟨(radicalElement (lastColumn g)).val,
      radical_le_upperUnipotent (radicalElement _).property⟩ (successor a)
  rw [h, ← restriction_eval, hf]
  simp

omit [T2Space F] [LocallyCompactSpace (Langlands.GeneralLinear (n + 2) F)] in
/-- A Whittaker functional vanishes on every function whose nonzero values sit
where some character of the row takes a value different from its value at the
final standard row. -/
theorem functional_eq_zero_of_finset {ℓ : Module.Dual ℂ (MirabolicCompactFunctions ψ (n + 1))}
    (hℓ : ℓ ∈ compactFunctionals ψ (n + 1)) (S : Finset ((Fin (n + 1) → F) × ℂ))
    (hS : ∀ p ∈ S, p.2 ≠ ψ.complex (p.1 (Fin.last n))) :
    ∀ h : MirabolicCompactFunctions ψ (n + 1),
      (∀ g, mirabolicCompactEval ψ (n + 1) h g ≠ 0 →
        ∃ p ∈ S, ψ.complex (rowOf g ⬝ᵥ p.1) = p.2) → ℓ h = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro h hh
    have h0 : h = 0 := compactFunctions_ext ψ fun g => by
      by_contra hg
      obtain ⟨p, hp, -⟩ := hh g hg
      exact absurd hp (Finset.notMem_empty p)
    rw [h0, map_zero]
  | insert p S _ ih =>
    intro h hh
    let h' := mirabolicCompactInduced ψ (n + 1) (radicalElement p.1).val h - p.2 • h
    have hval : ∀ g, mirabolicCompactEval ψ (n + 1) h' g =
        (ψ.complex (rowOf g ⬝ᵥ p.1) - p.2) * mirabolicCompactEval ψ (n + 1) h g := by
      intro g
      change mirabolicCompactEval ψ (n + 1)
          (mirabolicCompactInduced ψ (n + 1) (radicalElement p.1).val h) g -
          p.2 * mirabolicCompactEval ψ (n + 1) h g = _
      rw [mirabolicCompactEval_translate, eval_mul_radicalElement]
      ring
    have h0 : ℓ h' = 0 := by
      refine ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)) h' fun g hg => ?_
      rw [hval] at hg
      obtain ⟨q, hq, hqg⟩ := hh g (right_ne_zero_of_mul hg)
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact absurd (sub_eq_zero.mpr hqg) (left_ne_zero_of_mul hg)
      · exact ⟨q, hq, hqg⟩
    have hℓh' : ℓ h' = (ψ.complex (p.1 (Fin.last n)) - p.2) * ℓ h := by
      simp only [h', map_sub, map_smul, functional_radicalElement ψ hℓ, smul_eq_mul]
      ring
    rw [hℓh'] at h0
    exact (mul_eq_zero.mp h0).resolve_left
      (sub_ne_zero.mpr (hS p (Finset.mem_insert_self p S)).symm)

end Kernel

section KernelVanishing

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  {n : ℕ} [LocallyCompactSpace (Langlands.GeneralLinear (n + 2) F)]
variable (ψ : UnitaryAdditiveCharacter F)

/-- Every Whittaker functional of rank `n + 2` vanishes on the kernel of restriction,
provided the kernel of `ψ` is open. -/
theorem functional_eq_zero_of_restriction_eq_zero (hψ : IsOpen {t : F | ψ.complex t = 1})
    {ℓ : Module.Dual ℂ (MirabolicCompactFunctions ψ (n + 1))}
    (hℓ : ℓ ∈ compactFunctionals ψ (n + 1)) {f : MirabolicCompactFunctions ψ (n + 1)}
    (hf : restriction ψ f = 0) : ℓ f = 0 := by
  classical
  obtain ⟨K, hK⟩ := exists_openSubgroup_eval_mul ψ f
  let J := K.comap levi continuous_levi
  let O := RankinSelberg.lastRow '' (J : Set (Langlands.GeneralLinear (n + 1) F))
  have hO : IsOpen O := RankinSelberg.isOpen_lastRow_image J.toSubgroup J.isOpen
  have he : RankinSelberg.lastRow (1 : Langlands.GeneralLinear (n + 1) F) ∈ O :=
    ⟨1, J.one_mem, rfl⟩
  have : LocallyCompactSpace (mirabolic (n + 1) F) := Mirabolic.locallyCompactSpace
  obtain ⟨C, hC, hCimg⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (Mirabolic.upperUnipotent (n + 1) F) Mirabolic.upperUnipotent_isClosed f.property
  have hr : Continuous (rowOf (n := n) (F := F)) :=
    RankinSelberg.continuous_lastRow.comp continuous_projection
  let S := rowOf '' C \ O
  have hSc : IsCompact S := (hC.image hr).diff hO
  have hx : ∀ y ∈ S, ∃ x : Fin (n + 1) → F,
      ψ.complex (y ⬝ᵥ x) ≠ ψ.complex (x (Fin.last n)) := by
    intro y hy
    have hne : y - RankinSelberg.lastRow (1 : Langlands.GeneralLinear (n + 1) F) ≠ 0 := by
      intro h
      exact hy.2 ((sub_eq_zero.mp h) ▸ he)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    obtain ⟨t, ht⟩ := exists_complex_ne_one ψ
    refine ⟨Pi.single j (t / (y - RankinSelberg.lastRow (1 : Langlands.GeneralLinear (n + 1) F)) j), ?_⟩
    rw [← lastRow_one_dotProduct (Pi.single j (t / (y - RankinSelberg.lastRow
      (1 : Langlands.GeneralLinear (n + 1) F)) j)), Ne, complex_eq_iff, ← sub_dotProduct, dotProduct_single,
      mul_div_cancel₀ _ hj]
    exact ht
  choose! X hX using hx
  have hU : ∀ y ∈ S, {z | ψ.complex (z ⬝ᵥ X y) = ψ.complex (y ⬝ᵥ X y)} ∈ 𝓝 y := by
    intro y _
    have hset : {z | ψ.complex (z ⬝ᵥ X y) = ψ.complex (y ⬝ᵥ X y)} =
        (fun z => (z - y) ⬝ᵥ X y) ⁻¹' {t : F | ψ.complex t = 1} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, complex_eq_iff, sub_dotProduct]
    rw [hset]
    refine (hψ.preimage ((continuous_id.sub continuous_const).dotProduct continuous_const)).mem_nhds ?_
    simp
  obtain ⟨t, htS, htcover⟩ := hSc.elim_nhds_subcover _ hU
  refine functional_eq_zero_of_finset ψ hℓ (t.image fun y => (X y, ψ.complex (y ⬝ᵥ X y)))
    ?_ f ?_
  · simp only [Finset.mem_image]
    rintro _ ⟨y, hy, rfl⟩
    exact hX y (htS y hy)
  · intro g hg
    have hmem : Induction.quotientMap _ g ∈ Induction.quotientSupport
        (Mirabolic.upperUnipotent (n + 1) F)
        (Induction.eval _ (mirabolicCharacterRepresentation ψ (n + 1)) f.val) :=
      ⟨_, hg, rfl⟩
    rw [← hCimg] at hmem
    obtain ⟨c, hc, hcg⟩ := hmem
    have hu : g * c⁻¹ ∈ Mirabolic.upperUnipotent (n + 1) F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hcg)
    have hrow : rowOf g = rowOf c := by
      have := rowOf_upperUnipotent_mul ⟨g * c⁻¹, hu⟩ c
      rwa [inv_mul_cancel_right] at this
    have hgS : rowOf g ∈ S := by
      refine ⟨⟨c, hc, hrow.symm⟩, fun hO' => hg ?_⟩
      exact eval_eq_zero_of_rowOf_mem ψ hf hK hO'
    obtain ⟨y, hy, hyg⟩ := Set.mem_iUnion₂.mp (htcover hgS)
    exact ⟨_, Finset.mem_image_of_mem _ hy, hyg⟩

end KernelVanishing

section Induction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
variable (ψ : UnitaryAdditiveCharacter F)

omit [IsTopologicalDivisionRing F] [T2Space F] in
/-- The rank-one compact model is spanned by any function that is nonzero at the
identity, and is zero if there is none; either way some vector detects every
Whittaker functional. -/
theorem exists_testVector_zero [IsTopologicalRing F] :
    ∃ f₀ : MirabolicCompactFunctions ψ 0,
      ∀ ℓ ∈ compactFunctionals ψ 0, ℓ f₀ = 0 → ℓ = 0 := by
  classical
  by_cases h : ∃ f : MirabolicCompactFunctions ψ 0, mirabolicCompactEval ψ 0 f 1 ≠ 0
  · obtain ⟨f₀, hf₀⟩ := h
    refine ⟨f₀, fun ℓ _ hℓ₀ => LinearMap.ext fun f => ?_⟩
    have hf : f = (mirabolicCompactEval ψ 0 f 1 / mirabolicCompactEval ψ 0 f₀ 1) • f₀ :=
      compactFunctions_ext ψ fun g => by
        rw [Subsingleton.elim g 1]
        change mirabolicCompactEval ψ 0 f 1 =
          (mirabolicCompactEval ψ 0 f 1 / mirabolicCompactEval ψ 0 f₀ 1) *
            mirabolicCompactEval ψ 0 f₀ 1
        field_simp
    rw [hf, map_smul, hℓ₀, smul_zero, LinearMap.zero_apply]
  · push Not at h
    refine ⟨0, fun ℓ _ _ => LinearMap.ext fun f => ?_⟩
    have hf : f = 0 := compactFunctions_ext ψ fun g => by
      rw [Subsingleton.elim g 1, h f]
      rfl
    rw [hf, map_zero, LinearMap.zero_apply]

variable {n : ℕ} [NonarchimedeanGroup (Langlands.GeneralLinear (n + 2) F)]
  [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F)]
  [LocallyCompactSpace (Langlands.GeneralLinear (n + 2) F)]

/-- Every Whittaker functional of rank `n + 2` factors through restriction via a
Whittaker functional of rank `n + 1`. -/
theorem exists_functional_comp_restriction (hψ : IsOpen {t : F | ψ.complex t = 1})
    {ℓ : Module.Dual ℂ (MirabolicCompactFunctions ψ (n + 1))}
    (hℓ : ℓ ∈ compactFunctionals ψ (n + 1)) :
    ∃ ℓ' ∈ compactFunctionals ψ n, ℓ'.comp (restriction ψ) = ℓ := by
  have hR := restriction_surjective ψ hψ (n := n)
  have hmem : ℓ ∈ LinearMap.range (restriction ψ (n := n)).dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _ hR,
      Submodule.mem_dualAnnihilator]
    intro f hf
    exact functional_eq_zero_of_restriction_eq_zero ψ hψ hℓ hf
  obtain ⟨ℓ', hℓ'⟩ := hmem
  rw [LinearMap.dualMap_apply'] at hℓ'
  refine ⟨ℓ', fun u f' => ?_, hℓ'⟩
  obtain ⟨f, rfl⟩ := hR f'
  have h : ℓ (mirabolicCompactInduced ψ (n + 1) (successor u.val) f) =
      (mirabolicCharacter ψ n u : ℂ) * ℓ f := by
    rw [← mirabolicCharacter_successor ψ u]
    exact hℓ ⟨successor u.val, successor_mem_upperUnipotent u.property⟩ f
  have e : ∀ x, ℓ' (restriction ψ x) = ℓ x := fun x => LinearMap.congr_fun hℓ' x
  exact (congrArg ℓ' (restriction_translate ψ f u.val).symm).trans
    ((e _).trans (h.trans (congrArg _ (e f).symm)))

end Induction

section TestVector

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F)]
  [∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F)]
variable (ψ : UnitaryAdditiveCharacter F)

/-- Uniqueness of Whittaker functionals on the compact mirabolic model: some
vector detects every Whittaker functional, provided the kernel of `ψ` is open. -/
theorem exists_testVector (hψ : IsOpen {t : F | ψ.complex t = 1}) :
    ∀ n : ℕ, ∃ f₀ : MirabolicCompactFunctions ψ n,
      ∀ ℓ ∈ compactFunctionals ψ n, ℓ f₀ = 0 → ℓ = 0
  | 0 => exists_testVector_zero ψ
  | n + 1 => by
    obtain ⟨f₀, hf₀⟩ := exists_testVector hψ n
    obtain ⟨f₁, hf₁⟩ := restriction_surjective ψ hψ f₀
    refine ⟨f₁, fun ℓ hℓ hℓ₀ => ?_⟩
    obtain ⟨ℓ', hℓ', hcomp⟩ := exists_functional_comp_restriction ψ hψ hℓ
    have e : ℓ' (restriction ψ f₁) = ℓ f₁ := LinearMap.congr_fun hcomp f₁
    have h0 : ℓ' f₀ = 0 := by
      rw [← hf₁]
      exact e.trans hℓ₀
    have hℓ'₀ : ℓ' = 0 := hf₀ ℓ' hℓ' h0
    exact hcomp.symm.trans ((congrArg (fun m : Module.Dual ℂ (MirabolicCompactFunctions ψ n) =>
      m.comp (restriction ψ)) hℓ'₀).trans (LinearMap.zero_comp _))

end TestVector

section Padic

variable {F : Type uF} [Field F] [TopologicalSpace F] [NonarchimedeanAddGroup F]

/-- A continuous unitary additive character of a field with an open additive
subgroup basis at zero has an open kernel. -/
theorem isOpen_complex_eq_one (ψ : UnitaryAdditiveCharacter F) :
    IsOpen {t : F | ψ.complex t = 1} := by
  let S : AddSubgroup F :=
    { carrier := {t | ψ.complex t = 1}
      zero_mem' := AddChar.map_zero_eq_one _
      add_mem' := fun {a b} ha hb => by
        change ψ.complex (a + b) = 1
        rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        change ψ.complex (-a) = 1
        rw [AddChar.map_neg_eq_inv, ha, inv_one] }
  let O : Set F := {t | ‖ψ.complex t - 1‖ < (1 / 2 : ℝ)}
  have hO : IsOpen O :=
    isOpen_lt ((ψ.continuous_complex.sub continuous_const).norm) continuous_const
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean O
    (hO.mem_nhds (by simp [O]))
  refine S.isOpen_of_openAddSubgroup (U := K) fun t ht => ?_
  apply complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro k
  rw [← AddChar.map_nsmul_eq_pow]
  exact hK (K.nsmul_mem ht k)

end Padic

end MirabolicWhittaker

end Langlands.Whittaker
