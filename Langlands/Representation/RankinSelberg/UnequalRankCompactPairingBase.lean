import Langlands.Representation.RankinSelberg.UnequalRankCompactPairingReduction
import Langlands.Representation.Whittaker.MirabolicQuotientMeasure
import Langlands.Representation.Whittaker.MirabolicCompactAdapters

/-!
# Adjacent-rank unequal-rank compact mirabolic pairings

Restriction along the Levi embedding `GL_(n+1) → P_(n+1)` identifies the compact
mirabolic model of rank `n + 2`, restricted to `GL_(n+1)`, with the compact Whittaker
induction `c-Ind_N^(GL_(n+1)) θ` of the standard character. Consequently the adjacent-rank
unequal-rank covariant forms are the invariant forms on `c-Ind_N^(GL_(n+1)) θ × η`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear GeneralLinear.Mirabolic Topology

universe uF uW

namespace UnequalRankCompactPairing

section LeviAlgebra

variable {F : Type uF} [Field F] {n : ℕ}

/-- An upper unipotent matrix does not change the last coordinate of a vector. -/
theorem upperUnipotent_mulVec_last (u : GeneralLinear.upperUnipotent (n + 1) F)
    (x : Fin (n + 1) → F) :
    Matrix.mulVec u.val.val x (Fin.last n) = x (Fin.last n) := by
  change ∑ j, u.val.val (Fin.last n) j * x j = x (Fin.last n)
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [show u.val.val (Fin.last n) (Fin.last n) = 1 from UpperUnipotent.entry_diag u _, one_mul]
  · intro j _ hj
    rw [show u.val.val (Fin.last n) j = 0 from
      UpperUnipotent.entry_eq_zero u (Fin.lt_last_iff_ne_last.mpr hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The projection of an upper unipotent mirabolic matrix, as an upper unipotent matrix. -/
def projectionUnipotentGL (u : Mirabolic.upperUnipotent (n + 1) F) :
    GeneralLinear.upperUnipotent (n + 1) F :=
  ⟨projection u.val, MirabolicQuotient.projection_mem_upperUnipotent u.property⟩

/-- The Levi image of an upper unipotent matrix, as an upper unipotent mirabolic matrix. -/
def leviUnipotent (u : GeneralLinear.upperUnipotent (n + 1) F) :
    Mirabolic.upperUnipotent (n + 1) F :=
  ⟨levi u.val, MirabolicQuotient.levi_mem_upperUnipotent u.property⟩

/-- Left multiplication by an upper unipotent mirabolic matrix adds its final radical
coordinate to the final radical coordinate. -/
theorem lastColumn_upperUnipotent_mul_last (u : Mirabolic.upperUnipotent (n + 1) F)
    (p : mirabolic (n + 1) F) :
    lastColumn (u.val * p) (Fin.last n) =
      lastColumn p (Fin.last n) + lastColumn u.val (Fin.last n) := by
  rw [lastColumn_mul, Pi.add_apply]
  exact congrArg (· + lastColumn u.val (Fin.last n))
    (upperUnipotent_mulVec_last (projectionUnipotentGL u) (lastColumn p))

end LeviAlgebra

section Characters

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
variable (ψ : UnitaryAdditiveCharacter F)

/-- The standard character of the mirabolic unipotent group splits as the final radical
coordinate times the standard character of the projection. -/
theorem mirabolicCharacter_eq_projection (u : Mirabolic.upperUnipotent (n + 1) F) :
    (mirabolicCharacter ψ (n + 1) u : ℂ) =
      ψ.complex (lastColumn u.val (Fin.last n)) *
        (standardCharacter ψ n (projectionUnipotentGL u) : ℂ) :=
  MirabolicWhittaker.mirabolicCharacter_succ ψ u

/-- The Levi embedding preserves the standard character. -/
theorem mirabolicCharacter_leviUnipotent (u : GeneralLinear.upperUnipotent (n + 1) F) :
    (mirabolicCharacter ψ (n + 1) (leviUnipotent u) : ℂ) = standardCharacter ψ n u := by
  rw [mirabolicCharacter_eq_projection]
  have h1 : lastColumn (leviUnipotent u).val = 0 := lastColumn_levi _
  have h2 : projectionUnipotentGL (leviUnipotent u) = u := Subtype.ext (projection_levi u.val)
  rw [h1, h2, Pi.zero_apply, AddChar.map_zero_eq_one, one_mul]

end Characters

section Levi

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
variable (ψ : UnitaryAdditiveCharacter F)

/-- Compactly induced functions for the standard character of `GL_(n+1)`. -/
abbrev GLCompactFunctions (ψ : UnitaryAdditiveCharacter F) (n : ℕ) : Type uF :=
  Induction.CompactFunctions (GeneralLinear.upperUnipotent (n + 1) F)
    (characterRepresentation (standardCharacter ψ n))

/-- Compact Whittaker induction `c-Ind_N^(GL_(n+1)) θ` of the standard character. -/
abbrev glCompactInduced (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F) (GLCompactFunctions ψ n) :=
  Induction.compactInduced (GeneralLinear.upperUnipotent (n + 1) F)
    (characterRepresentation (standardCharacter ψ n))

/-- Functions in `c-Ind_N^(GL_(n+1)) θ` are determined by their values. -/
theorem glCompactFunctions_ext {f h : GLCompactFunctions ψ n}
    (hfh : ∀ g, f.val.val.val g = h.val.val.val g) : f = h :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext hfh)))

/-- Restriction of a function along the Levi embedding. -/
def leviRestrictFun (f : MirabolicCompactFunctions ψ (n + 1))
    (a : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  mirabolicCompactEval ψ (n + 1) f (levi a)

theorem leviRestrictFun_covariance (f : MirabolicCompactFunctions ψ (n + 1))
    (u : GeneralLinear.upperUnipotent (n + 1) F) (a : Langlands.GeneralLinear (n + 1) F) :
    leviRestrictFun ψ f (u.val * a) =
      characterRepresentation (standardCharacter ψ n) u (leviRestrictFun ψ f a) := by
  change mirabolicCompactEval ψ (n + 1) f (levi (u.val * a)) =
    (standardCharacter ψ n u : ℂ) * mirabolicCompactEval ψ (n + 1) f (levi a)
  rw [map_mul, ← mirabolicCharacter_leviUnipotent ψ u]
  exact mirabolicCompactEval_covariance ψ (n + 1) f (leviUnipotent u) (levi a)

/-- The Levi restriction as a smooth induced function. -/
def leviRestrictSmooth (f : MirabolicCompactFunctions ψ (n + 1)) :
    Induction.SmoothFunctions (GeneralLinear.upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)) :=
  Induction.smoothFunctionOf _ _ (leviRestrictFun ψ f) (leviRestrictFun_covariance ψ f)
    ((MirabolicWhittaker.exists_openSubgroup_eval_mul ψ f).choose.comap levi continuous_levi)
    (fun k x => by
      rw [leviRestrictFun, leviRestrictFun, map_mul]
      exact (MirabolicWhittaker.exists_openSubgroup_eval_mul ψ f).choose_spec
        ⟨levi k.val, OpenSubgroup.mem_comap.mp k.property⟩ _)

/-- The projected support of the Levi restriction lies in the image of the projected
support under the quotient homeomorphism. -/
theorem quotientSupport_leviRestrictFun_subset (f : MirabolicCompactFunctions ψ (n + 1)) :
    Induction.quotientSupport (GeneralLinear.upperUnipotent (n + 1) F) (leviRestrictFun ψ f) ⊆
      MirabolicQuotient.quotientHomeomorph '' Induction.quotientSupport
        (Mirabolic.upperUnipotent (n + 1) F) (mirabolicCompactEval ψ (n + 1) f) := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨Induction.quotientMap _ (levi a), ⟨levi a, ha, rfl⟩,
    congrArg (Quotient.mk _) (projection_levi a)⟩

theorem isCompact_quotientSupport_leviRestrictFun (f : MirabolicCompactFunctions ψ (n + 1)) :
    IsCompact (Induction.quotientSupport (GeneralLinear.upperUnipotent (n + 1) F)
      (leviRestrictFun ψ f)) :=
  (f.property.image MirabolicQuotient.quotientHomeomorph.continuous).of_isClosed_subset
    (Induction.isClosed_quotientSupport _ _ (leviRestrictSmooth ψ f))
    (quotientSupport_leviRestrictFun_subset ψ f)

/-- Restriction along the Levi embedding, as a linear map of compact models. -/
def leviRestriction : MirabolicCompactFunctions ψ (n + 1) →ₗ[ℂ] GLCompactFunctions ψ n where
  toFun f := ⟨leviRestrictSmooth ψ f, isCompact_quotientSupport_leviRestrictFun ψ f⟩
  map_add' _ _ := glCompactFunctions_ext ψ fun _ => rfl
  map_smul' _ _ := glCompactFunctions_ext ψ fun _ => rfl

@[simp] theorem leviRestriction_apply (f : MirabolicCompactFunctions ψ (n + 1))
    (a : Langlands.GeneralLinear (n + 1) F) :
    (leviRestriction ψ f).val.val.val a = mirabolicCompactEval ψ (n + 1) f (levi a) := rfl

/-- Every function of the compact mirabolic model is determined by its Levi restriction. -/
theorem eval_eq_lastColumn_mul_levi (f : MirabolicCompactFunctions ψ (n + 1))
    (p : mirabolic (n + 1) F) :
    mirabolicCompactEval ψ (n + 1) f p =
      ψ.complex (lastColumn p (Fin.last n)) *
        mirabolicCompactEval ψ (n + 1) f (levi (projection p)) := by
  have h := mirabolicCompactEval_covariance ψ (n + 1) f
    ⟨(radicalElement (lastColumn p)).val, radical_le_upperUnipotent (radicalElement _).property⟩
    (levi (projection p))
  rw [MirabolicWhittaker.mirabolicCharacter_radicalElement] at h
  exact (congrArg (mirabolicCompactEval ψ (n + 1) f) (eq_radicalElement_mul_levi p)).trans h

/-- Extension from `GL_(n+1)`: the radical character of the final coordinate times the
given function of the projection. -/
def leviExtendFun (h : GLCompactFunctions ψ n) (p : mirabolic (n + 1) F) : ℂ :=
  ψ.complex (lastColumn p (Fin.last n)) * h.val.val.val (projection p)

theorem leviExtendFun_covariance (h : GLCompactFunctions ψ n)
    (u : Mirabolic.upperUnipotent (n + 1) F) (p : mirabolic (n + 1) F) :
    leviExtendFun ψ h (u.val * p) =
      mirabolicCharacterRepresentation ψ (n + 1) u (leviExtendFun ψ h p) := by
  have hcov : h.val.val.val (projection u.val * projection p) =
      (standardCharacter ψ n (projectionUnipotentGL u) : ℂ) * h.val.val.val (projection p) :=
    h.val.val.property (projectionUnipotentGL u) (projection p)
  rw [mirabolicCharacterRepresentation_apply, mirabolicCharacter_eq_projection, leviExtendFun,
    leviExtendFun, lastColumn_upperUnipotent_mul_last, map_mul, hcov, AddChar.map_add_eq_mul]
  ring

/-- The right periods of the extension. -/
def leviExtendPeriods (h : GLCompactFunctions ψ n) : Subgroup (mirabolic (n + 1) F) where
  carrier := {k | ∀ p, leviExtendFun ψ h (p * k) = leviExtendFun ψ h p}
  one_mem' p := by rw [mul_one]
  mul_mem' {a b} ha hb p := by rw [← mul_assoc, hb, ha]
  inv_mem' {a} ha p := by
    have e := ha (p * a⁻¹)
    rw [inv_mul_cancel_right] at e
    exact e.symm

variable [T2Space F] [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F)]

/-- With an open kernel of `ψ`, the extension is right invariant under a neighbourhood of the
identity: the rows of the support are compact. -/
theorem leviExtendPeriods_mem_nhds (hψ : IsOpen {t : F | ψ.complex t = 1})
    (h : GLCompactFunctions ψ n) :
    (leviExtendPeriods ψ h : Set (mirabolic (n + 1) F)) ∈ 𝓝 1 := by
  obtain ⟨K, hK⟩ := Induction.compactInduced_smooth (GeneralLinear.upperUnipotent (n + 1) F)
    (characterRepresentation (standardCharacter ψ n)) h
  obtain ⟨C, hC, hCimg⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (GeneralLinear.upperUnipotent (n + 1) F) GeneralLinear.UpperUnipotent.isClosed h.property
  let φ : Langlands.GeneralLinear (n + 1) F × (Fin (n + 1) → F) → F :=
    fun cx => Matrix.mulVec cx.1.val cx.2 (Fin.last n)
  have hφ : Continuous φ := by
    show Continuous fun cx : Langlands.GeneralLinear (n + 1) F × (Fin (n + 1) → F) =>
      Matrix.mulVec cx.1.val cx.2 (Fin.last n)
    exact (continuous_apply (Fin.last n)).comp
      ((Units.continuous_val.comp continuous_fst).matrix_mulVec continuous_snd)
  have hsub : C ×ˢ ({0} : Set (Fin (n + 1) → F)) ⊆ φ ⁻¹' {t | ψ.complex t = 1} := by
    rintro ⟨c, x⟩ ⟨-, hx⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp [φ]
  obtain ⟨u, U, -, hU, hCu, h0U, hCU⟩ :=
    generalized_tube_lemma hC isCompact_singleton (hψ.preimage hφ) hsub
  have hO : (projection ⁻¹' (K : Set (Langlands.GeneralLinear (n + 1) F)) ∩
      lastColumn ⁻¹' U : Set (mirabolic (n + 1) F)) ∈ 𝓝 1 := by
    refine ((K.isOpen.preimage continuous_projection).inter
      (hU.preimage continuous_lastColumn)).mem_nhds ⟨?_, ?_⟩
    · simp only [Set.mem_preimage, map_one, SetLike.mem_coe]
      exact K.one_mem
    · simp only [Set.mem_preimage, lastColumn_one]
      exact h0U rfl
  refine Filter.mem_of_superset hO ?_
  rintro k ⟨hkK, hkU⟩ p
  have hper : h.val.val.val (projection p * projection k) = h.val.val.val (projection p) :=
    congrArg (fun φ : GLCompactFunctions ψ n => φ.val.val.val (projection p))
      (hK ⟨projection k, hkK⟩)
  rw [leviExtendFun, leviExtendFun, lastColumn_mul, map_mul, hper, Pi.add_apply,
    AddChar.map_add_eq_mul]
  by_cases hp : h.val.val.val (projection p) = 0
  · rw [hp, mul_zero, mul_zero]
  · have hmem : Induction.quotientMap _ (projection p) ∈ Induction.quotientSupport
        (GeneralLinear.upperUnipotent (n + 1) F)
        (Induction.eval _ (characterRepresentation (standardCharacter ψ n)) h.val) :=
      ⟨projection p, hp, rfl⟩
    rw [← hCimg] at hmem
    obtain ⟨c, hc, hcp⟩ := hmem
    have hu : projection p * c⁻¹ ∈ GeneralLinear.upperUnipotent (n + 1) F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hcp)
    have hlast : Matrix.mulVec (projection p).val (lastColumn k) (Fin.last n) =
        Matrix.mulVec c.val (lastColumn k) (Fin.last n) := by
      have he : (projection p).val = (projection p * c⁻¹).val * c.val := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [he, ← Matrix.mulVec_mulVec]
      exact upperUnipotent_mulVec_last ⟨_, hu⟩ _
    have hψk : ψ.complex (Matrix.mulVec c.val (lastColumn k) (Fin.last n)) = 1 :=
      hCU (Set.mk_mem_prod (hCu hc) hkU)
    rw [hlast, hψk, one_mul]

theorem isOpen_leviExtendPeriods (hψ : IsOpen {t : F | ψ.complex t = 1})
    (h : GLCompactFunctions ψ n) :
    IsOpen (leviExtendPeriods ψ h : Set (mirabolic (n + 1) F)) :=
  Subgroup.isOpen_of_mem_nhds _ (leviExtendPeriods_mem_nhds ψ hψ h)

/-- The extension as a smooth induced function, with its open subgroup of periods. -/
def leviExtendSmooth (hψ : IsOpen {t : F | ψ.complex t = 1}) (h : GLCompactFunctions ψ n) :
    MirabolicSmoothFunctions ψ (n + 1) :=
  Induction.smoothFunctionOf _ _ (leviExtendFun ψ h) (leviExtendFun_covariance ψ h)
    ⟨leviExtendPeriods ψ h, isOpen_leviExtendPeriods ψ hψ h⟩ (fun k x => k.property x)

omit [T2Space F] [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F)] in
/-- The projected support of the extension lies in the image of the projected support of
the given function under the inverse quotient homeomorphism. -/
theorem quotientSupport_leviExtendFun_subset (h : GLCompactFunctions ψ n) :
    Induction.quotientSupport (Mirabolic.upperUnipotent (n + 1) F) (leviExtendFun ψ h) ⊆
      MirabolicQuotient.quotientHomeomorph.symm '' Induction.quotientSupport
        (GeneralLinear.upperUnipotent (n + 1) F)
        (Induction.eval _ (characterRepresentation (standardCharacter ψ n)) h.val) := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨Induction.quotientMap _ (projection p), ⟨projection p, right_ne_zero_of_mul hp, rfl⟩, ?_⟩
  rw [Homeomorph.symm_apply_eq]
  rfl

theorem isCompact_quotientSupport_leviExtendFun (hψ : IsOpen {t : F | ψ.complex t = 1})
    (h : GLCompactFunctions ψ n) :
    IsCompact (Induction.quotientSupport (Mirabolic.upperUnipotent (n + 1) F)
      (leviExtendFun ψ h)) :=
  (h.property.image MirabolicQuotient.quotientHomeomorph.symm.continuous).of_isClosed_subset
    (Induction.isClosed_quotientSupport _ _ (leviExtendSmooth ψ hψ h))
    (quotientSupport_leviExtendFun_subset ψ h)

/-- Extension from `GL_(n+1)` to the mirabolic group, as a linear map of compact models. -/
def leviExtension (hψ : IsOpen {t : F | ψ.complex t = 1}) :
    GLCompactFunctions ψ n →ₗ[ℂ] MirabolicCompactFunctions ψ (n + 1) where
  toFun h := ⟨leviExtendSmooth ψ hψ h, isCompact_quotientSupport_leviExtendFun ψ hψ h⟩
  map_add' _ _ := MirabolicWhittaker.compactFunctions_ext ψ fun _ => mul_add _ _ _
  map_smul' _ _ := MirabolicWhittaker.compactFunctions_ext ψ fun _ => mul_left_comm _ _ _

/-- Restriction along the Levi embedding is an equivalence from the compact mirabolic model,
restricted to `GL_(n+1)`, onto `c-Ind_N^(GL_(n+1)) θ`. -/
def leviEquiv (hψ : IsOpen {t : F | ψ.complex t = 1}) :
    Representation.Equiv ((mirabolicCompactInduced ψ (n + 1)).comp levi) (glCompactInduced ψ n) :=
  Representation.Equiv.mk
    { leviRestriction ψ with
      invFun := leviExtension ψ hψ
      left_inv := fun f => MirabolicWhittaker.compactFunctions_ext ψ fun p =>
        (eval_eq_lastColumn_mul_levi ψ f p).symm
      right_inv := fun h => glCompactFunctions_ext ψ fun a => by
        change ψ.complex (lastColumn (levi a) (Fin.last n)) * h.val.val.val (projection (levi a)) =
          h.val.val.val a
        rw [lastColumn_levi, projection_levi, Pi.zero_apply, AddChar.map_zero_eq_one, one_mul] }
    (fun g => LinearMap.ext fun f => glCompactFunctions_ext ψ fun a => by
      change mirabolicCompactEval ψ (n + 1) f (levi a * levi g) =
        mirabolicCompactEval ψ (n + 1) f (levi (a * g))
      rw [map_mul])

end Levi

section Adjacent

variable {F : Type uF} [Field F] {n : ℕ}

/-- At adjacent ranks the block embedding `g ↦ diag(g, 1)` is the Levi embedding. -/
theorem unequalRankEmbedding_adjacent (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankEmbedding (Nat.lt_add_one n) g = levi g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [unequalRankEmbedding_entry]
  have hl : ¬ (Fin.last (n + 1)).val < n + 1 := by simp
  induction i using Fin.lastCases with
  | last =>
    change _ = (levi g).val.val (Fin.last (n + 1)) j
    rw [levi_bottom]
    simp only [hl, ↓reduceDIte]
    exact if_congr eq_comm rfl rfl
  | cast i =>
    have hi : (Fin.castSucc i).val < n + 1 := i.isLt
    induction j using Fin.lastCases with
    | last =>
      change _ = (levi g).val.val i.castSucc (Fin.last (n + 1))
      rw [levi_last]
      simp only [hi, hl, ↓reduceDIte]
    | cast j =>
      have hj : (Fin.castSucc j).val < n + 1 := j.isLt
      change _ = (levi g).val.val i.castSucc j.castSucc
      rw [levi_first]
      simp only [hi, hj, ↓reduceDIte]
      rfl

end Adjacent

section Forms

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

/-- At adjacent ranks the unipotent covariance law is vacuous and the block embedding is the
Levi embedding, so the unequal-rank forms are the invariant forms on the restriction of the
compact model to `GL_(n+1)`, with covariance `|det|^(1/2 - s)`. -/
theorem forms_adjacent_eq (s : ℂ) :
    unequalRankMirabolicForms (Nat.lt_add_one n) ψ abv (mirabolicCompactInduced ψ (n + 1)) η s =
      InvariantBilinear.forms ((mirabolicCompactInduced ψ (n + 1)).comp levi) η
        (fun g => determinantWeight abv g ((((n + 1) - n : ℕ) : ℂ) / 2 - s)) := by
  ext B
  constructor
  · intro hB g f w
    have e := hB.1 g f w
    rw [unequalRankEmbedding_adjacent] at e
    exact e
  · intro hB
    refine ⟨fun g f w => ?_, fun u hu f w => ?_⟩
    · rw [unequalRankEmbedding_adjacent]
      exact hB g f w
    · have hu' : u ∈ unequalRankCovarianceSubgroup n (n + 1) F := hu
      rw [unequalRankCovarianceSubgroup_adjacent, Subgroup.mem_bot] at hu'
      subst hu'
      simp

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- The determinant character `|det|^c` is trivial on the upper unipotent group. -/
theorem determinantPower_unipotent (c : ℂ) (u : GeneralLinear.upperUnipotent (n + 1) F) :
    Shahidi.determinantPower abv (n + 1) c u = 1 := by
  apply Units.ext
  rw [Shahidi.determinantPower_apply, unipotent_det, map_one, Complex.ofReal_one,
    Complex.one_cpow, Units.val_one]

variable [T2Space F] [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F)]

/-- Adjacent-rank unequal-rank forms on the compact mirabolic model are the invariant forms
on `c-Ind_N^(GL_(n+1)) θ × η`. -/
def formsAdjacentEquiv (hψ : IsOpen {t : F | ψ.complex t = 1})
    (hopen : Shahidi.IsOpenNormOne abv) (s : ℂ) :
    unequalRankMirabolicForms (Nat.lt_add_one n) ψ abv (mirabolicCompactInduced ψ (n + 1)) η s ≃ₗ[ℂ]
      InvariantBilinear.forms (glCompactInduced ψ n) η (fun _ => (1 : ℂ)) :=
  (LinearEquiv.ofEq _ _ (forms_adjacent_eq ψ abv η s)).trans
    ((InvariantBilinear.equivLeft η _ (leviEquiv ψ hψ)).trans
      (Induction.formsCharacterShift _ _ η
        (Shahidi.determinantPower abv (n + 1) ((((n + 1) - n : ℕ) : ℂ) / 2 - s))
        (determinantPower_unipotent abv _)
        (Shahidi.isOpen_ker_determinantPower hopen (n + 1) _) _ _ (fun _ => (mul_one _).symm)))

end Forms

end UnequalRankCompactPairing

end Langlands.RankinSelberg
