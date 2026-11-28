import Langlands.Global.GMFamilyFieldDescent
import Langlands.LinearAlgebra.GMFamilySpecialDescent
import Langlands.LinearAlgebra.GMFamilyCentreReduction
import Langlands.LinearAlgebra.GMFamilyCoarseFamilies
import Langlands.LinearAlgebra.GMFamilySplittingMeasures
import Langlands.LinearAlgebra.GMFamilyWallWeights

/-! # The field-descent formula for a root set and a fine Levi flat -/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open Classical Module Submodule

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a₁ b : Submodule ℝ E}

/-- The field-descent formula of `HasFieldDescentFormula`, with the fine space `a₁` in place of
the whole space. -/
def HasFieldDescentFormulaIn (R : Finset E) (a₁ b : Submodule ℝ E) : Prop :=
  let z := coarseCenter R b
  ∀ c₁ : Finset E → StrongDual ℝ a₁ → ℂ, IsFamily R a₁ c₁ →
    (∀ S ∈ parabolics R b, ∃ S₁ ∈ parabolics R a₁, S ⊆ S₁) ∧
    (∀ S ∈ parabolics R b, ∀ S₁ ∈ parabolics R a₁, S ⊆ S₁ →
      ∀ Λ : StrongDual ℝ b,
        inducedFamily R b a₁ c₁ S Λ = c₁ S₁ (extendParam b a₁ Λ)) ∧
    IsFamily R b (inducedFamily R b a₁ c₁) ∧
    ∃ (c₀ : StrongDual ℝ b → ℂ) (cQ : Finset E → StrongDual ℝ a₁ → ℂ),
      IsSmoothThetaExtension R b c₀ (cM R b (inducedFamily R b a₁ c₁)) ∧
      (∀ Q ∈ faces R a₁,
        IsSmoothThetaExtension (leviRoots R Q) a₁ (cQ Q) (cQM R a₁ c₁ Q)) ∧
      ∀ ξ ∈ a₁ ⊓ bᗮ,
        (∀ L₁ ∈ leviSpaces R a₁, dDescent b z a₁ L₁ ≠ 0 →
          ∀ p : E, p ∈ L₁ ⊓ zᗮ → p - ξ ∈ b ⊓ zᗮ → IsRegular R L₁ p) →
        ∀ Λ : StrongDual ℝ b,
          c₀ Λ = ∑ L₁ ∈ leviSpaces R a₁, (dDescent b z a₁ L₁ : ℂ) *
            cQ (descentSection R b z ξ L₁) (extendParam b a₁ Λ)

theorem hasFieldDescentFormula_iff_top :
    HasFieldDescentFormula R b ↔ HasFieldDescentFormulaIn R ⊤ b := Iff.rfl

namespace FieldDescentRoots

open CentreReduction

omit [FiniteDimensional ℝ E] in
theorem le_of_mem_leviSpaces {L : Submodule ℝ E} (hL : L ∈ leviSpaces R a₁) : L ≤ a₁ := by
  obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hL
  exact inf_le_left

omit [FiniteDimensional ℝ E] in
theorem coarseCenter_le_of_mem_leviSpaces (ha₁ : IsLeviSpace R a₁) {L : Submodule ℝ E}
    (hL : L ∈ leviSpaces R a₁) : coarseCenter R b ≤ L :=
  inf_le_right.trans (central_le_of_mem_leviSpaces (centralSpace_le_of_levi ha₁) hL)

theorem mem_orthogonal_of_starProjection {K L : Submodule ℝ E} (hKL : K ≤ L) {x : E}
    (hx : x ∈ Kᗮ) : L.starProjection x ∈ Kᗮ := by
  intro w hw
  rw [← inner_starProjection_left_eq_right, starProjection_eq_self_iff.mpr (hKL hw)]
  exact inner_right_of_mem_orthogonal hw hx

/-- A root vanishing on a Levi flat `L` and on `b` vanishes on `a₁` when the descent coefficient
of `L` is nonzero: the restriction to `a₁` lies in both orthogonal complements. -/
theorem restrictedRoot_eq_zero_of_transverse (hb : b ≤ a₁) {L : Submodule ℝ E}
    (hzL : coarseCenter R b ≤ L) (hLa₁ : L ≤ a₁)
    (hd : dDescent b (coarseCenter R b) a₁ L ≠ 0) {r : E}
    (hrL : restrictedRoot L r = 0) (hrb : restrictedRoot b r = 0) : restrictedRoot a₁ r = 0 := by
  have hdis := ((measureFactor_ne_zero_iff
    (inf_le_inf_left _ (orthogonal_le (inf_le_left : coarseCenter R b ≤ b)))
    (inf_le_inf_left _ (orthogonal_le hzL))).mp hd).1
  have hrL' : r ∈ Lᗮ := (restrictedRoot_eq_zero_iff (a := L)).mp hrL
  have hrb' : r ∈ bᗮ := (restrictedRoot_eq_zero_iff (a := b)).mp hrb
  have hx : a₁.starProjection r = 0 := by
    have hmem : a₁.starProjection r ∈ (a₁ ⊓ bᗮ) ⊓ (a₁ ⊓ Lᗮ) :=
      ⟨⟨a₁.starProjection_apply_mem r, mem_orthogonal_of_starProjection hb hrb'⟩,
        a₁.starProjection_apply_mem r, mem_orthogonal_of_starProjection hLa₁ hrL'⟩
    rw [hdis.eq_bot] at hmem
    exact (Submodule.mem_bot ℝ).mp hmem
  exact Subtype.ext hx

/-! ### Offsets in general position -/

/-- The offsets whose descent point on `L` is orthogonal to `r`. -/
def badOffsets (b z L : Submodule ℝ E) (a₁ : Submodule ℝ E) (r : E) :
    Submodule ℝ (a₁ ⊓ bᗮ : Submodule ℝ E) where
  carrier := {ξ | ∃ p : E, p ∈ L ⊓ zᗮ ∧ p - (ξ : E) ∈ b ⊓ zᗮ ∧ ⟪r, p⟫ = 0}
  add_mem' := by
    rintro ξ η ⟨p, hp, hpb, hpr⟩ ⟨q, hq, hqb, hqr⟩
    refine ⟨p + q, add_mem hp hq, ?_, by rw [inner_add_right, hpr, hqr, add_zero]⟩
    have h := add_mem hpb hqb
    convert h using 1
    simp only [Submodule.coe_add]
    abel
  zero_mem' := ⟨0, zero_mem _, by simp, inner_zero_right r⟩
  smul_mem' := by
    rintro c ξ ⟨p, hp, hpb, hpr⟩
    refine ⟨c • p, smul_mem _ c hp, ?_, by rw [real_inner_smul_right, hpr, mul_zero]⟩
    have h := smul_mem _ c hpb
    convert h using 1
    simp only [Submodule.coe_smul, smul_sub]

theorem badOffsets_ne_top (ha₁ : IsLeviSpace R a₁) (hb : b ≤ a₁)
    {L : Submodule ℝ E} (hL : L ∈ leviSpaces R a₁)
    (hd : dDescent b (coarseCenter R b) a₁ L ≠ 0) {r : E} (hr : r ∈ R)
    (hrL : restrictedRoot L r ≠ 0) : badOffsets b (coarseCenter R b) L a₁ r ≠ ⊤ := by
  let z := coarseCenter R b
  have hzL : z ≤ L := coarseCenter_le_of_mem_leviSpaces ha₁ hL
  have hLa₁ : L ≤ a₁ := le_of_mem_leviSpaces hL
  have hza : z ≤ b := inf_le_left
  let q : E := L.starProjection r
  have hrz : r ∈ zᗮ := fun w hw => by
    rw [real_inner_comm]
    exact inner_central hr hw.2
  have hq : q ∈ L ⊓ zᗮ := ⟨L.starProjection_apply_mem r, mem_orthogonal_of_starProjection hzL hrz⟩
  have hqr : ⟪r, q⟫ ≠ 0 := by
    have h0 : q ≠ 0 := fun h => hrL (Subtype.ext h)
    have hsplit : ⟪r, q⟫ = ⟪q, q⟫ := by
      have h := L.starProjection_inner_eq_zero r q hq.1
      rw [inner_sub_left, sub_eq_zero] at h
      exact h
    rw [hsplit]
    exact inner_self_ne_zero.mpr h0
  have hbq : b.starProjection q ∈ b ⊓ zᗮ :=
    ⟨b.starProjection_apply_mem q, mem_orthogonal_of_starProjection hza hq.2⟩
  let ξ : (a₁ ⊓ bᗮ : Submodule ℝ E) := ⟨q - b.starProjection q,
    sub_mem (hLa₁ hq.1) (hb (b.starProjection_apply_mem q)), b.sub_starProjection_mem_orthogonal q⟩
  intro htop
  have hξ : ξ ∈ badOffsets b z L a₁ r := htop ▸ Submodule.mem_top
  obtain ⟨p, hp, hpb, hpr⟩ := hξ
  obtain ⟨_, _, hu⟩ := existsUnique_descentPoint hza hb hzL hLa₁ hd ξ.prop
  have hqξ : q - (ξ : E) ∈ b ⊓ zᗮ := by
    convert hbq using 1
    change q - (q - b.starProjection q) = _
    abel
  rw [hu p ⟨hp, hpb⟩, ← hu q ⟨hq, hqξ⟩] at hpr
  exact hqr hpr

/-- **Offsets in general position exist.** -/
theorem exists_generic_offset (ha₁ : IsLeviSpace R a₁) (hb : b ≤ a₁) :
    ∃ ξ ∈ a₁ ⊓ bᗮ, ∀ L ∈ leviSpaces R a₁, dDescent b (coarseCenter R b) a₁ L ≠ 0 →
      ∀ p : E, p ∈ L ⊓ (coarseCenter R b)ᗮ → p - ξ ∈ b ⊓ (coarseCenter R b)ᗮ →
        IsRegular R L p := by
  let z := coarseCenter R b
  let I := ((leviSpaces R a₁) ×ˢ R).filter
    (fun x => dDescent b z a₁ x.1 ≠ 0 ∧ restrictedRoot x.1 x.2 ≠ 0)
  let P (i : I) : Submodule ℝ (a₁ ⊓ bᗮ : Submodule ℝ E) := badOffsets b z i.1.1 a₁ i.1.2
  have hP (i : I) : P i ≠ ⊤ := by
    obtain ⟨hmem, hd, hr0⟩ := Finset.mem_filter.mp i.prop
    obtain ⟨hL, hr⟩ := Finset.mem_product.mp hmem
    exact badOffsets_ne_top ha₁ hb hL hd hr hr0
  obtain ⟨ξ, hξ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
  refine ⟨ξ, ξ.prop, fun L hL hd p hp hpb => ⟨hp.1, fun r hr hrL hpr => ?_⟩⟩
  let i : I := ⟨(L, r), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hL, hr⟩, hd, hrL⟩⟩
  exact hξ i ⟨p, hp, hpb, hpr⟩

/-! ### Nonvanishing denominators at the descent sections -/

/-- At the descent section of a transverse Levi flat, the denominators of the Levi component
do not vanish at the extension of a parameter in general position on `b`. -/
theorem theta_extendParam_ne_zero (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁) (hb : b ≤ a₁)
    {L : Submodule ℝ E} (hL : L ∈ leviSpaces R a₁)
    (hd : dDescent b (coarseCenter R b) a₁ L ≠ 0) {p : E} (hp : IsRegular R L p)
    {Λ : StrongDual ℝ b}
    (hΛ : ∀ r ∈ R, restrictedRoot b r ≠ 0 → Λ (restrictedRoot b r) ≠ 0) :
    ∀ S ∈ parabolics (leviRoots R (posSet R p)) a₁, theta a₁ S (extendParam b a₁ Λ) ≠ 0 := by
  have hLa₁ : L ≤ a₁ := le_of_mem_leviSpaces hL
  have hzL : coarseCenter R b ≤ L := coarseCenter_le_of_mem_leviSpaces ha₁ hL
  have hQ : posSet R p ∈ faces R a₁ := mem_faces_iff.mpr ⟨p, hLa₁ hp.1, rfl⟩
  intro S hS
  rw [theta_eq_product]
  refine mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr ?_)) ?_
  · have hli := simpleRoots_independent (isRootSet_leviRoots hR hQ)
      (isLeviSpace_leviRoots_of_mem_faces hR ha₁ hQ) hS
    exact ((gramVolume_pos_iff _).mpr (hli.map' a₁.subtype (ker_subtype _))).ne'
  · refine Finset.prod_ne_zero_iff.mpr fun u hu => ?_
    rw [ne_eq, parameterFactor_eq_zero]
    obtain ⟨r, hrS, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
    obtain ⟨h, hh, hSh⟩ := mem_parabolics_iff.mp hS
    have hSl : S ⊆ leviRoots R (posSet R p) := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    obtain ⟨hrR, hrp⟩ := (mem_leviRoots_posSet hR).mp (hSl hrS)
    have hra₁ : restrictedRoot a₁ r ≠ 0 := by
      intro h0
      have hpos : 0 < ⟪r, h⟫ := by
        rw [hSh] at hrS
        exact (mem_posSet.mp hrS).2
      rw [← inner_restrictedRoot hh.1, h0, Submodule.coe_zero, inner_zero_left] at hpos
      exact lt_irrefl _ hpos
    have hrL : restrictedRoot L r = 0 := by
      by_contra hne
      exact hp.2 r hrR hne hrp
    have hrb : restrictedRoot b r ≠ 0 := fun h0 =>
      hra₁ (restrictedRoot_eq_zero_of_transverse hb hzL hLa₁ hd hrL h0)
    change Λ (b.orthogonalProjectionOnto (restrictedRoot a₁ r : E)) ≠ 0
    rw [show b.orthogonalProjectionOnto (restrictedRoot a₁ r : E) = restrictedRoot b r from
      restrictedRoot_nested hb r]
    exact hΛ r hrR hrb

/-! ### The descent identity at parameters in general position -/

/-- **The descent identity at parameters in general position.** For a root set `R`, a Levi flat
`a₁`, a special subspace `b ⊆ a₁` compatible with the central space, an offset in general
position and a parameter on which no nonzero restricted root vanishes, the supplementary function
of the induced family is the sum over the Levi flats of the descent coefficients times any
functions agreeing with the relative supplementary functions where their denominators do not
vanish. The identity is reduced to `specialDescentFormula` for the enlargement of `b` by the
central directions orthogonal to it. -/
theorem cM_eq_descentSum (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁) (hb : b ≤ a₁)
    (hZ : IsCentreSplit R b) {m : E → ℝ} (hm : IsSpecialSubspace R b a₁ m)
    {c₁ : Finset E → StrongDual ℝ a₁ → ℂ} (hc₁ : IsFamily R a₁ c₁)
    {cQ : Finset E → StrongDual ℝ a₁ → ℂ}
    (hcQ : ∀ Q ∈ faces R a₁, ∀ Λ : StrongDual ℝ a₁,
      (∀ S ∈ parabolics (leviRoots R Q) a₁, theta a₁ S Λ ≠ 0) → cQ Q Λ = cQM R a₁ c₁ Q Λ)
    {ξ : E} (hξ : ξ ∈ a₁ ⊓ bᗮ) (hgen : IsGenericOffset R b (b ⊓ centralSpace R) a₁ ξ)
    {Λ : StrongDual ℝ b} (hΛ : ∀ r ∈ R, restrictedRoot b r ≠ 0 → Λ (restrictedRoot b r) ≠ 0) :
    cM R b (inducedFamily R b a₁ c₁) Λ =
      ∑ L ∈ leviSpaces R a₁, (dDescent b (b ⊓ centralSpace R) a₁ L : ℂ) *
        cQ (descentSection R b (b ⊓ centralSpace R) ξ L) (extendParam b a₁ Λ) := by
  have hZa₁ := centralSpace_le_of_levi ha₁
  have hgen' := (isGenericOffset_hull_iff hZ hZa₁ hξ.2).mp hgen
  have key := specialDescentFormula hR ha₁ (hull_le hb hZa₁) (central_le_hull hZ)
    (isSpecialSubspace_hull hm) c₁ hc₁ (offset_hull hZ hZa₁ hξ) hgen'
    (extendParam b (hull R b) Λ) (generic_hull hΛ)
  rw [← cM_hull c₁ Λ, key]
  apply Finset.sum_congr rfl
  intro L hL
  have hZL := central_le_of_mem_leviSpaces hZa₁ hL
  have hLa₁ := le_of_mem_leviSpaces hL
  rw [extendParam_extendParam le_hull, ← dDescent_hull hZ hZa₁ hZL]
  by_cases hd : dDescent b (b ⊓ centralSpace R) a₁ L = 0
  · simp [hd]
  · congr 1
    rw [← descentSection_hull hZ hb hZa₁ hZL hLa₁ (by rwa [← dDescent_hull hZ hZa₁ hZL]) hξ]
    have hzL : b ⊓ centralSpace R ≤ L := inf_le_right.trans hZL
    obtain ⟨p, ⟨hpL, hpA⟩, -⟩ := existsUnique_descentPoint inf_le_left hb hzL hLa₁ hd hξ
    rw [descentSection_eq_posSet inf_le_left hb hzL hLa₁ hd hξ hpL hpA]
    exact (hcQ _ (mem_faces_iff.mpr ⟨p, hLa₁ hpL.1, rfl⟩) _
      (theta_extendParam_ne_zero hR ha₁ hb hL hd (hgen L hL hd p hpL hpA) hΛ)).symm

/-! ### Density and continuity -/

/-- The parameters on which no nonzero restricted root vanishes. -/
def genericParams (R : Finset E) (b : Submodule ℝ E) : Set (StrongDual ℝ b) :=
  {Λ | ∀ r ∈ R, restrictedRoot b r ≠ 0 → Λ (restrictedRoot b r) ≠ 0}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A finite intersection of dense open sets is dense. -/
theorem dense_biInter_finset_of_isOpen {X ι : Type*} [TopologicalSpace X] {s : Finset ι}
    {f : ι → Set X} (ho : ∀ i ∈ s, IsOpen (f i)) (hd : ∀ i ∈ s, Dense (f i)) :
    Dense (⋂ i ∈ (s : Set ι), f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.coe_insert, Set.biInter_insert]
    exact (hd a (Finset.mem_insert_self a s)).inter_of_isOpen_left
      (ih (fun i hi => ho i (Finset.mem_insert_of_mem hi))
        (fun i hi => hd i (Finset.mem_insert_of_mem hi)))
      (ho a (Finset.mem_insert_self a s))

theorem dense_genericParams : Dense (genericParams R b) := by
  have he : genericParams R b = ⋂ r ∈ ((R.filter fun r => restrictedRoot b r ≠ 0 : Finset E) : Set E),
      {Λ : StrongDual ℝ b | Λ (restrictedRoot b r) ≠ 0} := by
    ext Λ
    simp [genericParams]
  rw [he]
  apply dense_biInter_finset_of_isOpen
  · intro r _
    exact isOpen_ne_fun (ContinuousLinearMap.apply ℝ ℝ (restrictedRoot b r)).continuous
      continuous_const
  · intro r hr
    have hr0 : restrictedRoot b r ≠ 0 := (Finset.mem_filter.mp hr).2
    let f : StrongDual ℝ b →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (restrictedRoot b r)
    have hker : LinearMap.ker (f : StrongDual ℝ b →ₗ[ℝ] ℝ) ≠ ⊤ := by
      intro htop
      have h : InnerProductSpace.toDual ℝ b (restrictedRoot b r) ∈
          LinearMap.ker (f : StrongDual ℝ b →ₗ[ℝ] ℝ) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at h
      change InnerProductSpace.toDual ℝ b (restrictedRoot b r) (restrictedRoot b r) = 0 at h
      rw [InnerProductSpace.toDual_apply_apply] at h
      exact inner_self_ne_zero.mpr hr0 h
    have hset : {Λ : StrongDual ℝ b | Λ (restrictedRoot b r) ≠ 0} =
        ((LinearMap.ker (f : StrongDual ℝ b →ₗ[ℝ] ℝ) : Set (StrongDual ℝ b)))ᶜ := by
      ext Λ
      simp [f]
    rw [hset, ← interior_eq_empty_iff_dense_compl]
    by_contra hne
    exact hker (Submodule.eq_top_of_nonempty_interior' _ (Set.nonempty_iff_ne_empty.mpr hne))

theorem continuous_theta (S : Finset E) : Continuous (theta b S) := by
  have h : theta b S = fun Λ => ((gramVolume (fun i : simpleRoots b S => ((i : b) : E)) : ℝ) : ℂ)⁻¹ *
      ∏ u ∈ simpleRoots b S, parameterFactor u Λ := funext (theta_eq_product S)
  rw [h]
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro u _
  unfold parameterFactor
  exact (contDiff_imaginaryFactor _).continuous

/-- The parameters at which no denominator vanishes. -/
def regularParams (R : Finset E) (b : Submodule ℝ E) : Set (StrongDual ℝ b) :=
  {Λ | ∀ S ∈ parabolics R b, theta b S Λ ≠ 0}

theorem isOpen_regularParams : IsOpen (regularParams R b) := by
  have he : regularParams R b = ⋂ S ∈ parabolics R b, {Λ : StrongDual ℝ b | theta b S Λ ≠ 0} := by
    ext Λ
    simp [regularParams]
  rw [he]
  exact isOpen_biInter_finset fun S _ => isOpen_ne_fun (continuous_theta S) continuous_const

theorem continuousOn_cM {c : Finset E → StrongDual ℝ b → ℂ}
    (hc : ∀ S ∈ parabolics R b, Continuous (c S)) :
    ContinuousOn (cM R b c) (regularParams R b) := by
  unfold cM
  apply continuousOn_finsetSum
  intro S hS
  exact (hc S hS).continuousOn.mul ((continuous_theta S).continuousOn.inv₀ fun Λ hΛ => hΛ S hS)

end FieldDescentRoots

open FieldDescentRoots CentreReduction in
/-- **The field-descent formula for a root set.** For a root set `R`, a Levi flat `a₁` and a
subspace `b ⊆ a₁` which is special for positive weights and preserved by the orthogonal
projection to the central space, the descent formula of Arthur 2005, Lemma 17.5, holds with
smooth supplementary functions at every parameter. -/
theorem hasFieldDescentFormulaIn (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁) (hb : b ≤ a₁)
    (hZ : IsCentreSplit R b) {m : E → ℝ} (hm : IsSpecialSubspace R b a₁ m) :
    HasFieldDescentFormulaIn R a₁ b := by
  dsimp only [HasFieldDescentFormulaIn]
  intro c₁ hc₁
  have hind := isFamily_inducedFamily hR hb hc₁
  refine ⟨fun S hS => exists_fine_parabolic_extension hb hS,
    fun S hS S₁ hS₁ hSS₁ Λ => inducedFamily_eq_of_extension hR hb hc₁ hS hS₁ hSS₁ Λ, hind, ?_⟩
  obtain ⟨cQ, hcQs, hcQ⟩ := exists_smooth_cQM hR ha₁ hc₁
  obtain ⟨ξ₀, hξ₀, hgen₀⟩ := exists_generic_offset ha₁ hb
  let rhs (ξ : E) (Λ : StrongDual ℝ b) : ℂ :=
    ∑ L ∈ leviSpaces R a₁, (dDescent b (coarseCenter R b) a₁ L : ℂ) *
      cQ (descentSection R b (coarseCenter R b) ξ L) (extendParam b a₁ Λ)
  have hrhs (ξ : E) : ContDiff ℝ ∞ (rhs ξ) :=
    ContDiff.sum fun L _ => contDiff_const.mul ((hcQs _).comp (contDiff_extendParam b a₁))
  have hgenId (ξ : E) (hξ : ξ ∈ a₁ ⊓ bᗮ) (hg : IsGenericOffset R b (b ⊓ centralSpace R) a₁ ξ) :
      Set.EqOn (rhs ξ) (cM R b (inducedFamily R b a₁ c₁)) (genericParams R b) :=
    fun Λ hΛ => (cM_eq_descentSum hR ha₁ hb hZ hm hc₁ hcQ hξ hg hΛ).symm
  refine ⟨rhs ξ₀, cQ, ⟨hrhs ξ₀, fun Λ hΛ => ?_⟩, fun Q hQ => ⟨hcQs Q, hcQ Q hQ⟩,
    fun ξ hξ hg Λ => ?_⟩
  · have heq : Set.EqOn (rhs ξ₀) (cM R b (inducedFamily R b a₁ c₁))
        (regularParams R b ∩ genericParams R b) := fun Λ' hΛ' => hgenId ξ₀ hξ₀ hgen₀ hΛ'.2
    exact heq.of_subset_closure (hrhs ξ₀).continuous.continuousOn
      (continuousOn_cM fun S hS => (hind.1 S hS).continuous) Set.inter_subset_left
      (dense_genericParams.open_subset_closure_inter isOpen_regularParams) hΛ
  · have h := Continuous.ext_on dense_genericParams (hrhs ξ₀).continuous (hrhs ξ).continuous
      (fun Λ' hΛ' => (hgenId ξ₀ hξ₀ hgen₀ hΛ').trans (hgenId ξ hξ hg hΛ').symm)
    exact congrFun h Λ

end Langlands.GMFamily
