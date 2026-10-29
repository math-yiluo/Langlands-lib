import Langlands.Representation.RankinSelberg.UnequalRankBilinearForms
import Langlands.Representation.Whittaker.MirabolicCompactWhittakerUniqueness

/-!
# Rank reduction for unequal-rank compact mirabolic pairings

For `n < m`, composing with restriction along the successor embedding
`P_m → P_(m+1)` identifies the unequal-rank covariant forms on the compact
mirabolic model of rank `m + 1` at exponent `s` with those of rank `m` at
exponent `s - 1/2`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear GeneralLinear.Mirabolic Topology

universe uF uW

namespace UnequalRankCompactPairing

section Algebra

variable {F : Type uF} [Field F] {n m : ℕ}

/-- The block embedding of rank `m + 1` is the successor of the block embedding of rank `m`. -/
theorem unequalRankEmbedding_succ (hnm : n < m) (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankEmbedding (Nat.lt_add_one_of_lt hnm) g = successor (unequalRankEmbedding hnm g) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [unequalRankEmbedding_entry]
  induction i using Fin.lastCases with
  | last =>
    change _ = (levi (unequalRankEmbedding hnm g).val).val.val (Fin.last (m + 1)) j
    rw [levi_bottom]
    have h : ¬ (Fin.last (m + 1)).val < n + 1 := by simp; omega
    simp only [h, ↓reduceDIte]
    exact if_congr eq_comm rfl rfl
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [successor_last]
      have h : ¬ (Fin.last (m + 1)).val < n + 1 := by simp; omega
      simp only [h, ↓reduceDIte, dite_eq_ite]
      split_ifs with h1 h2
      · rfl
      · exact absurd h2 (Fin.castSucc_ne_last i)
      · rfl
    | cast j =>
      rw [successor_first, unequalRankEmbedding_entry]
      simp only [Fin.val_castSucc, Fin.castSucc_inj]

/-- The exponent bookkeeping of one reduction step. -/
theorem weight_succ (hnm : n < m) (s : ℂ) :
    (((m + 1 - n : ℕ) : ℂ) / 2 - s) = ((m - n : ℕ) : ℂ) / 2 - (s - 1 / 2) := by
  rw [show m + 1 - n = (m - n) + 1 by omega]
  push_cast
  ring

/-- Radical matrices of rank `m + 2` lie in `U_(n+2,m+2)` when `n < m`. -/
theorem isCovarianceUnipotent_radical (hnm : n < m) (x : Fin (m + 1) → F) :
    IsUnequalRankCovarianceUnipotent n (radicalToUpperUnipotent (radicalElement x)) := by
  intro i j _ hj
  have hj' : j ≠ Fin.last (m + 1) := by
    intro h
    rw [h, Fin.val_last] at hj
    omega
  obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hj'
  exact (radicalElement x).property i k

/-- The lift of an upper unipotent matrix is upper unipotent in the mirabolic group. -/
theorem unequalRankUnipotentLift_mem {r : ℕ} (u : GeneralLinear.upperUnipotent (r + 1) F) :
    unequalRankUnipotentLift u ∈ Mirabolic.upperUnipotent r F :=
  u.property

/-- The successor of an upper unipotent matrix of rank `m + 1`. -/
def successorUnipotent (u : GeneralLinear.upperUnipotent (m + 1) F) :
    GeneralLinear.upperUnipotent (m + 2) F :=
  upperUnipotentEquiv ⟨successor (unequalRankUnipotentLift u),
    MirabolicWhittaker.successor_mem_upperUnipotent (unequalRankUnipotentLift_mem u)⟩

/-- The mirabolic lift of `successorUnipotent u` is the successor of the lift of `u`. -/
theorem unequalRankUnipotentLift_successorUnipotent (u : GeneralLinear.upperUnipotent (m + 1) F) :
    unequalRankUnipotentLift (successorUnipotent u) = successor (unequalRankUnipotentLift u) :=
  rfl

/-- An upper unipotent matrix of rank `m + 2` as an element of the plus subgroup. -/
def plusUnipotent (u : GeneralLinear.upperUnipotent (m + 2) F) : plusSubgroup m F :=
  ⟨unequalRankUnipotentLift u,
    MirabolicWhittaker.upperUnipotent_le_plusSubgroup (unequalRankUnipotentLift_mem u)⟩

/-- The plus projection of an upper unipotent matrix of rank `m + 2`: its leading
`(m + 1)`-square block. -/
def projectionUnipotent (u : GeneralLinear.upperUnipotent (m + 2) F) :
    GeneralLinear.upperUnipotent (m + 1) F :=
  upperUnipotentEquiv ⟨plusProjection (plusUnipotent u),
    MirabolicWhittaker.plusProjection_mem_upperUnipotent _ (unequalRankUnipotentLift_mem u)⟩

/-- The mirabolic lift of `projectionUnipotent u` is the plus projection. -/
theorem unequalRankUnipotentLift_projectionUnipotent (u : GeneralLinear.upperUnipotent (m + 2) F) :
    unequalRankUnipotentLift (projectionUnipotent u) = plusProjection (plusUnipotent u) :=
  rfl

/-- Successors of matrices in `U_(n+2,m+1)` lie in `U_(n+2,m+2)`. -/
theorem isCovarianceUnipotent_successor (hnm : n < m)
    {u : GeneralLinear.upperUnipotent (m + 1) F} (hu : IsUnequalRankCovarianceUnipotent n u) :
    IsUnequalRankCovarianceUnipotent n (successorUnipotent u) := by
  intro i j hi hj
  have hi' : i ≠ Fin.last (m + 1) := by
    intro h
    rw [h, Fin.val_last] at hi
    omega
  have hj' : j ≠ Fin.last (m + 1) := by
    intro h
    rw [h, Fin.val_last] at hj
    omega
  obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.mpr hi'
  obtain ⟨b, rfl⟩ := Fin.exists_castSucc_eq.mpr hj'
  change (successor (unequalRankUnipotentLift u)).val.val a.castSucc b.castSucc = _
  rw [successor_first]
  simpa using hu a b hi hj

/-- Plus projections of matrices in `U_(n+2,m+2)` lie in `U_(n+2,m+1)`. -/
theorem isCovarianceUnipotent_projectionUnipotent {u : GeneralLinear.upperUnipotent (m + 2) F}
    (hu : IsUnequalRankCovarianceUnipotent n u) :
    IsUnequalRankCovarianceUnipotent n (projectionUnipotent u) := by
  intro i j hi hj
  change (plusProjection (plusUnipotent u)).val.val i j = _
  rw [plusProjection_apply]
  have h := hu i.castSucc j.castSucc hi hj
  simp only [Fin.castSucc_inj] at h
  exact h

end Algebra

section Kernel

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {m : ℕ}
variable (ψ : UnitaryAdditiveCharacter F)

/-- Covariance of a functional under right translation by the radical, through
the final coordinate only. -/
def IsRadicalCovariant (ℓ : Module.Dual ℂ (MirabolicCompactFunctions ψ (m + 1))) : Prop :=
  ∀ (x : Fin (m + 1) → F) (f : MirabolicCompactFunctions ψ (m + 1)),
    ℓ (mirabolicCompactInduced ψ (m + 1) (radicalElement x).val f) =
      ψ.complex (x (Fin.last m)) * ℓ f

/-- A radical-covariant functional vanishes on every function whose nonzero values
sit where some character of the row takes a value different from its value at the
final standard row. -/
theorem functional_eq_zero_of_finset {ℓ : Module.Dual ℂ (MirabolicCompactFunctions ψ (m + 1))}
    (hℓ : IsRadicalCovariant ψ ℓ) (S : Finset ((Fin (m + 1) → F) × ℂ))
    (hS : ∀ p ∈ S, p.2 ≠ ψ.complex (p.1 (Fin.last m))) :
    ∀ h : MirabolicCompactFunctions ψ (m + 1),
      (∀ g, mirabolicCompactEval ψ (m + 1) h g ≠ 0 →
        ∃ p ∈ S, ψ.complex (MirabolicWhittaker.rowOf g ⬝ᵥ p.1) = p.2) → ℓ h = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro h hh
    have h0 : h = 0 := MirabolicWhittaker.compactFunctions_ext ψ fun g => by
      by_contra hg
      obtain ⟨p, hp, -⟩ := hh g hg
      exact absurd hp (Finset.notMem_empty p)
    rw [h0, map_zero]
  | insert p S _ ih =>
    intro h hh
    let h' := mirabolicCompactInduced ψ (m + 1) (radicalElement p.1).val h - p.2 • h
    have hval : ∀ g, mirabolicCompactEval ψ (m + 1) h' g =
        (ψ.complex (MirabolicWhittaker.rowOf g ⬝ᵥ p.1) - p.2) *
          mirabolicCompactEval ψ (m + 1) h g := by
      intro g
      change mirabolicCompactEval ψ (m + 1)
          (mirabolicCompactInduced ψ (m + 1) (radicalElement p.1).val h) g -
          p.2 * mirabolicCompactEval ψ (m + 1) h g = _
      rw [mirabolicCompactEval_translate, MirabolicWhittaker.eval_mul_radicalElement]
      ring
    have h0 : ℓ h' = 0 := by
      refine ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)) h' fun g hg => ?_
      rw [hval] at hg
      obtain ⟨q, hq, hqg⟩ := hh g (right_ne_zero_of_mul hg)
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact absurd (sub_eq_zero.mpr hqg) (left_ne_zero_of_mul hg)
      · exact ⟨q, hq, hqg⟩
    have hℓh' : ℓ h' = (ψ.complex (p.1 (Fin.last m)) - p.2) * ℓ h := by
      simp only [h', map_sub, map_smul, hℓ p.1 h, smul_eq_mul]
      ring
    rw [hℓh'] at h0
    exact (mul_eq_zero.mp h0).resolve_left
      (sub_ne_zero.mpr (hS p (Finset.mem_insert_self p S)).symm)

end Kernel

section KernelVanishing

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  {m : ℕ} [LocallyCompactSpace (Langlands.GeneralLinear (m + 2) F)]
variable (ψ : UnitaryAdditiveCharacter F)

/-- Every radical-covariant functional of rank `m + 2` vanishes on the kernel of
restriction, provided the kernel of `ψ` is open. -/
theorem functional_eq_zero_of_restriction_eq_zero (hψ : IsOpen {t : F | ψ.complex t = 1})
    {ℓ : Module.Dual ℂ (MirabolicCompactFunctions ψ (m + 1))}
    (hℓ : IsRadicalCovariant ψ ℓ) {f : MirabolicCompactFunctions ψ (m + 1)}
    (hf : MirabolicWhittaker.restriction ψ f = 0) : ℓ f = 0 := by
  classical
  obtain ⟨K, hK⟩ := MirabolicWhittaker.exists_openSubgroup_eval_mul ψ f
  let J := K.comap levi continuous_levi
  let O := RankinSelberg.lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F))
  have hO : IsOpen O := RankinSelberg.isOpen_lastRow_image J.toSubgroup J.isOpen
  have he : RankinSelberg.lastRow (1 : Langlands.GeneralLinear (m + 1) F) ∈ O :=
    ⟨1, J.one_mem, rfl⟩
  have : LocallyCompactSpace (mirabolic (m + 1) F) := Mirabolic.locallyCompactSpace
  obtain ⟨C, hC, hCimg⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (Mirabolic.upperUnipotent (m + 1) F) Mirabolic.upperUnipotent_isClosed f.property
  have hr : Continuous (MirabolicWhittaker.rowOf (n := m) (F := F)) :=
    RankinSelberg.continuous_lastRow.comp continuous_projection
  let S := MirabolicWhittaker.rowOf '' C \ O
  have hSc : IsCompact S := (hC.image hr).diff hO
  have hx : ∀ y ∈ S, ∃ x : Fin (m + 1) → F,
      ψ.complex (y ⬝ᵥ x) ≠ ψ.complex (x (Fin.last m)) := by
    intro y hy
    have hne : y - RankinSelberg.lastRow (1 : Langlands.GeneralLinear (m + 1) F) ≠ 0 := by
      intro h
      exact hy.2 ((sub_eq_zero.mp h) ▸ he)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    obtain ⟨t, ht⟩ := MirabolicWhittaker.exists_complex_ne_one ψ
    refine ⟨Pi.single j (t / (y - RankinSelberg.lastRow
      (1 : Langlands.GeneralLinear (m + 1) F)) j), ?_⟩
    rw [← MirabolicWhittaker.lastRow_one_dotProduct (Pi.single j (t / (y - RankinSelberg.lastRow
      (1 : Langlands.GeneralLinear (m + 1) F)) j)), Ne, MirabolicWhittaker.complex_eq_iff,
      ← sub_dotProduct, dotProduct_single, mul_div_cancel₀ _ hj]
    exact ht
  choose! X hX using hx
  have hU : ∀ y ∈ S, {z | ψ.complex (z ⬝ᵥ X y) = ψ.complex (y ⬝ᵥ X y)} ∈ 𝓝 y := by
    intro y _
    have hset : {z | ψ.complex (z ⬝ᵥ X y) = ψ.complex (y ⬝ᵥ X y)} =
        (fun z => (z - y) ⬝ᵥ X y) ⁻¹' {t : F | ψ.complex t = 1} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, MirabolicWhittaker.complex_eq_iff,
        sub_dotProduct]
    rw [hset]
    refine (hψ.preimage ((continuous_id.sub continuous_const).dotProduct
      continuous_const)).mem_nhds ?_
    simp
  obtain ⟨t, htS, htcover⟩ := hSc.elim_nhds_subcover _ hU
  refine functional_eq_zero_of_finset ψ hℓ (t.image fun y => (X y, ψ.complex (y ⬝ᵥ X y)))
    ?_ f ?_
  · simp only [Finset.mem_image]
    rintro _ ⟨y, hy, rfl⟩
    exact hX y (htS y hy)
  · intro g hg
    have hmem : Induction.quotientMap _ g ∈ Induction.quotientSupport
        (Mirabolic.upperUnipotent (m + 1) F)
        (Induction.eval _ (mirabolicCharacterRepresentation ψ (m + 1)) f.val) :=
      ⟨_, hg, rfl⟩
    rw [← hCimg] at hmem
    obtain ⟨c, hc, hcg⟩ := hmem
    have hu : g * c⁻¹ ∈ Mirabolic.upperUnipotent (m + 1) F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hcg)
    have hrow : MirabolicWhittaker.rowOf g = MirabolicWhittaker.rowOf c := by
      have := MirabolicWhittaker.rowOf_upperUnipotent_mul ⟨g * c⁻¹, hu⟩ c
      rwa [inv_mul_cancel_right] at this
    have hgS : MirabolicWhittaker.rowOf g ∈ S := by
      refine ⟨⟨c, hc, hrow.symm⟩, fun hO' => hg ?_⟩
      exact MirabolicWhittaker.eval_eq_zero_of_rowOf_mem ψ hf hK hO'
    obtain ⟨y, hy, hyg⟩ := Set.mem_iUnion₂.mp (htcover hgS)
    exact ⟨_, Finset.mem_image_of_mem _ hy, hyg⟩

end KernelVanishing

section Characters

variable {F : Type uF} [Field F] [TopologicalSpace F] {m : ℕ}
variable (ψ : UnitaryAdditiveCharacter F)

/-- The standard character of rank `m + 2` splits as the final adjacent entry times the
standard character of the plus projection. -/
theorem standardCharacter_succ (u : GeneralLinear.upperUnipotent (m + 2) F) :
    (standardCharacter ψ (m + 1) u : ℂ) =
      ψ.complex (lastColumn (unequalRankUnipotentLift u) (Fin.last m)) *
        (standardCharacter ψ m (projectionUnipotent u) : ℂ) :=
  MirabolicWhittaker.mirabolicCharacter_succ ψ (upperUnipotentEquiv.symm u)

/-- The successor embedding preserves the standard character. -/
theorem standardCharacter_successor (u : GeneralLinear.upperUnipotent (m + 1) F) :
    (standardCharacter ψ (m + 1) (successorUnipotent u) : ℂ) = standardCharacter ψ m u :=
  congrArg _ (MirabolicWhittaker.mirabolicCharacter_successor ψ (upperUnipotentEquiv.symm u))

/-- On the radical only the final coordinate is seen by the standard character. -/
theorem standardCharacter_radicalElement (x : Fin (m + 1) → F) :
    (standardCharacter ψ (m + 1) (radicalToUpperUnipotent (radicalElement x)) : ℂ) =
      ψ.complex (x (Fin.last m)) :=
  MirabolicWhittaker.mirabolicCharacter_radicalElement ψ x

end Characters

section Translation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {m : ℕ}
variable (ψ : UnitaryAdditiveCharacter F)

/-- Translation by a product is the composite of the translations. -/
theorem induced_mul_apply (a b : mirabolic (m + 1) F) (f : MirabolicCompactFunctions ψ (m + 1)) :
    mirabolicCompactInduced ψ (m + 1) (a * b) f =
      mirabolicCompactInduced ψ (m + 1) a (mirabolicCompactInduced ψ (m + 1) b f) := by
  rw [map_mul]
  rfl

end Translation

section Restriction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] {n m : ℕ}
  [LocallyCompactSpace (Langlands.GeneralLinear (m + 2) F)]
variable (ψ : UnitaryAdditiveCharacter F)

/-- Restriction intertwines the block embeddings of ranks `m + 1` and `m`. -/
theorem restriction_unequalRankEmbedding (hnm : n < m) (g : Langlands.GeneralLinear (n + 1) F)
    (f : MirabolicCompactFunctions ψ (m + 1)) :
    MirabolicWhittaker.restriction ψ
        (mirabolicCompactInduced ψ (m + 1) (unequalRankEmbedding (Nat.lt_add_one_of_lt hnm) g) f) =
      mirabolicCompactInduced ψ m (unequalRankEmbedding hnm g)
        (MirabolicWhittaker.restriction ψ f) := by
  rw [unequalRankEmbedding_succ, MirabolicWhittaker.restriction_translate]

/-- Restriction turns radical translation into multiplication by the character of
the final coordinate. -/
theorem restriction_radicalElement (x : Fin (m + 1) → F)
    (f : MirabolicCompactFunctions ψ (m + 1)) :
    MirabolicWhittaker.restriction ψ
        (mirabolicCompactInduced ψ (m + 1) (radicalElement x).val f) =
      ψ.complex (x (Fin.last m)) • MirabolicWhittaker.restriction ψ f :=
  MirabolicWhittaker.compactFunctions_ext ψ fun g => by
    change mirabolicCompactEval ψ (m + 1)
        (mirabolicCompactInduced ψ (m + 1) (radicalElement x).val f) (successor g) =
      ψ.complex (x (Fin.last m)) * mirabolicCompactEval ψ (m + 1) f (successor g)
    rw [mirabolicCompactEval_translate, MirabolicWhittaker.eval_mul_radicalElement,
      MirabolicWhittaker.rowOf, projection_successor,
      (RankinSelberg.mem_mirabolic_iff_lastRow _).mp g.property,
      MirabolicWhittaker.lastRow_one_dotProduct]

/-- Restriction of a translate by the plus subgroup: the radical part contributes a
scalar and the plus projection acts on the restriction. -/
theorem restriction_plus (p : plusSubgroup m F) (f : MirabolicCompactFunctions ψ (m + 1)) :
    MirabolicWhittaker.restriction ψ (mirabolicCompactInduced ψ (m + 1) p.val f) =
      ψ.complex (lastColumn p.val (Fin.last m)) •
        mirabolicCompactInduced ψ m (plusProjection p) (MirabolicWhittaker.restriction ψ f) := by
  have h1 := congrArg
    (fun g => MirabolicWhittaker.restriction ψ (mirabolicCompactInduced ψ (m + 1) g f))
    (plus_eq_radicalElement_mul_successor p)
  refine h1.trans ?_
  rw [induced_mul_apply, restriction_radicalElement]
  exact congrArg (fun h => ψ.complex (lastColumn p.val (Fin.last m)) • h)
    (MirabolicWhittaker.restriction_translate ψ f (plusProjection p))

end Restriction

section Forms

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] {n m : ℕ}
  [LocallyCompactSpace (Langlands.GeneralLinear (m + 2) F)]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

/-- Pulling back along restriction carries covariant forms of rank `m` at `s - 1/2`
to covariant forms of rank `m + 1` at `s`. -/
theorem comp_restriction_mem (hnm : n < m) (s : ℂ)
    {B' : MirabolicCompactFunctions ψ m →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hB' : B' ∈ unequalRankMirabolicForms hnm ψ abv (mirabolicCompactInduced ψ m) η (s - 1 / 2)) :
    B'.comp (MirabolicWhittaker.restriction ψ) ∈ unequalRankMirabolicForms
        (Nat.lt_add_one_of_lt hnm) ψ abv (mirabolicCompactInduced ψ (m + 1)) η s := by
  refine ⟨fun g f w => ?_, fun u hu f w => ?_⟩
  · have e := hB'.1 g (MirabolicWhittaker.restriction ψ f) w
    rw [← weight_succ hnm] at e
    exact (congrArg (fun x => B' x (η g w)) (restriction_unequalRankEmbedding ψ hnm g f)).trans e
  · have e := hB'.2 (projectionUnipotent u) (isCovarianceUnipotent_projectionUnipotent hu)
      (MirabolicWhittaker.restriction ψ f) w
    calc B' (MirabolicWhittaker.restriction ψ
          (mirabolicCompactInduced ψ (m + 1) (unequalRankUnipotentLift u) f)) w
        = B' (ψ.complex (lastColumn (unequalRankUnipotentLift u) (Fin.last m)) •
            mirabolicCompactInduced ψ m (plusProjection (plusUnipotent u))
              (MirabolicWhittaker.restriction ψ f)) w :=
          congrArg (fun x => B' x w) (restriction_plus ψ (plusUnipotent u) f)
      _ = ψ.complex (lastColumn (unequalRankUnipotentLift u) (Fin.last m)) *
            B' (mirabolicCompactInduced ψ m (unequalRankUnipotentLift (projectionUnipotent u))
              (MirabolicWhittaker.restriction ψ f)) w :=
          LinearMap.map_smul₂ _ _ _ _
      _ = ψ.complex (lastColumn (unequalRankUnipotentLift u) (Fin.last m)) *
            ((standardCharacter ψ m (projectionUnipotent u) : ℂ) *
              B' (MirabolicWhittaker.restriction ψ f) w) :=
          congrArg (fun z => ψ.complex (lastColumn (unequalRankUnipotentLift u) (Fin.last m)) * z) e
      _ = (standardCharacter ψ (m + 1) u : ℂ) * B' (MirabolicWhittaker.restriction ψ f) w := by
          rw [standardCharacter_succ ψ u, mul_assoc]

/-- Conversely, when restriction is surjective, a form of rank `m` whose pullback is
covariant of rank `m + 1` at `s` is itself covariant at `s - 1/2`. -/
theorem mem_of_comp_restriction_mem (hnm : n < m)
    (hR : Function.Surjective (MirabolicWhittaker.restriction ψ (F := F) (n := m))) (s : ℂ)
    {B' : MirabolicCompactFunctions ψ m →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hB : B'.comp (MirabolicWhittaker.restriction ψ) ∈ unequalRankMirabolicForms
        (Nat.lt_add_one_of_lt hnm) ψ abv (mirabolicCompactInduced ψ (m + 1)) η s) :
    B' ∈ unequalRankMirabolicForms hnm ψ abv (mirabolicCompactInduced ψ m) η (s - 1 / 2) := by
  refine ⟨fun g h w => ?_, fun u hu h w => ?_⟩
  · obtain ⟨f, rfl⟩ := hR h
    have e := hB.1 g f w
    simp only [LinearMap.comp_apply] at e
    rw [weight_succ hnm] at e
    exact (congrArg (fun x => B' x (η g w)) (restriction_unequalRankEmbedding ψ hnm g f)).symm.trans e
  · have hRh : ∃ f, MirabolicWhittaker.restriction ψ f = h := hR h
    obtain ⟨f, rfl⟩ := hRh
    have e := hB.2 (successorUnipotent u) (isCovarianceUnipotent_successor hnm hu) f w
    simp only [LinearMap.comp_apply] at e
    calc B' (mirabolicCompactInduced ψ m (unequalRankUnipotentLift u)
          (MirabolicWhittaker.restriction ψ f)) w
        = B' (MirabolicWhittaker.restriction ψ (mirabolicCompactInduced ψ (m + 1)
            (successor (unequalRankUnipotentLift u)) f)) w :=
          congrArg (fun x => B' x w)
            (MirabolicWhittaker.restriction_translate ψ f (unequalRankUnipotentLift u)).symm
      _ = B' (MirabolicWhittaker.restriction ψ (mirabolicCompactInduced ψ (m + 1)
            (unequalRankUnipotentLift (successorUnipotent u)) f)) w :=
          congrArg (fun g => B' (MirabolicWhittaker.restriction ψ
            (mirabolicCompactInduced ψ (m + 1) g f)) w)
            (unequalRankUnipotentLift_successorUnipotent u).symm
      _ = (standardCharacter ψ (m + 1) (successorUnipotent u) : ℂ) *
            B' (MirabolicWhittaker.restriction ψ f) w := e
      _ = (standardCharacter ψ m u : ℂ) * B' (MirabolicWhittaker.restriction ψ f) w :=
          congrArg (fun z : ℂ => z * B' (MirabolicWhittaker.restriction ψ f) w)
            (standardCharacter_successor ψ u)

end Forms

section Factorization

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  {n m : ℕ} [LocallyCompactSpace (Langlands.GeneralLinear (m + 1) F)]
  [LocallyCompactSpace (Langlands.GeneralLinear (m + 2) F)]
  [NonarchimedeanGroup (Langlands.GeneralLinear (m + 2) F)]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

/-- Every covariant form of rank `m + 1` factors through restriction. -/
theorem exists_comp_restriction (hnm : n < m) (hψ : IsOpen {t : F | ψ.complex t = 1}) {s : ℂ}
    {B : MirabolicCompactFunctions ψ (m + 1) →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hB : B ∈ unequalRankMirabolicForms (Nat.lt_add_one_of_lt hnm) ψ abv
      (mirabolicCompactInduced ψ (m + 1)) η s) :
    ∃ B' : MirabolicCompactFunctions ψ m →ₗ[ℂ] W →ₗ[ℂ] ℂ,
      B'.comp (MirabolicWhittaker.restriction ψ) = B := by
  have hR := MirabolicWhittaker.restriction_surjective ψ hψ (n := m)
  have hker : LinearMap.ker (MirabolicWhittaker.restriction ψ (n := m)) ≤ LinearMap.ker B := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    refine LinearMap.ext fun w => ?_
    refine functional_eq_zero_of_restriction_eq_zero ψ hψ (ℓ := B.flip w) (fun x h => ?_) hf
    have e := hB.2 (radicalToUpperUnipotent (radicalElement x))
      (isCovarianceUnipotent_radical hnm x) h w
    rw [standardCharacter_radicalElement ψ x] at e
    simp only [LinearMap.flip_apply]
    exact e
  refine ⟨(LinearMap.ker _).liftQ B hker ∘ₗ
    ((MirabolicWhittaker.restriction ψ).quotKerEquivOfSurjective hR).symm.toLinearMap,
    LinearMap.ext fun f => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- Pulling back covariant forms of rank `m` along restriction. -/
def formsSuccMap (hnm : n < m) (s : ℂ) :
    unequalRankMirabolicForms hnm ψ abv (mirabolicCompactInduced ψ m) η (s - 1 / 2) →ₗ[ℂ]
      unequalRankMirabolicForms (Nat.lt_add_one_of_lt hnm) ψ abv
        (mirabolicCompactInduced ψ (m + 1)) η s :=
  LinearMap.codRestrict _
    { toFun := fun B' => B'.val.comp (MirabolicWhittaker.restriction ψ)
      map_add' := fun B C => LinearMap.add_comp _ C.val B.val
      map_smul' := fun c B => LinearMap.smul_comp c B.val _ }
    fun B' => comp_restriction_mem ψ abv η hnm s B'.property

omit [LocallyCompactSpace (Langlands.GeneralLinear (m + 1) F)]
  [NonarchimedeanGroup (Langlands.GeneralLinear (m + 2) F)] in
/-- `formsSuccMap` is composition with restriction. -/
theorem formsSuccMap_val (hnm : n < m) (s : ℂ)
    (B' : unequalRankMirabolicForms hnm ψ abv (mirabolicCompactInduced ψ m) η (s - 1 / 2)) :
    (formsSuccMap ψ abv η hnm s B').val = B'.val.comp (MirabolicWhittaker.restriction ψ) :=
  rfl

/-- Composition with the surjective restriction is injective. -/
theorem formsSuccMap_injective (hnm : n < m) (hψ : IsOpen {t : F | ψ.complex t = 1}) (s : ℂ) :
    Function.Injective (formsSuccMap ψ abv η hnm s) := by
  intro B C h
  have h' : B.val.comp (MirabolicWhittaker.restriction ψ) =
      C.val.comp (MirabolicWhittaker.restriction ψ) := congrArg Subtype.val h
  exact Subtype.ext ((LinearMap.cancel_right
    (MirabolicWhittaker.restriction_surjective ψ hψ (n := m))).mp h')

/-- Every covariant form of rank `m + 1` at `s` is a pullback of a covariant form of
rank `m` at `s - 1/2`. -/
theorem formsSuccMap_surjective (hnm : n < m) (hψ : IsOpen {t : F | ψ.complex t = 1}) (s : ℂ) :
    Function.Surjective (formsSuccMap ψ abv η hnm s) := by
  intro B
  have hR := MirabolicWhittaker.restriction_surjective ψ hψ (n := m)
  have h := exists_comp_restriction ψ abv η hnm hψ (s := s) (B := B.val) B.property
  have hB' := Classical.choose_spec h
  have hmem : (Classical.choose h).comp (MirabolicWhittaker.restriction ψ) ∈
      unequalRankMirabolicForms (Nat.lt_add_one_of_lt hnm) ψ abv
        (mirabolicCompactInduced ψ (m + 1)) η s := hB'.symm ▸ B.property
  refine ⟨⟨Classical.choose h, mem_of_comp_restriction_mem ψ abv η hnm hR s hmem⟩,
    Subtype.ext ?_⟩
  exact (formsSuccMap_val ψ abv η hnm s _).trans hB'

/-- One reduction step: covariant forms of rank `m + 1` at `s` are those of rank `m`
at `s - 1/2`, through restriction along the successor embedding. -/
def formsSuccEquiv (hnm : n < m) (hψ : IsOpen {t : F | ψ.complex t = 1}) (s : ℂ) :
    unequalRankMirabolicForms hnm ψ abv (mirabolicCompactInduced ψ m) η (s - 1 / 2) ≃ₗ[ℂ]
      unequalRankMirabolicForms (Nat.lt_add_one_of_lt hnm) ψ abv
        (mirabolicCompactInduced ψ (m + 1)) η s :=
  LinearEquiv.ofBijective (formsSuccMap ψ abv η hnm s)
    ⟨formsSuccMap_injective ψ abv η hnm hψ s, formsSuccMap_surjective ψ abv η hnm hψ s⟩

end Factorization

end UnequalRankCompactPairing

end Langlands.RankinSelberg
