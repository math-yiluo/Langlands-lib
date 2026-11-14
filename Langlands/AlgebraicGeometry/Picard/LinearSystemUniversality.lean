import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionSetup
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveLocal
import Langlands.AlgebraicGeometry.Picard.SectionZeroIdealFrames
import Langlands.AlgebraicGeometry.Picard.PushforwardLineBundle

/-! # Linear systems and their universal divisors over opens of the base

For `g : Y ⟶ S` and a Picard class `m` on `Y`, a divisor of the linear system of `m` over a test
`t : T ⟶ S` is a relative effective Cartier divisor `E` on `Y ×_S T` with
`[O(E)] = [m_T] + [n]` for a class `n` on `T`. A scheme `l : P ⟶ S` with a divisor `W` of the
linear system over `P` is universal over an open `V` of `S` if `P` lies over `V` and every
divisor over a locally noetherian test lying over `V` is the pullback of `W` along exactly one
point of `P`. Universality is inherited by base changes to smaller opens, and two universal
families over the same open are isomorphic. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemGluing

open PicardHilbertPiecesReduction (mapX mapX_comp mapX_congr mapX_fst mapX_snd dcl dcl_congr
  pb_comp_apply pb_iso_inv_hom pb_mapX_fst)

section Generators

/-- **Effective Cartier ideals have local regular generators.** -/
lemma exists_local_regular_generator_of_isEffectiveCartierIdeal {X : Scheme.{u}}
    (I : X.IdealSheafData) (h : IsEffectiveCartierIdeal I) (z : X) :
    ∃ U : X.affineOpens, z ∈ U.1 ∧ ∃ a : Γ(X, U.1),
      I.ideal U = Ideal.span {a} ∧ IsSMulRegular Γ(X, U.1) a := by
  let L : LineBundle X := ⟨StructureKernelModule.kernelModule I.subschemeι, h⟩
  obtain ⟨U, hzU, t, ht⟩ := SectionZeroIdeal.exists_affine_frame L z
  have hbij := ht.bijective (le_refl U.1) (le_refl U.1)
  simp only [SectionZeroIdeal.map_id_apply] at hbij
  have hmem : ∀ y : Γ(X, U.1), y ∈ I.ideal U ↔
      y ∈ RingHom.ker (I.subschemeι.app U.1).hom := by
    intro y
    rw [Scheme.IdealSheafData.ker_subschemeι_app]
  have hsmul : ∀ (c : Γ(X, U.1)) (s : Γ(L.obj, U.1)), (c • s).val = c * s.val := fun _ _ => rfl
  refine ⟨U, hzU, t.val, ?_, ?_⟩
  · ext y
    rw [Ideal.mem_span_singleton']
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := hbij.2 ⟨y, (hmem y).1 hy⟩
      exact ⟨c, (hsmul c t).symm.trans (congrArg Subtype.val hc)⟩
    · rintro ⟨c, rfl⟩
      rw [hmem, ← hsmul]
      exact (c • t).property
  · intro c d hcd
    apply hbij.1
    apply Subtype.ext
    change c * t.val = d * t.val
    rw [mul_comm c, mul_comm d]
    exact hcd

end Generators

variable {S Y : Scheme.{u}} (g : Y ⟶ S) (m : Group Y)

/-- **The divisors of the linear system of the class `m` over a test `t`.** -/
def LS {T : Scheme.{u}} (t : T ⟶ S) (E : (pullback g t).IdealSheafData) : Prop :=
  ∃ hE : IsRelativeEffectiveCartierIdeal (pullback.snd g t) E, ∃ n : Group T,
    dcl E hE.1 = Group.pullback (pullback.fst g t) m + Group.pullback (pullback.snd g t) n

variable {g m}

/-- **Divisors of the linear system pull back to divisors of the linear system.** -/
lemma LS.comap {T T' : Scheme.{u}} {t : T ⟶ S} {t' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ t = t')
    {E : (pullback g t).IdealSheafData} (hE : LS g m t E) : LS g m t' (E.comap (mapX g h w)) := by
  obtain ⟨hE, n, hn⟩ := hE
  obtain ⟨hJ, hd⟩ := PicardHilbertPiecesReduction.divBC g
    RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange h w E hE
  refine ⟨hJ, Group.pullback h n, ?_⟩
  rw [hd, hn, map_add, pb_mapX_fst, ← pb_comp_apply, mapX_snd, pb_comp_apply]

lemma mapX_id {T : Scheme.{u}} {t : T ⟶ S} (w : 𝟙 T ≫ t = t) : mapX g (𝟙 T) w = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mapX_fst, Category.id_comp]
  · rw [mapX_snd, Category.comp_id, Category.id_comp]

variable (g m)

/-- **Universality over an open `V` of the base.** -/
structure IsUniversalOn (V : S.Opens) {P : Scheme.{u}} (l : P ⟶ S)
    (W : (pullback g l).IdealSheafData) : Prop where
  range_le : Set.range l ⊆ (V : Set S)
  ls : LS g m l W
  exists_point : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S),
    Set.range t ⊆ (V : Set S) → ∀ E : (pullback g t).IdealSheafData, LS g m t E →
      ∃ (k : T ⟶ P) (hk : k ≫ l = t), W.comap (mapX g k hk) = E
  eq_of_comap_eq : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S) (k₁ k₂ : T ⟶ P)
    (hk₁ : k₁ ≫ l = t) (hk₂ : k₂ ≫ l = t),
      W.comap (mapX g k₁ hk₁) = W.comap (mapX g k₂ hk₂) → k₁ = k₂

variable {g m}

/-- **Universality restricts along pullback squares over smaller opens.** -/
theorem IsUniversalOn.of_isPullback {V V' : S.Opens} (hVV : V' ≤ V) {P P' : Scheme.{u}}
    {l : P ⟶ S} {W : (pullback g l).IdealSheafData} (hU : IsUniversalOn g m V l W)
    (k : P' ⟶ P) (s : P' ⟶ V') (hsq : IsPullback k s l V'.ι) :
    IsUniversalOn g m V' (s ≫ V'.ι) (W.comap (mapX g k (by rw [hsq.w]))) where
  range_le := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (Scheme.Opens.range_ι V').subset ⟨_, rfl⟩
  ls := hU.ls.comap k _
  exists_point T _ t ht E hE := by
    obtain ⟨k₀, hk₀, hk₀E⟩ := hU.exists_point T t (ht.trans hVV) E hE
    have hr : Set.range t ⊆ Set.range V'.ι := by rw [Scheme.Opens.range_ι]; exact ht
    let t'' := IsOpenImmersion.lift V'.ι t hr
    have ht'' : t'' ≫ V'.ι = t := IsOpenImmersion.lift_fac _ _ _
    let k' := hsq.lift k₀ t'' (by rw [hk₀, ht''])
    have hk'1 : k' ≫ k = k₀ := hsq.lift_fst _ _ _
    have hk'2 : k' ≫ s = t'' := hsq.lift_snd _ _ _
    refine ⟨k', by rw [← Category.assoc, hk'2, ht''], ?_⟩
    rw [← Scheme.IdealSheafData.comap_comp, mapX_comp]
    rw [← hk₀E]
    exact congrArg _ (mapX_congr g hk'1 _ _)
  eq_of_comap_eq T _ t k₁ k₂ hk₁ hk₂ h := by
    have e₁ : (k₁ ≫ k) ≫ l = t := by rw [Category.assoc, hsq.w, hk₁]
    have e₂ : (k₂ ≫ k) ≫ l = t := by rw [Category.assoc, hsq.w, hk₂]
    have hfst : k₁ ≫ k = k₂ ≫ k := by
      refine hU.eq_of_comap_eq T t _ _ e₁ e₂ ?_
      have c₁ := mapX_comp g k (by rw [hsq.w]) k₁ hk₁
      have c₂ := mapX_comp g k (by rw [hsq.w]) k₂ hk₂
      rw [← c₁, ← c₂, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp] at *
      exact h
    have hsnd : k₁ ≫ s = k₂ ≫ s := by
      rw [← cancel_mono V'.ι, Category.assoc, Category.assoc, hk₁, hk₂]
    exact hsq.hom_ext hfst hsnd

/-- **Two universal families over the same open are isomorphic.** -/
theorem isIso_of_isUniversalOn {V : S.Opens} {P₁ P₂ : Scheme.{u}} [IsLocallyNoetherian P₁]
    [IsLocallyNoetherian P₂] {l₁ : P₁ ⟶ S} {l₂ : P₂ ⟶ S} {W₁ : (pullback g l₁).IdealSheafData}
    {W₂ : (pullback g l₂).IdealSheafData} (h₁ : IsUniversalOn g m V l₁ W₁)
    (h₂ : IsUniversalOn g m V l₂ W₂) (ℓ : P₁ ⟶ P₂) (hℓ : ℓ ≫ l₂ = l₁)
    (hW : W₂.comap (mapX g ℓ hℓ) = W₁) : IsIso ℓ := by
  obtain ⟨μ, hμ, hμW⟩ := h₁.exists_point P₂ l₂ h₂.range_le W₂ h₂.ls
  have e₁ : (ℓ ≫ μ) ≫ l₁ = l₁ := by rw [Category.assoc, hμ, hℓ]
  have e₂ : (μ ≫ ℓ) ≫ l₂ = l₂ := by rw [Category.assoc, hℓ, hμ]
  have h1 : ℓ ≫ μ = 𝟙 P₁ := by
    refine h₁.eq_of_comap_eq P₁ l₁ _ _ e₁ (Category.id_comp _) ?_
    rw [← mapX_comp g μ hμ ℓ hℓ, Scheme.IdealSheafData.comap_comp, hμW, hW, mapX_id,
      Scheme.IdealSheafData.comap_id]
  have h2 : μ ≫ ℓ = 𝟙 P₂ := by
    refine h₂.eq_of_comap_eq P₂ l₂ _ _ e₂ (Category.id_comp _) ?_
    rw [← mapX_comp g ℓ hℓ μ hμ, Scheme.IdealSheafData.comap_comp, hW, hμW, mapX_id,
      Scheme.IdealSheafData.comap_id]
  exact ⟨μ, h1, h2⟩

end Langlands.AlgebraicGeometry.Picard.LinearSystemGluing
