import Langlands.Algebra.RegularModuleHomLeftLimitComparisonProof
import Langlands.Representation.Character.ModularContragredientProof
import Langlands.Representation.Hecke.ContragredientDualModuleProof
import Langlands.Representation.Hecke.Intertwiner
import Langlands.Representation.Smooth.CompactCompletionAction
import Langlands.Representation.Smooth.CompactCompletionMaps

/-!
# Regular Hecke-module maps and compact-open completion

Evaluation at normalized compact-open indicators identifies maps from the
regular Hecke module with the compact-open completion. Right translation
of Haar distributions gives the translation law on completed vectors.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Hecke

open Langlands.Algebra HarishChandraSchwartz MeasureTheory
open HeckeAlgebra (normalizedIndicator)

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- Integrated normalized indicators are the compact averaging projections for any left Haar
measure. -/
theorem heckeAction_normalizedIndicator_eq_compactAverage (K : CompactOpenSubgroup G)
    (v : V) :
    heckeAction μ ρ hρ (normalizedIndicator μ K.1 K.2) v =
      Compact.averageMap ρ hρ K.1 K.2 v := by
  have h := Jacquet.map_averageMap_of_forall_eq ρ hρ K.1 K.2
    (heckeAction μ ρ hρ (normalizedIndicator μ K.1 K.2)) v _
    (fun k => heckeAction_group_of_rightInvariant μ ρ hρ K.1 K.2 _
      (HeckeAlgebra.normalizedIndicator_mem_biInvariant μ K.1 K.2).2 k v)
  rw [heckeAction_normalizedIndicator_of_fixed μ ρ hρ K.1 K.2
    (Compact.averageMap_mem_fixedVectors ρ hρ K.1 K.2 v)] at h
  exact h.symm

/-- The original Hecke-module Hom from the left regular module into a smooth representation. -/
abbrev RegularHeckeHom :=
  @NonUnitalModuleHom (HeckeAlgebra μ) (HeckeAlgebra μ) V _ _ _
    (NonUnitalModule.regular (HeckeAlgebra μ)) (heckeNonUnitalModule μ ρ hρ)

private def compactIndicator (K : CompactOpenSubgroup G) : Idempotent (HeckeAlgebra μ) :=
  ⟨normalizedIndicator μ K.1 K.2, HeckeAlgebra.normalizedIndicator_idempotent μ K.1 K.2⟩

omit [T2Space G] [LocallyCompactSpace G] in
private theorem compactIndicator_le {K L : CompactOpenSubgroup G} (hLK : L.1 ≤ K.1) :
    compactIndicator μ K ≤ compactIndicator μ L :=
  (Idempotent.le_iff_mul _ _).mpr
    ⟨HeckeAlgebra.normalizedIndicator_mul_of_le μ K.1 K.2 L.1 L.2 hLK,
      HeckeAlgebra.normalizedIndicator_mul_of_ge μ K.1 K.2 L.1 L.2 hLK⟩

private theorem exists_le_compactIndicator (e : Idempotent (HeckeAlgebra μ)) :
    ∃ K : CompactOpenSubgroup G, e ≤ compactIndicator μ K := by
  classical
  obtain ⟨K, hK, _, _, hunit⟩ := HeckeAlgebra.finiteFamilyLocalUnits G μ {↑e} ⊤
  exact ⟨⟨K, hK⟩, (Idempotent.le_iff_mul _ _).mpr (hunit e (by simp))⟩

private abbrev HeckeLeftLimit :=
  @NonUnitalModuleLeftLimit (HeckeAlgebra μ) V _ _ (heckeNonUnitalModule μ ρ hρ)

private theorem restrictCompactIndices_compatible (x : HeckeLeftLimit μ ρ hρ)
    (K L : CompactOpenSubgroup G) (hLK : L.1 ≤ K.1) :
    Compact.averageMap ρ hρ K.1 K.2 (x.val (compactIndicator μ L)) =
      x.val (compactIndicator μ K) := by
  have h := x.property.2 (compactIndicator μ K) (compactIndicator μ L)
    (compactIndicator_le μ hLK)
  change heckeAction μ ρ hρ (normalizedIndicator μ K.1 K.2)
    (x.val (compactIndicator μ L)) = x.val (compactIndicator μ K) at h
  exact (heckeAction_normalizedIndicator_eq_compactAverage μ ρ hρ K _).symm.trans h

private def restrictCompactIndices :
    HeckeLeftLimit μ ρ hρ →+ CompactCompletion.completion ρ hρ where
  toFun x := ⟨fun K => x.val (compactIndicator μ K),
    restrictCompactIndices_compatible μ ρ hρ x⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem restrictCompactIndices_bijective :
    Function.Bijective (restrictCompactIndices μ ρ hρ) := by
  classical
  let := heckeNonUnitalModule μ ρ hρ
  constructor
  · intro x y h
    apply Subtype.ext
    funext e
    obtain ⟨K, hK⟩ := exists_le_compactIndicator μ e
    have hxy : x.val (compactIndicator μ K) = y.val (compactIndicator μ K) :=
      congrArg (fun z : CompactCompletion.completion ρ hρ => z.val K) h
    rw [← x.property.2 _ _ hK, ← y.property.2 _ _ hK, hxy]
  · intro x
    let K (e : Idempotent (HeckeAlgebra μ)) := Classical.choose (exists_le_compactIndicator μ e)
    have hK (e : Idempotent (HeckeAlgebra μ)) : e ≤ compactIndicator μ (K e) :=
      Classical.choose_spec (exists_le_compactIndicator μ e)
    let y (e : Idempotent (HeckeAlgebra μ)) := (e : HeckeAlgebra μ) • x.val (K e)
    have hcoord (e : Idempotent (HeckeAlgebra μ)) (L : CompactOpenSubgroup G)
        (he : e ≤ compactIndicator μ L) : y e = (e : HeckeAlgebra μ) • x.val L := by
      let J := (K e).inf L
      have hJL : J.1 ≤ L.1 := (K e).inf_le_right L
      have hJK : J.1 ≤ (K e).1 := (K e).inf_le_left L
      have hcompare (B : CompactOpenSubgroup G) (hJB : J.1 ≤ B.1)
          (heB : e ≤ compactIndicator μ B) :
          (e : HeckeAlgebra μ) • x.val B = (e : HeckeAlgebra μ) • x.val J := by
        rw [← x.property B J hJB,
          ← heckeAction_normalizedIndicator_eq_compactAverage μ ρ hρ]
        change (e : HeckeAlgebra μ) • ((compactIndicator μ B : HeckeAlgebra μ) • x.val J) = _
        rw [← mul_smul, ((Idempotent.le_iff_mul _ _).mp heB).2]
      exact (hcompare (K e) hJK (hK e)).trans (hcompare L hJL he).symm
    refine ⟨⟨y, ?_⟩, ?_⟩
    · constructor
      · intro e
        change (e : HeckeAlgebra μ) • ((e : HeckeAlgebra μ) • x.val (K e)) = y e
        rw [← mul_smul, e.property.eq]
      · intro e f hef
        change (e : HeckeAlgebra μ) • ((f : HeckeAlgebra μ) • x.val (K f)) = y e
        rw [← mul_smul, ((Idempotent.le_iff_mul _ _).mp hef).2]
        exact (hcoord e (K f) (hef.trans (hK f))).symm
    · apply Subtype.ext
      funext L
      change y (compactIndicator μ L) = x.val L
      rw [hcoord _ L le_rfl]
      change heckeAction μ ρ hρ (normalizedIndicator μ L.1 L.2) (x.val L) = x.val L
      rw [heckeAction_normalizedIndicator_eq_compactAverage μ ρ hρ]
      exact x.property L L le_rfl

/-- Evaluate at each normalized compact-open indicator to identify the actual regular
Hecke-module Hom with the compact-open completion. -/
def regularHomCompactCompletionEquiv :
    RegularHeckeHom μ ρ hρ ≃+ CompactCompletion.completion ρ hρ := by
  letI := heckeNonUnitalModule μ ρ hρ
  let E : RegularModuleHom (HeckeAlgebra μ) V ≃+ RegularHeckeHom μ ρ hρ :=
    RegularModuleHom.equivNonUnitalModuleHom
  let F : RegularModuleHom (HeckeAlgebra μ) V →+ HeckeLeftLimit μ ρ hρ :=
    RegularModuleHom.toLeftLimit
  have hF : Function.Bijective F := by
    obtain ⟨e, he, _, _⟩ := regularModuleHomLeftLimitComparison (M := V)
      (Homomorphism.isIdempotented μ)
    change Function.Bijective (RegularModuleHom.toLeftLimit (A := HeckeAlgebra μ) (M := V))
    rw [← he]
    exact e.bijective
  exact AddEquiv.ofBijective ((restrictCompactIndices μ ρ hρ).comp (F.comp E.symm.toAddMonoidHom))
    ((restrictCompactIndices_bijective μ ρ hρ).comp (hF.comp E.symm.bijective))

@[simp]
theorem regularHomCompactCompletionEquiv_apply (q : RegularHeckeHom μ ρ hρ)
    (K : CompactOpenSubgroup G) :
    (regularHomCompactCompletionEquiv μ ρ hρ q).val K = q (normalizedIndicator μ K.1 K.2) :=
  rfl

/-- Recover the value at a test using any normalized indicator that is a right unit for it. -/
theorem regularHomCompactCompletionEquiv_symm_apply (x : CompactCompletion.completion ρ hρ)
    (b : HeckeAlgebra μ) (K : CompactOpenSubgroup G)
    (hb : b * normalizedIndicator μ K.1 K.2 = b) :
    (regularHomCompactCompletionEquiv μ ρ hρ).symm x b =
      heckeAction μ ρ hρ b (x.val K) := by
  let := NonUnitalModule.regular (HeckeAlgebra μ)
  let := heckeNonUnitalModule μ ρ hρ
  let E := regularHomCompactCompletionEquiv μ ρ hρ
  have hx := congrArg (fun y : CompactCompletion.completion ρ hρ => y.val K)
    (E.apply_symm_apply x)
  change (regularHomCompactCompletionEquiv μ ρ hρ (E.symm x)).val K = x.val K at hx
  rw [regularHomCompactCompletionEquiv_apply] at hx
  calc
    E.symm x b = E.symm x (b * normalizedIndicator μ K.1 K.2) := congrArg (E.symm x) hb.symm
    _ = heckeAction μ ρ hρ b (E.symm x (normalizedIndicator μ K.1 K.2)) :=
      (E.symm x).map_smul' b (normalizedIndicator μ K.1 K.2)
    _ = heckeAction μ ρ hρ b (x.val K) := congrArg (heckeAction μ ρ hρ b) hx

/-- Postcomposition by an intertwiner gives the componentwise map on completions. -/
theorem regularHomCompactCompletionEquiv_natural {W : Type w} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ)
    (q : RegularHeckeHom μ ρ hρ) :
    regularHomCompactCompletionEquiv μ σ hσ
      (@NonUnitalModuleHom.comp (HeckeAlgebra μ) (HeckeAlgebra μ) V W _ _ _ _
        (NonUnitalModule.regular (HeckeAlgebra μ))
        (heckeNonUnitalModule μ ρ hρ) (heckeNonUnitalModule μ σ hσ)
        (heckeActionIntertwiner μ hρ hσ T).toNonUnitalModuleHom q) =
      CompactCompletion.map hρ hσ T (regularHomCompactCompletionEquiv μ ρ hρ q) := by
  apply Subtype.ext
  funext K
  rfl

private theorem heckeAction_rightRepresentation (g : G) (b : HeckeAlgebra μ) (v : V) :
    heckeAction μ ρ hρ (Homomorphism.rightRepresentation μ (MonoidHom.id G) g⁻¹ b) v =
      heckeAction μ ρ hρ b (ρ g v) := by
  have ht : Homomorphism.rightRepresentation μ (MonoidHom.id G) g⁻¹ b =
      haarScale g • TestFunction.rightTranslate g⁻¹ (HeckeAlgebra.toTestFunction μ b) := by
    apply HeckeAlgebra.ext
    intro a
    rw [Homomorphism.rightRepresentation_apply, MonoidHom.id_apply, inv_inv]
    rfl
  rw [ht]
  change integratedAction μ ρ hρ
      (haarScale g • TestFunction.rightTranslate g⁻¹ (HeckeAlgebra.toTestFunction μ b)) v =
    integratedAction μ ρ hρ (HeckeAlgebra.toTestFunction μ b) (ρ g v)
  rw [map_smul, LinearMap.smul_apply, Character.integratedAction_right_input_modular μ ρ hρ]
  simp [HarmonicAnalysis.Distribution.renardModular_apply, haarScale]

/-- Translation on the completion corresponds to precomposition by inverse right translation
of Haar distributions. -/
theorem regularHomCompactCompletionEquiv_symm_translate (g : G)
    (x : CompactCompletion.completion ρ hρ) (b : HeckeAlgebra μ) :
    (regularHomCompactCompletionEquiv μ ρ hρ).symm (CompactCompletion.action ρ hρ g x) b =
      (regularHomCompactCompletionEquiv μ ρ hρ).symm x
        (Homomorphism.rightRepresentation μ (MonoidHom.id G) g⁻¹ b) := by
  classical
  let b' := Homomorphism.rightRepresentation μ (MonoidHom.id G) g⁻¹ b
  obtain ⟨K₀, hK₀, _, _, hK⟩ := HeckeAlgebra.finiteFamilyLocalUnits G μ {b} ⊤
  let K : CompactOpenSubgroup G := ⟨K₀, hK₀⟩
  let L := K.conj g⁻¹
  obtain ⟨J, hJ, hJL, _, hJfix⟩ := HeckeAlgebra.finiteFamilyLocalUnits G μ {b'} L.1
  have hb := (hK b (by simp)).2
  have hb' := (hJfix b' (by simp)).2
  change (regularHomCompactCompletionEquiv μ ρ hρ).symm (CompactCompletion.action ρ hρ g x) b =
    (regularHomCompactCompletionEquiv μ ρ hρ).symm x b'
  rw [regularHomCompactCompletionEquiv_symm_apply μ ρ hρ _ b K hb,
    regularHomCompactCompletionEquiv_symm_apply μ ρ hρ _ b' ⟨J, hJ⟩ hb',
    CompactCompletion.action_apply]
  change heckeAction μ ρ hρ b (ρ g (x.val L)) = heckeAction μ ρ hρ b' (x.val ⟨J, hJ⟩)
  rw [heckeAction_rightRepresentation μ ρ hρ g b,
    ← x.property L ⟨J, hJ⟩ hJL, ← CompactCompletion.averageMap_translate ρ hρ g K,
    ← heckeAction_normalizedIndicator_eq_compactAverage μ ρ hρ K,
    ← Module.End.mul_apply, ← map_mul, hb]

end Langlands.Hecke
