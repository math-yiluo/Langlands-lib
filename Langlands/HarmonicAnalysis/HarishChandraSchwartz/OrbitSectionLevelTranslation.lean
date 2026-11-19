import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology
import Langlands.HarmonicAnalysis.TorusMonomialSeminormControl
import Langlands.Representation.Plancherel.ProductInducedOrbitFullAction

/-! # Finite derivative bounds for translation between orbit section levels -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ

/-- Right-invariant evaluations on one compact group are determined by their values
on the finite quotient. Any ambient linear functional restricts to a sum of linear
functionals of those evaluations. -/
private theorem exists_sum_dual_of_rightInvariantEvaluation
    {X V W : Type*} [Group X] (L : Subgroup X) [Fintype (X ⧸ L)]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (E : W →ₗ[ℂ] (X → V)) (hE : Function.Injective E) (ℓ : Module.Dual ℂ W) :
    ∃ duals : (X ⧸ L) → Module.Dual ℂ V,
      ∀ w ∈ rightInvariantEvaluationSubmodule E L,
        ℓ w = ∑ j, duals j (E w j.out) := by
  classical
  let S := rightInvariantEvaluationSubmodule E L
  let T : S →ₗ[ℂ] ((X ⧸ L) → V) :=
    { toFun := fun v j => E v.val j.out
      map_add' := fun a b => funext fun j => congrFun (E.map_add a.val b.val) j.out
      map_smul' := fun c a => funext fun j => congrFun (E.map_smul c a.val) j.out }
  have hT : Function.Injective T := by
    intro v w hvw
    apply Subtype.ext
    apply hE
    funext k
    let j : X ⧸ L := QuotientGroup.mk k
    have hm : j.out⁻¹ * k ∈ L :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact j.out_eq)
    have hv := v.property j.out ⟨j.out⁻¹ * k, hm⟩
    have hw := w.property j.out ⟨j.out⁻¹ * k, hm⟩
    simpa only [mul_inv_cancel_left] using hv.trans ((congrFun hvw j).trans hw.symm)
  let ℓ' := (ℓ.comp S.subtype).comp T.leftInverse
  refine ⟨fun j => ℓ'.comp (LinearMap.single ℂ (fun _ : X ⧸ L => V) j), fun w hw => ?_⟩
  let v : S := ⟨w, hw⟩
  have hv : ℓ' (T v) = ℓ w := by
    change ℓ (T.leftInverse (T v)).val = ℓ w
    rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hT)]
  rw [← hv]
  change ℓ' (T v) = ∑ j, ℓ' (Pi.single j (T v j))
  rw [← map_sum, LinearMap.sum_single_apply]

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] [DecidableEq J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (he : HasLaurentUnitaryCoordinates ν e)

set_option hygiene false in
local notation "CompactPicture" => ProductInducedCompactPicture h K π.obj
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "levelToSections" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "levelSeminorms" => OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "restriction" => productInducedSmoothOrbitCompactRestriction
  h hU ν π K hP hK hν hr hPK e
set_option hygiene false in
local notation "fullAction" => productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he

/-- A common open level inside the compact picture for the translate by `x`. -/
def orbitSectionTranslatedLevel (K H : OpenSubgroup G) (x : G × G) : OpenSubgroup G :=
  K ⊓ (H.comap (MulAut.conj x.1⁻¹).toMonoidHom (IsTopologicalGroup.continuous_conj _)) ⊓
    (H.comap (MulAut.conj x.2⁻¹).toMonoidHom (IsTopologicalGroup.continuous_conj _))

/-- The actual translation acts linearly from the original level to the
intersection of the two conjugated levels with `K`. -/
def orbitSectionLevelTranslate (H : OpenSubgroup G) (x : G × G) :
    SectionLevel H →ₗ[ℂ] SectionLevel (orbitSectionTranslatedLevel K H x) :=
  let A := productInducedOrbitRepresentation h hU ν π
  ((A x).comp (orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H).subtype).codRestrict
    (orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK (orbitSectionTranslatedLevel K H x))
    (fun q => by
      refine ⟨productInducedOrbitRepresentation_full_smooth_mem h hU ν π K hP hK hν hr hPK e
        he x q.property.1, fun k => ?_⟩
      let l : H.prod H := ⟨x⁻¹ * k.val * x, by
        have h₁ := k.property.1.1.2
        have h₂ := k.property.2.2
        change x.1⁻¹ * k.val.1 * (x.1⁻¹)⁻¹ ∈ H at h₁
        change x.2⁻¹ * k.val.2 * (x.2⁻¹)⁻¹ ∈ H at h₂
        constructor
        · change x.1⁻¹ * k.val.1 * x.1 ∈ H
          simpa only [inv_inv] using h₁
        · change x.2⁻¹ * k.val.2 * x.2 ∈ H
          simpa only [inv_inv] using h₂⟩
      change A k.val (A x q.val) = A x q.val
      have hk : k.val * x = x * l.val := by dsimp [l]; group
      have hl : A l.val q.val = q.val := q.property.2 l
      rw [← Module.End.mul_apply, ← map_mul, hk, map_mul, Module.End.mul_apply, hl])

omit [DecidableEq J] in
@[simp]
theorem orbitSectionLevelTranslate_toSections (H : OpenSubgroup G) (x : G × G)
    (q : SectionLevel H) :
    levelToSections (orbitSectionTranslatedLevel K H x)
      (orbitSectionLevelTranslate h hU hP K hK hPK ν π hν hr e he H x q) =
      fullAction x (levelToSections H q) := rfl

/-- For one translate, each output derivative seminorm is bounded by a finite
supremum of input derivative seminorms on the original level. -/
theorem exists_orbitSectionLevelTranslate_seminorm_bound
    (H : OpenSubgroup G) (x : G × G) (l : List J) (ℓ : Module.Dual ℂ CompactPicture) :
    ∃ t : Finset (List J × Module.Dual ℂ CompactPicture), ∃ c : ℝ≥0,
      ∀ q : SectionLevel H,
        levelSeminorms (orbitSectionTranslatedLevel K H x) (l, ℓ)
          (orbitSectionLevelTranslate h hU hP K hK hPK ν π hν hr e he H x q) ≤
          (c : ℝ) * (t.sup (levelSeminorms H)) q := by
  classical
  let H' := orbitSectionTranslatedLevel K H x
  let tr := orbitSectionLevelTranslate h hU hP K hK hPK ν π hν hr e he H x
  have hH' : H' ≤ K := inf_le_left.trans inf_le_left
  let L := OpenSubgroup.comap (K.prod K).toSubgroup.subtype continuous_subtype_val (H'.prod H')
  let : CompactSpace (K.prod K) := isCompact_iff_compactSpace.mp (hK.prod hK)
  let : IsTopologicalGroup (K.prod K) := inferInstanceAs (IsTopologicalGroup (K.prod K).toSubgroup)
  let Q := (K.prod K) ⧸ L.toSubgroup
  let : Fintype Q := Fintype.ofFinite Q
  let E := productInducedCompactEvaluation h K π.obj
  obtain ⟨duals, hduals⟩ := exists_sum_dual_of_rightInvariantEvaluation L.toSubgroup E
    (productInducedCompactEvaluation_injective h K π.obj) ℓ
  have hfixed (q : SectionLevel H) (z : J → Circle) :
      restriction (levelToSections H' (tr q)) z ∈ rightInvariantEvaluationSubmodule E L.toSubgroup := by
    intro k a
    let b : H'.prod H' := ⟨a.val.val, a.property⟩
    have hf := productInducedCompactRepresentation_orbitSectionCompactRestriction
      ν π e h hU K hP hK hν hr hPK H' hH' (levelToSections H' (tr q)) (tr q).property b z
    exact congrArg (fun v : CompactPicture => E v k) hf
  choose p k hpk using fun j : Q => product_compact_factorization K hPK ((j.out : G × G) * x)
  let a (j : Q) : M := h.projection ⟨(p j).val.1, (p j).property.1⟩ *
    (h.projection ⟨(p j).val.2, (p j).property.2⟩)⁻¹
  let W (j : Q) : smoothFiniteTorusFunctions J := unitaryUnramifiedSmoothEvaluation ν e he (a j)
  let d (j : Q) : Module.Dual ℂ CompactPicture := (duals j).comp
    ((inducingRepresentation (h.prod h) (hU.prod hU)
      (productLeviObject π.obj π.obj.contragredient) (p j)).comp
      ((LinearMap.proj (k j)).comp E))
  let f (j : Q) (q : SectionLevel H) :=
    orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK (d j) (levelToSections H q)
  have hsum (q : SectionLevel H) :
      orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK ℓ (levelToSections H' (tr q)) =
        ∑ j, W j * f j q := by
    apply Subtype.ext
    funext z
    rw [orbitSectionCoefficient_apply, hduals _ (hfixed q z)]
    rw [show levelToSections H' (tr q) = fullAction x (levelToSections H q) from rfl]
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hval := productInducedOrbitRepresentation_full_restriction_eval
      h hU ν π K hP hK hν hr hPK e x j.out (p j) (k j) (hpk j)
      (levelToSections H q).val z
    change E (restriction (fullAction x (levelToSections H q)) z) j.out =
      ((e.symm z).val (a j) : ℂ) •
        inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject π.obj π.obj.contragredient) (p j)
          (E (restriction (levelToSections H q) z) (k j)) at hval
    refine (congrArg (duals j) hval).trans ?_
    rw [map_smul]
    rfl
  let n := l.length
  let t : Finset (List J × Module.Dual ℂ CompactPicture) :=
    Finset.univ.biUnion fun j : Q => (torusDerivativeLists (J := J) n).image fun m => (m, d j)
  let C (j : Q) : ℝ := (2 : ℝ)^n * smoothTorusDerivativeControl n (W j)
  have hC (j : Q) : 0 ≤ C j := mul_nonneg (by positivity) (apply_nonneg _ _)
  let c : ℝ≥0 := ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC j⟩
  refine ⟨t, c, fun q => ?_⟩
  have hcontrol (j : Q) : smoothTorusDerivativeControl n (f j q) ≤
      (t.sup (levelSeminorms H)) q := by
    unfold smoothTorusDerivativeControl
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro m hm
    have hmem : (m, d j) ∈ t := Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ j, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    exact (Finset.le_sup (f := levelSeminorms H) hmem) q
  change orbitSectionSeminorm ν π e h hU K hP hK hν hr hPK (l, ℓ)
    (levelToSections H' (tr q)) ≤ _
  rw [orbitSectionSeminorm_apply]
  change ‖smoothTorusToContinuousMap (torusPartialDerivListLinear l
    (orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK ℓ (levelToSections H' (tr q))))‖ ≤ _
  rw [hsum q, map_sum, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖smoothTorusToContinuousMap (torusPartialDerivListLinear l (W j * f j q))‖
      ≤ ∑ j, C j * (t.sup (levelSeminorms H)) q := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [ContinuousMap.norm_le _ (mul_nonneg (hC j) (apply_nonneg _ _))]
        intro z
        change ‖(torusPartialDerivListLinear l (W j * f j q)).val z‖ ≤ _
        rw [torusPartialDerivListLinear_apply]
        exact (norm_torusPartialDerivList_mul_le_control n (W j) (f j q) l le_rfl z).trans
          (mul_le_mul_of_nonneg_left (hcontrol j) (hC j))
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- Translation is continuous for the existing seminorm topologies at the two levels. -/
theorem continuous_orbitSectionLevelTranslate (H : OpenSubgroup G) (x : G × G) :
    Continuous (orbitSectionLevelTranslate h hU hP K hK hPK ν π hν hr e he H x) := by
  refine WithSeminorms.continuous_of_isBounded
    (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK H)
    (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK
      (orbitSectionTranslatedLevel K H x)) _ ?_
  intro i
  obtain ⟨t, c, hc⟩ := exists_orbitSectionLevelTranslate_seminorm_bound
    h hU hP K hK hPK ν π hν hr e he H x i.1 i.2
  exact ⟨t, c, fun q => by
    simpa only [Seminorm.comp_apply, smul_apply, NNReal.smul_def, smul_eq_mul, Prod.mk.eta] using hc q⟩

/-- Any finite supremum of derivative seminorms at the translated level is
bounded by a finite supremum at the original level. -/
theorem exists_orbitSectionLevelTranslate_finsetSup_bound
    (H : OpenSubgroup G) (x : G × G) (s : Finset (List J × Module.Dual ℂ CompactPicture)) :
    ∃ t : Finset (List J × Module.Dual ℂ CompactPicture), ∃ c : ℝ≥0,
      ∀ q : SectionLevel H,
        (s.sup (levelSeminorms (orbitSectionTranslatedLevel K H x)))
          (orbitSectionLevelTranslate h hU hP K hK hPK ν π hν hr e he H x q) ≤
          (c : ℝ) * (t.sup (levelSeminorms H)) q := by
  let H' := orbitSectionTranslatedLevel K H x
  let tr := orbitSectionLevelTranslate h hU hP K hK hPK ν π hν hr e he H x
  let P := (s.sup (levelSeminorms H')).comp tr
  have hcont : Continuous P :=
    (Seminorm.continuous_finsetSup fun i _ =>
      (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK H').continuous_seminorm i).comp
      (continuous_orbitSectionLevelTranslate h hU hP K hK hPK ν π hν hr e he H x)
  obtain ⟨t, c, -, hc⟩ := Seminorm.bound_of_continuous
    (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK H) P hcont
  exact ⟨t, c, fun q => by
    simpa only [P, Seminorm.comp_apply, smul_apply, NNReal.smul_def, smul_eq_mul] using hc q⟩

end Langlands.HarishChandraSchwartz
