import Langlands.HarmonicAnalysis.TorusMonomialSeminormControl
import Langlands.Representation.Plancherel.ProductInducedOrbitFullAction

/-! # Change of compact picture for the original orbit sections -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K L : OpenSubgroup G)
  (hK : IsCompact (K : Set G)) (hL : IsCompact (L : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hPL : ∀ g : G, ∃ p : P, ∃ l : L, g = (p : G) * (l : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (he : HasLaurentUnitaryCoordinates ν e)

set_option hygiene false in
local notation "Pic" A => ProductInducedCompactPicture h A π.obj
set_option hygiene false in
local notation "restrictionK" => productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
set_option hygiene false in
local notation "restrictionL" => productInducedFamilyRestriction ν e h L hP hL hν hr hU hPL π.obj

omit [Fintype J] in
/-- The new compact restriction expands in finitely many fixed linear maps of
the old compact restriction with one parameter character for each map. -/
private theorem exists_compactRestriction_sum :
    ∃ s : Finset (P.prod P), ∃ T : (P.prod P) → (Pic K) →ₗ[ℂ] (Pic L),
      ∀ (F : ProductInducedTorusFamilies ν e h hU π.obj) (z : J → Circle),
        restrictionL F z = ∑ p ∈ s,
          ((e.symm z).val (h.projection ⟨p.val.1, p.property.1⟩ *
            (h.projection ⟨p.val.2, p.property.2⟩)⁻¹) : ℂ) • T p (restrictionK F z) := by
  classical
  let V (p : P.prod P) : Set (G × G) := {x | (p : G × G)⁻¹ * x ∈ K.prod K}
  have hLc : IsCompact ((L.prod L : OpenSubgroup (G × G)) : Set (G × G)) := hL.prod hL
  obtain ⟨s, hs⟩ := hLc.elim_finite_subcover V
    (fun p => (K.prod K).isOpen.preimage (continuous_const.mul continuous_id)) (fun x _ => by
      obtain ⟨p, k, hk⟩ := product_compact_factorization K hPK x
      refine Set.mem_iUnion.mpr ⟨p, ?_⟩
      change (p : G × G)⁻¹ * x ∈ K.prod K
      rw [hk, inv_mul_cancel_left]
      exact k.property)
  have hx (x : L.prod L) : ∃ p ∈ s, (p : G × G)⁻¹ * (x : G × G) ∈ K.prod K := by
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp (hs x.property)
    exact ⟨p, hp, hx⟩
  choose p hp hk using hx
  let k (x : L.prod L) : K.prod K := ⟨(p x : G × G)⁻¹ * (x : G × G), hk x⟩
  let EK := productInducedCompactEvaluation h K π.obj
  let EL := productInducedCompactEvaluation h L π.obj
  let A (q : P.prod P) : (Pic K) →ₗ[ℂ] ((L.prod L) → CoefficientTensor π.obj) :=
    LinearMap.pi fun x => if p x = q then
      (inducingRepresentation (h.prod h) (hU.prod hU)
        (productLeviObject π.obj π.obj.contragredient) q).comp ((LinearMap.proj (k x)).comp EK)
      else 0
  let a (q : P.prod P) : M := h.projection ⟨q.val.1, q.property.1⟩ *
    (h.projection ⟨q.val.2, q.property.2⟩)⁻¹
  refine ⟨s, fun q => EL.leftInverse.comp (A q), fun F z => ?_⟩
  have hEL : EL.leftInverse (EL (restrictionL F z)) = restrictionL F z :=
    LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr (productInducedCompactEvaluation_injective h L π.obj)) _
  have hsum : EL (restrictionL F z) = ∑ q ∈ s, ((e.symm z).val (a q) : ℂ) • A q (restrictionK F z) := by
    funext x
    have hfac : (x : G × G) = (p x : G × G) * (k x : G × G) := (mul_inv_cancel_left _ _).symm
    have heval : EL (restrictionL F z) x = ((e.symm z).val (a (p x)) : ℂ) •
        inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject π.obj π.obj.contragredient) (p x) (EK (restrictionK F z) (k x)) := by
      change productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) π.obj
        (eval _ _ (F z) (x : G × G)) = _
      rw [hfac]
      exact (congrArg (productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) π.obj)
        ((F z).val.property (p x) (k x : G × G))).trans
        (productCompactTwistTensorEquiv_inducing h hU ν (unitaryTorusParameter ν e z) π.obj (p x) _)
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single_of_mem (p x) (hp x) (fun q _ hne => by
      simp [A, Ne.symm hne])]
    dsimp only [A]
    rw [LinearMap.pi_apply, ite_eq_left (rfl : p x = p x)]
    exact heval
  calc
    _ = EL.leftInverse (EL (restrictionL F z)) := hEL.symm
    _ = _ := by simp only [hsum, map_sum, map_smul, LinearMap.comp_apply, a]

include he in
/-- Finite scalar smoothness of an actual orbit section is independent of
the compact open Iwasawa factor. -/
theorem productInducedSmoothOrbitSections_le_changeCompact :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK ≤
      productInducedSmoothOrbitSections ν π e h hU L hP hL hν hr hPL := by
  classical
  intro q hq
  refine ⟨hq.1, ?_⟩
  obtain ⟨s, T, hT⟩ := exists_compactRestriction_sum h hU hP K L hK hL hPK hPL ν π hν hr e
  let F := productInducedOrbitPullback ν π e h hU q
  let a (p : P.prod P) : M := h.projection ⟨p.val.1, p.property.1⟩ *
    (h.projection ⟨p.val.2, p.property.2⟩)⁻¹
  let W (p : P.prod P) := unitaryUnramifiedSmoothEvaluation ν e he (a p)
  change restrictionL F ∈ finiteSmoothFamilies J (Pic L)
  rw [show restrictionL F = ∑ p ∈ s, fun z => (W p).val z • T p (restrictionK F z) from
    funext fun z => by rw [hT F z, Finset.sum_apply]; rfl]
  exact (finiteSmoothFamilies J (Pic L)).sum_mem (fun p _ =>
    mem_finiteSmoothFamilies_smul (mem_finiteSmoothFamilies_linearMap hq.2 (T p)) (W p))

variable [DecidableEq J]

set_option hygiene false in
local notation "levelK" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "levelL" => OrbitSectionLevel ν π e h hU L hP hL hν hr hPL
set_option hygiene false in
local notation "includeK" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "includeL" => OrbitSectionLevel.toSections ν π e h hU L hP hL hν hr hPL
set_option hygiene false in
local notation "seminormK" => OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "seminormL" => OrbitSectionLevel.seminormFamily ν π e h hU L hP hL hν hr hPL

/-- Keep the same actual section and view it at the common open level in the
new compact picture. -/
def orbitSectionLevelChangeCompact (H : OpenSubgroup G) : levelK H →ₗ[ℂ] levelL (H ⊓ L) :=
  Submodule.inclusion (by
    intro q hq
    refine ⟨productInducedSmoothOrbitSections_le_changeCompact h hU hP K L hK hL hPK hPL ν π hν hr e he
      hq.1, fun x => ?_⟩
    exact hq.2 ⟨x.val, x.property.1.1, x.property.2.1⟩)

omit [DecidableEq J] in
@[simp]
theorem orbitSectionLevelChangeCompact_toSections_val (H : OpenSubgroup G) (q : levelK H) :
    (includeL (H ⊓ L) (orbitSectionLevelChangeCompact h hU hP K L hK hL hPK hPL
      ν π hν hr e he H q)).val = (includeK H q).val := rfl

set_option hygiene false in
local notation "changeLevel" => orbitSectionLevelChangeCompact h hU hP K L hK hL hPK hPL ν π hν hr e he

/-- A derivative seminorm after change of compact picture is bounded by
a finite supremum of derivative seminorms in the original compact picture. -/
theorem exists_orbitSectionLevelChangeCompact_seminorm_bound
    (H : OpenSubgroup G) (l : List J) (ℓ : Module.Dual ℂ (Pic L)) :
    ∃ t : Finset (List J × Module.Dual ℂ (Pic K)), ∃ c : ℝ≥0,
      ∀ q : levelK H, seminormL (H ⊓ L) (l, ℓ) (changeLevel H q) ≤
        (c : ℝ) * (t.sup (seminormK H)) q := by
  classical
  obtain ⟨s, T, hT⟩ := exists_compactRestriction_sum h hU hP K L hK hL hPK hPL ν π hν hr e
  let a (p : P.prod P) : M := h.projection ⟨p.val.1, p.property.1⟩ *
    (h.projection ⟨p.val.2, p.property.2⟩)⁻¹
  let W (p : P.prod P) := unitaryUnramifiedSmoothEvaluation ν e he (a p)
  let d (p : P.prod P) := ℓ.comp (T p)
  let f (p : P.prod P) (q : levelK H) :=
    orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK (d p) (includeK H q)
  have hsum (q : levelK H) :
      orbitSectionCoefficient ν π e h hU L hP hL hν hr hPL ℓ (includeL (H ⊓ L) (changeLevel H q)) =
        ∑ p ∈ s, W p * f p q := by
    apply Subtype.ext
    funext z
    rw [orbitSectionCoefficient_apply]
    let F := productInducedOrbitPullback ν π e h hU (includeK H q).val
    change ℓ (restrictionL F z) = _
    rw [hT F z, map_sum]
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro p hp
    rw [map_smul]
    rfl
  let n := l.length
  let t : Finset (List J × Module.Dual ℂ (Pic K)) :=
    s.biUnion fun p => (torusDerivativeLists (J := J) n).image fun m => (m, d p)
  let C (p : P.prod P) : ℝ := (2 : ℝ)^n * smoothTorusDerivativeControl n (W p)
  have hC (p : P.prod P) : 0 ≤ C p := mul_nonneg (by positivity) (apply_nonneg _ _)
  let c : ℝ≥0 := ⟨∑ p ∈ s, C p, Finset.sum_nonneg fun p _ => hC p⟩
  refine ⟨t, c, fun q => ?_⟩
  have hcontrol (p : P.prod P) (hp : p ∈ s) : smoothTorusDerivativeControl n (f p q) ≤
      (t.sup (seminormK H)) q := by
    unfold smoothTorusDerivativeControl
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro m hm
    have hmem : (m, d p) ∈ t := Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    exact (Finset.le_sup (f := seminormK H) hmem) q
  change smoothTorusSeminorm J l
    (orbitSectionCoefficient ν π e h hU L hP hL hν hr hPL ℓ
      (includeL (H ⊓ L) (changeLevel H q))) ≤ _
  rw [hsum q, smoothTorusSeminorm_apply, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p ∈ s, ‖smoothTorusDerivative J l (W p * f p q)‖
      ≤ ∑ p ∈ s, C p * (t.sup (seminormK H)) q := by
        refine Finset.sum_le_sum fun p hp => ?_
        change smoothTorusSeminorm J l (W p * f p q) ≤ _
        apply (smoothTorusSeminorm_le_iff J l _ (mul_nonneg (hC p) (apply_nonneg _ _))).mpr
        intro z
        exact (norm_torusPartialDerivList_mul_le_control n (W p) (f p q) l le_rfl z).trans
          (mul_le_mul_of_nonneg_left (hcontrol p hp) (hC p))
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- Changing compact picture is continuous at the two original section levels. -/
theorem continuous_orbitSectionLevelChangeCompact (H : OpenSubgroup G) :
    Continuous (changeLevel H) := by
  refine WithSeminorms.continuous_of_isBounded
    (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK H)
    (OrbitSectionLevel.withSeminorms ν π e h hU L hP hL hν hr hPL (H ⊓ L)) _ ?_
  intro i
  obtain ⟨t, c, hc⟩ := exists_orbitSectionLevelChangeCompact_seminorm_bound
    h hU hP K L hK hL hPK hPL ν π hν hr e he H i.1 i.2
  exact ⟨t, c, fun q => by
    simpa only [Seminorm.comp_apply, smul_apply, NNReal.smul_def, smul_eq_mul, Prod.mk.eta] using hc q⟩

/-- Any finite collection of output seminorms is controlled simultaneously by a
finite collection of input seminorms. -/
theorem exists_orbitSectionLevelChangeCompact_finsetSup_bound
    (H : OpenSubgroup G) (s : Finset (List J × Module.Dual ℂ (Pic L))) :
    ∃ t : Finset (List J × Module.Dual ℂ (Pic K)), ∃ c : ℝ≥0,
      ∀ q : levelK H, (s.sup (seminormL (H ⊓ L))) (changeLevel H q) ≤
        (c : ℝ) * (t.sup (seminormK H)) q := by
  let p := (s.sup (seminormL (H ⊓ L))).comp (changeLevel H)
  have hcont : Continuous p :=
    (Seminorm.continuous_finsetSup fun i _ =>
      (OrbitSectionLevel.withSeminorms ν π e h hU L hP hL hν hr hPL (H ⊓ L)).continuous_seminorm i).comp
      (continuous_orbitSectionLevelChangeCompact h hU hP K L hK hL hPK hPL ν π hν hr e he H)
  obtain ⟨t, c, -, hc⟩ := Seminorm.bound_of_continuous
    (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK H) p hcont
  exact ⟨t, c, fun q => by
    simpa only [p, Seminorm.comp_apply, smul_apply, NNReal.smul_def, smul_eq_mul] using hc q⟩

end Langlands.HarishChandraSchwartz
