import Langlands.LocalFactor.Ramification.Herbrand.TruncationWeilComapProof
import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof

/-!
# Weil truncation quotients through a transitivity index

Through a transitivity index `μ`, the inclusion of local Weil groups induces a
filtered topological isomorphism `W_E / R_E(x) ≃ₜ* W_F / R_F(x)` for every
`-1 ≤ x ≤ μ`.
-/

noncomputable section

namespace Langlands.Ramification.Kummer

open LocalClassField HerbrandBridge Weil.Local
open _root_.Langlands.Ramification.Padic
open VirtualRepresentation.LocalWeil.Ramification

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Normality of the Weil upper group, pulled back from the absolute upper group;
the same local instance as in the statement module. -/
local instance (F : PadicField.{u} p) (x : ℝ) : (upperGroup F x).Normal :=
  Subgroup.Normal.comap inferInstance _

/-- Above `-1`, every finite upper ramification group lies in the inertia group. -/
theorem upperRamificationGroup_le_zero_of_neg_one_lt {F : PadicField.{u} p}
    (T : F.TopologicalData) (K : Type*) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier] {x : ℝ} (hx : -1 < x) :
    upperRamificationGroup T K x ≤ upperRamificationGroup T K 0 := by
  rw [upperRamificationGroup_eq_lower, upperRamificationGroup_eq_lower, herbrandPsi_zero]
  apply lowerRamificationGroupInt_antitone
  have h : herbrandPsi T K (-1) < herbrandPsi T K x := herbrandPsi_strictMono T K hx
  rw [herbrandPsi_neg_one] at h
  have h' : (-1 : ℤ) < ⌈herbrandPsi T K x⌉ := Int.lt_ceil.mpr (by exact_mod_cast h)
  simp only [Int.ceil_zero]
  omega

/-- Above `-1`, the absolute upper group lies in the absolute inertia group. -/
theorem absoluteUpperRamificationGroup_le_inertia_of_neg_one_lt (F : PadicField.{u} p)
    {x : ℝ} (hx : -1 < x) :
    absoluteUpperRamificationGroup F x ≤ F.absoluteInertia F.canonicalTopologicalData := by
  rw [← absoluteUpperCanonicalInertia F]
  intro σ hσ
  rw [mem_absoluteUpperRamificationGroup_iff] at hσ ⊢
  intro L
  exact upperRamificationGroup_le_zero_of_neg_one_lt _ _ hx (hσ L)

/-- An absolute Galois element in inertia is the projection of a Weil element in
degree zero. -/
theorem exists_localProjection_eq_of_mem_inertia (F : PadicField.{u} p)
    {h : Field.absoluteGaloisGroup F.Carrier}
    (hh : h ∈ F.absoluteInertia F.canonicalTopologicalData) :
    ∃ i : localWeilGroup F, localProjection F i = h := by
  rw [← localResidueDegree_ker F, MonoidHom.mem_ker] at hh
  refine ⟨⟨((h, 1) : Field.absoluteGaloisGroup F.Carrier × Weil.Degree), ?_⟩, rfl⟩
  change localResidueDegree F h = Weil.frobenius 1
  rw [map_one]
  exact hh

/-- Under transitivity at `μ`, every Weil element is a product of an element of
the image of `W_E` and an element of `R_F(x)`, for `-1 ≤ x ≤ μ`. -/
theorem exists_upperGroup_mul_mem_range (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ)
    (htrans : E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤)
    {x : ℝ} (hx : -1 ≤ x) (hxμ : x ≤ μ) (w : localWeilGroup F) :
    ∃ i ∈ upperGroup F x, w * i⁻¹ ∈ (intermediateWeilMap F E).toMonoidHom.range := by
  rcases hx.eq_or_lt with hx | hx
  · subst hx
    refine ⟨w, ?_, ?_⟩
    · rw [mem_upperGroup, absoluteUpperRamificationGroup_neg_one]
      exact Subgroup.mem_top _
    · rw [mul_inv_cancel]
      exact Subgroup.one_mem _
  · have hw : localProjection F w ∈
        E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ := by
      rw [htrans]
      exact Subgroup.mem_top _
    obtain ⟨g, hg, h, hh, hgh⟩ :=
      (Subgroup.mem_sup_of_normal_right (ht := absoluteUpperRamificationGroup_normal F μ)).mp hw
    obtain ⟨i, hi⟩ := exists_localProjection_eq_of_mem_inertia F
      (absoluteUpperRamificationGroup_le_inertia_of_neg_one_lt F (hx.trans_le hxμ) hh)
    refine ⟨i, ?_, ?_⟩
    · rw [mem_upperGroup, hi]
      exact absoluteUpperRamificationGroup_antitone F hxμ hh
    · rw [intermediateWeilMap_range]
      have e1 : localProjection F (w * i⁻¹) = g := by
        rw [map_mul, map_inv, hi, ← hgh, mul_inv_cancel_right]
      change localProjection F (w * i⁻¹) ∈ E.field.fixingSubgroup
      rw [e1]
      exact hg

/-- A continuous homomorphism of local Weil groups that is an open map, pulls back
`R_F(y)` to `R_K(y)` for `-1 ≤ y ≤ x`, and whose image together with `R_F(x)`
generates `W_F` elementwise, induces a filtered topological isomorphism of the
quotients by the upper groups of index `x`. -/
theorem weilQuotientIsoAlong_of_comap (K F : PadicField.{u} p)
    (ι : localWeilGroup K →ₜ* localWeilGroup F) (x : ℝ) (hx : -1 ≤ x)
    (hcomap : ∀ y : ℝ, -1 ≤ y → y ≤ x →
      (upperGroup F y).comap ι.toMonoidHom = upperGroup K y)
    (hsplit : ∀ w : localWeilGroup F,
      ∃ i ∈ upperGroup F x, w * i⁻¹ ∈ ι.toMonoidHom.range)
    (hιopen : IsOpenMap ι) :
    WeilQuotientIsoAlong K F ι x := by
  have hle : upperGroup K x ≤ (upperGroup F x).comap ι.toMonoidHom :=
    (hcomap x hx le_rfl).ge
  let f : localWeilGroup K ⧸ upperGroup K x →* localWeilGroup F ⧸ upperGroup F x :=
    QuotientGroup.map _ _ ι.toMonoidHom hle
  have hf : ∀ w, f (QuotientGroup.mk w) = QuotientGroup.mk (ι w) := fun w => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [hf, QuotientGroup.eq_one_iff] at hq
      rw [QuotientGroup.eq_one_iff, ← hcomap x hx le_rfl]
      exact hq
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      obtain ⟨i, hi, a, ha⟩ := hsplit w
      have ha' : ι a = w * i⁻¹ := ha
      refine ⟨QuotientGroup.mk a, ?_⟩
      rw [hf, QuotientGroup.eq, ha', mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
        mul_one]
      exact hi
  let e := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have he : ∀ w, e (QuotientGroup.mk w) = QuotientGroup.mk (ι w) := fun w => rfl
  have hcont : Continuous e := by
    rw [(QuotientGroup.isQuotientMap_mk (upperGroup K x)).continuous_iff]
    exact QuotientGroup.continuous_mk.comp ι.continuous
  have himage : ∀ s : Set (localWeilGroup K ⧸ upperGroup K x),
      e '' s = QuotientGroup.mk '' (ι '' (QuotientGroup.mk ⁻¹' s)) := by
    intro s
    ext q
    constructor
    · rintro ⟨r, hr, rfl⟩
      induction r using QuotientGroup.induction_on with
      | H w => exact ⟨ι w, ⟨w, hr, rfl⟩, (he w).symm⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk w, hw, he w⟩
  have hopen : IsOpenMap e := by
    intro s hs
    rw [himage]
    exact QuotientGroup.isOpenMap_coe _ (hιopen _ (hs.preimage QuotientGroup.continuous_mk))
  let hom := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  let φ : (localWeilGroup K ⧸ upperGroup K x) ≃ₜ* (localWeilGroup F ⧸ upperGroup F x) :=
    { toMulEquiv := e
      continuous_toFun := hcont
      continuous_invFun := hom.symm.continuous }
  refine ⟨φ, fun w => rfl, ?_⟩
  intro y hy hyx
  change e '' _ = _
  rw [Set.image_image]
  simp only [he]
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨ι a, ?_, rfl⟩
    rw [← hcomap y hy hyx] at ha
    exact ha
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨i, hi, a, ha⟩ := hsplit r
    have ha' : ι a = r * i⁻¹ := ha
    refine ⟨a, ?_, ?_⟩
    · rw [← hcomap y hy hyx]
      change ι a ∈ upperGroup F y
      rw [ha']
      exact Subgroup.mul_mem _ hr
        (Subgroup.inv_mem _ (upperGroup_antitone F hyx hi))
    · change QuotientGroup.mk (ι a) = QuotientGroup.mk r
      rw [QuotientGroup.eq, ha', mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      exact hi

/-- The intermediate Weil map is an open map: it is an embedding with open range. -/
theorem intermediateWeilMap_isOpenMap (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) :
    IsOpenMap (intermediateWeilMap F E) := by
  have hrange : IsOpen (Set.range (intermediateWeilMap F E)) := by
    have := pullbackFixingSubgroup_open F.Carrier E.field (localResidueDegree F)
    rwa [← intermediateWeilMap_range] at this
  exact (Topology.IsOpenEmbedding.mk (intermediateWeilMap_isEmbedding F E) hrange).isOpenMap

/-- Through the transitivity index, the Weil inclusion induces filtered
topological isomorphisms of the upper truncation quotients. -/
theorem truncationWeilQuotient : TruncationWeilQuotientStatement.{u} := by
  intro p _ F E μ htrans x hx hxμ
  exact weilQuotientIsoAlong_of_comap _ F (intermediateWeilMap F E) x hx
    (fun y hy hyx => truncationWeilComap p F E μ htrans y hy (hyx.trans hxμ))
    (exists_upperGroup_mul_mem_range F E μ htrans hx hxμ)
    (intermediateWeilMap_isOpenMap F E)

end Langlands.Ramification.Kummer
