import Langlands.LinearAlgebra.GMFamilySliceSpecial
import Langlands.LinearAlgebra.GMFamilyDescentVolume

/-! # Enlarging a coarse subspace by central directions -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Module Submodule

namespace Langlands.GMFamily

namespace CentreReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {b a₁ : Submodule ℝ E}

/-- The central directions orthogonal to `b`. -/
abbrev surplus (R : Finset E) (b : Submodule ℝ E) : Submodule ℝ E := centralSpace R ⊓ bᗮ

/-- The enlargement of `b` by the central directions orthogonal to it. -/
abbrev hull (R : Finset E) (b : Submodule ℝ E) : Submodule ℝ E := b ⊔ surplus R b

/-- The central space compatible with `b`: the orthogonal projection to the central space
preserves `b`. -/
def IsCentreSplit (R : Finset E) (b : Submodule ℝ E) : Prop :=
  ∀ x ∈ b, (centralSpace R).starProjection x ∈ b

omit [FiniteDimensional ℝ E] in
theorem inner_central {r w : E} (hr : r ∈ R) (hw : w ∈ centralSpace R) : ⟪r, w⟫ = 0 := by
  have h := Submodule.mem_iInf _ |>.mp hw r
  exact (Submodule.mem_iInf _ |>.mp h hr) |> mem_orthogonal_singleton_iff_inner_right.mp

omit [FiniteDimensional ℝ E] in
theorem le_hull : b ≤ hull R b := le_sup_left

omit [FiniteDimensional ℝ E] in
theorem surplus_le_hull : surplus R b ≤ hull R b := le_sup_right

theorem orthogonal_invariant (hZ : IsCentreSplit R b) {y : E} (hy : y ∈ bᗮ) :
    (centralSpace R).starProjection y ∈ bᗮ := by
  intro x hx
  rw [real_inner_comm, inner_starProjection_left_eq_right]
  exact inner_left_of_mem_orthogonal (hZ x hx) hy

/-- A central vector is the sum of its central component in `b` and a surplus vector. -/
theorem central_decomp (hZ : IsCentreSplit R b) {z : E} (hz : z ∈ centralSpace R) :
    ∃ u ∈ b ⊓ centralSpace R, ∃ w ∈ surplus R b, z = u + w := by
  let Z := centralSpace R
  refine ⟨Z.starProjection (b.starProjection z), ⟨hZ _ (b.starProjection_apply_mem z),
    Z.starProjection_apply_mem _⟩, Z.starProjection (z - b.starProjection z),
    ⟨Z.starProjection_apply_mem _, orthogonal_invariant hZ (b.sub_starProjection_mem_orthogonal z)⟩,
    ?_⟩
  rw [← map_add, add_sub_cancel, starProjection_eq_self_iff.mpr hz]

theorem central_le_hull (hZ : IsCentreSplit R b) : centralSpace R ≤ hull R b := by
  intro z hz
  obtain ⟨u, hu, w, hw, rfl⟩ := central_decomp hZ hz
  exact add_mem (le_hull hu.1) (surplus_le_hull hw)

theorem central_eq_sup (hZ : IsCentreSplit R b) :
    centralSpace R = (b ⊓ centralSpace R) ⊔ surplus R b := by
  apply le_antisymm
  · intro z hz
    obtain ⟨u, hu, w, hw, rfl⟩ := central_decomp hZ hz
    exact add_mem (mem_sup_left hu) (mem_sup_right hw)
  · exact sup_le inf_le_right inf_le_left

omit [FiniteDimensional ℝ E] in
theorem inner_surplus_of_mem {x w : E} (hx : x ∈ b) (hw : w ∈ surplus R b) : ⟪x, w⟫ = 0 :=
  inner_right_of_mem_orthogonal hx hw.2

omit [FiniteDimensional ℝ E] in
theorem mem_orthogonal_hull {x : E} :
    x ∈ (hull R b)ᗮ ↔ x ∈ bᗮ ∧ x ∈ (surplus R b)ᗮ := by
  rw [← Submodule.inf_orthogonal]
  rfl

omit [FiniteDimensional ℝ E] in
theorem orthogonal_hull_of_central {x : E} (hb : x ∈ bᗮ) (hZ : x ∈ (centralSpace R)ᗮ) :
    x ∈ (hull R b)ᗮ :=
  mem_orthogonal_hull.mpr ⟨hb, orthogonal_le inf_le_left hZ⟩

omit [FiniteDimensional ℝ E] in
/-- An element of the enlargement orthogonal to the surplus lies in `b`. -/
theorem mem_of_mem_hull {x : E} (hx : x ∈ hull R b) (ho : x ∈ (surplus R b)ᗮ) : x ∈ b := by
  obtain ⟨y, hy, w, hw, rfl⟩ := mem_sup.mp hx
  have hw0 : w = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have h := ho w hw
    rw [inner_add_right, real_inner_comm y w, inner_surplus_of_mem hy hw, zero_add] at h
    exact h
  rw [hw0, add_zero]
  exact hy

/-- The restrictions of roots to `b` and to its enlargement agree. -/
theorem coe_restrictedRoot_hull {r : E} (hr : r ∈ R) :
    (restrictedRoot (hull R b) r : E) = (restrictedRoot b r : E) := by
  change (hull R b).starProjection r = _
  apply eq_starProjection_of_mem_of_inner_eq_zero (le_hull (restrictedRoot b r).prop)
  intro w hw
  obtain ⟨y, hy, u, hu, rfl⟩ := mem_sup.mp hw
  rw [inner_add_right]
  change ⟪r - b.starProjection r, y⟫ + ⟪r - b.starProjection r, u⟫ = 0
  rw [b.starProjection_inner_eq_zero r y hy, zero_add, inner_sub_left, inner_central hr hu.1,
    inner_right_of_mem_orthogonal (b.starProjection_apply_mem r) hu.2, sub_zero]

theorem restrictedRoot_hull_eq_zero_iff {r : E} (hr : r ∈ R) :
    restrictedRoot (hull R b) r = 0 ↔ restrictedRoot b r = 0 := by
  rw [← Submodule.coe_eq_zero, coe_restrictedRoot_hull hr, Submodule.coe_eq_zero]

omit [FiniteDimensional ℝ E] in
theorem posSet_add_central {p w : E} (hw : w ∈ centralSpace R) : posSet R (p + w) = posSet R p := by
  ext r
  simp only [mem_posSet_iff]
  refine and_congr_right fun hr => ?_
  rw [inner_add_right, inner_central hr hw, add_zero]

theorem isRegular_add_central {L : Submodule ℝ E} {p w : E} (hw : w ∈ centralSpace R)
    (hwL : w ∈ L) : IsRegular R L (p + w) ↔ IsRegular R L p := by
  unfold IsRegular
  have hmem : p + w ∈ L ↔ p ∈ L := ⟨fun h => by simpa using L.sub_mem h hwL,
    fun h => L.add_mem h hwL⟩
  rw [hmem]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro r hr
  rw [inner_add_right, inner_central hr hw, add_zero]

/-- The chambers of `b` and of its enlargement are the same sets of roots. -/
theorem parabolics_hull : parabolics R (hull R b) = parabolics R b := by
  ext S
  rw [mem_parabolics_iff, mem_parabolics_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := mem_sup.mp hh.1
    refine ⟨y, ⟨hy, fun r hr hr0 => ?_⟩, posSet_add_central hw.1⟩
    have h := hh.2 r hr ((restrictedRoot_hull_eq_zero_iff hr).not.mpr hr0)
    rwa [inner_add_right, inner_central hr hw.1, add_zero] at h
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, ⟨le_hull hh.1, fun r hr hr0 =>
      hh.2 r hr ((restrictedRoot_hull_eq_zero_iff hr).not.mp hr0)⟩, rfl⟩


/-! ### Denominators and supplementary functions -/

theorem restrictedRoot_hull {r : E} (hr : r ∈ R) :
    restrictedRoot (hull R b) r = Submodule.inclusion le_hull (restrictedRoot b r) :=
  Subtype.ext (coe_restrictedRoot_hull hr)

theorem restrictedRoots_hull {S : Finset E} (hS : S ⊆ R) :
    restrictedRoots (hull R b) S =
      (restrictedRoots b S).image (Submodule.inclusion (le_hull (R := R) (b := b))) := by
  ext w
  simp only [restrictedRoots, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, ⟨r, hr, rfl⟩, (restrictedRoot_hull (hS hr)).symm⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, restrictedRoot_hull (hS hr)⟩

theorem simpleRoots_hull {S : Finset E} (hS : S ⊆ R) :
    simpleRoots (hull R b) S =
      (simpleRoots b S).image (Submodule.inclusion (le_hull (R := R) (b := b))) := by
  let f := Submodule.inclusion (le_hull (R := R) (b := b))
  have hf : Function.Injective f := Submodule.inclusion_injective _
  ext w
  simp only [simpleRoots, Finset.mem_filter, Finset.mem_image, restrictedRoots_hull hS]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hind⟩
    refine ⟨v, ⟨hv, fun ⟨u, hu, x, hx, he⟩ => hind ⟨f u, ⟨u, hu, rfl⟩, f x, ⟨x, hx, rfl⟩, ?_⟩⟩, rfl⟩
    rw [he, map_add]
  · rintro ⟨v, ⟨hv, hind⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨x, hx, rfl⟩, he⟩
    apply hind
    refine ⟨u, hu, x, hx, hf ?_⟩
    rw [he, map_add]

theorem extendParam_apply_of_mem {c : Submodule ℝ E} (hbc : b ≤ c) (Λ : StrongDual ℝ b) (v : b) :
    extendParam b c Λ (Submodule.inclusion hbc v) = Λ v := by
  change Λ (b.orthogonalProjectionOnto (v : E)) = Λ v
  rw [orthogonalProjectionOnto_mem_subspace_eq_self]

/-- The denominators on `b` and on its enlargement agree. -/
theorem theta_hull {S : Finset E} (hS : S ⊆ R) (Λ : StrongDual ℝ b) :
    theta (hull R b) S (extendParam b (hull R b) Λ) = theta b S Λ := by
  let f := Submodule.inclusion (le_hull (R := R) (b := b))
  have hf : Function.Injective f := Submodule.inclusion_injective _
  have hmem (v : simpleRoots b S) : f v ∈ simpleRoots (hull R b) S := by
    rw [simpleRoots_hull hS]
    exact Finset.mem_image_of_mem _ v.prop
  let e : simpleRoots b S ≃ simpleRoots (hull R b) S :=
    Equiv.ofBijective (fun v => ⟨f v, hmem v⟩)
      ⟨fun v w h => Subtype.ext (hf (congrArg Subtype.val h)), fun w => by
        have hw : (w : hull R b) ∈ (simpleRoots b S).image f := by
          rw [← simpleRoots_hull hS]
          exact w.prop
        obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hw
        exact ⟨⟨v, hv⟩, Subtype.ext he⟩⟩
  unfold theta thetaOf
  congr 1
  · congr 2
    rw [← gramVolume_reindex e]
    rfl
  · refine (Fintype.prod_equiv e _ _ (fun v => ?_)).symm
    change Complex.I * (Λ v : ℂ) = Complex.I * (extendParam b (hull R b) Λ (f v) : ℂ)
    rw [extendParam_apply_of_mem]

theorem extendParam_extendParam {c d : Submodule ℝ E} (hbc : b ≤ c) (Λ : StrongDual ℝ b) :
    extendParam c d (extendParam b c Λ) = extendParam b d Λ := by
  ext x
  change Λ (restrictedRoot b (restrictedRoot c (x : E) : E)) = Λ (restrictedRoot b (x : E))
  rw [restrictedRoot_nested hbc]

theorem inducedFamily_hull (c₁ : Finset E → StrongDual ℝ a₁ → ℂ) (S : Finset E)
    (Λ : StrongDual ℝ b) :
    inducedFamily R (hull R b) a₁ c₁ S (extendParam b (hull R b) Λ) =
      inducedFamily R b a₁ c₁ S Λ := by
  unfold inducedFamily
  rw [extendParam_extendParam le_hull]

/-- The supplementary functions of the induced families on `b` and on its enlargement agree. -/
theorem cM_hull (c₁ : Finset E → StrongDual ℝ a₁ → ℂ) (Λ : StrongDual ℝ b) :
    cM R (hull R b) (inducedFamily R (hull R b) a₁ c₁) (extendParam b (hull R b) Λ) =
      cM R b (inducedFamily R b a₁ c₁) Λ := by
  unfold cM
  rw [parabolics_hull]
  apply Finset.sum_congr rfl
  intro S hS
  rw [inducedFamily_hull, theta_hull (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)]

theorem generic_hull {Λ : StrongDual ℝ b}
    (hΛ : ∀ r ∈ R, restrictedRoot b r ≠ 0 → Λ (restrictedRoot b r) ≠ 0) :
    ∀ r ∈ R, restrictedRoot (hull R b) r ≠ 0 →
      extendParam b (hull R b) Λ (restrictedRoot (hull R b) r) ≠ 0 := by
  intro r hr hr0
  rw [restrictedRoot_hull hr, extendParam_apply_of_mem]
  exact hΛ r hr ((restrictedRoot_hull_eq_zero_iff hr).not.mp hr0)

theorem isSpecialSubspace_hull {m : E → ℝ} (hm : IsSpecialSubspace R b a₁ m) :
    IsSpecialSubspace R (hull R b) a₁ m := by
  refine ⟨hm.1, fun β hβ => ?_⟩
  by_cases hb : (β : E) ∈ b
  · let β₀ : b := ⟨β, hb⟩
    have hβ₀ : β₀ ≠ 0 := by
      intro h
      apply hβ
      have h' : (β₀ : E) = 0 := by rw [h]; rfl
      exact Subtype.ext h'
    have hfilter : R.filter (fun r => restrictedRoot (hull R b) r = β) =
        R.filter (fun r => restrictedRoot b r = β₀) := by
      apply Finset.filter_congr
      intro r hr
      rw [← Subtype.coe_inj, coe_restrictedRoot_hull hr, ← Subtype.coe_inj]
    rw [hfilter]
    exact le_hull (hm.2 β₀ hβ₀)
  · have hfilter : R.filter (fun r => restrictedRoot (hull R b) r = β) = ∅ := by
      apply Finset.filter_false_of_mem
      intro r hr he
      apply hb
      rw [← he, coe_restrictedRoot_hull hr]
      exact (restrictedRoot b r).prop
    rw [hfilter, Finset.sum_empty]
    exact zero_mem _

/-! ### Volumes -/

private theorem finrank_eq_of_decomp {U U' X : Submodule ℝ E} (hsup : U' ⊔ X = U)
    (hinf : U' ⊓ X = ⊥) : finrank ℝ U = finrank ℝ U' + finrank ℝ X := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U' X
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact h

omit [FiniteDimensional ℝ E] in
theorem surplus_le_fine (hZa₁ : centralSpace R ≤ a₁) : surplus R b ≤ a₁ :=
  inf_le_left.trans hZa₁

theorem sub_central_mem_orthogonal_hull {u : E} (hu : u ∈ bᗮ) (hZ : IsCentreSplit R b) :
    u - (centralSpace R).starProjection u ∈ (hull R b)ᗮ :=
  orthogonal_hull_of_central (sub_mem hu (orthogonal_invariant hZ hu))
    ((centralSpace R).sub_starProjection_mem_orthogonal u)

theorem central_mem_surplus {u : E} (hu : u ∈ bᗮ) (hZ : IsCentreSplit R b) :
    (centralSpace R).starProjection u ∈ surplus R b :=
  ⟨(centralSpace R).starProjection_apply_mem u, orthogonal_invariant hZ hu⟩

theorem normal_decomp (hZ : IsCentreSplit R b) (hZa₁ : centralSpace R ≤ a₁) :
    (a₁ ⊓ (hull R b)ᗮ) ⊔ surplus R b = a₁ ⊓ bᗮ ∧ (a₁ ⊓ (hull R b)ᗮ) ⊓ surplus R b = ⊥ := by
  constructor
  · apply le_antisymm
    · exact sup_le (inf_le_inf_left _ (orthogonal_le le_hull))
        (le_inf (surplus_le_fine hZa₁) inf_le_right)
    · rintro u ⟨hu₁, hu⟩
      have h := add_mem (mem_sup_left (S := a₁ ⊓ (hull R b)ᗮ) (T := surplus R b)
        ⟨sub_mem hu₁ (hZa₁ ((centralSpace R).starProjection_apply_mem u)),
          sub_central_mem_orthogonal_hull hu hZ⟩) (mem_sup_right (central_mem_surplus hu hZ))
      rwa [sub_add_cancel] at h
  · rw [eq_bot_iff]
    rintro x ⟨⟨_, hx⟩, hxs⟩
    have := inf_orthogonal_eq_bot (hull R b)
    rw [eq_bot_iff] at this
    exact this ⟨surplus_le_hull hxs, hx⟩

theorem noncentral_decomp (hZ : IsCentreSplit R b) (hZa₁ : centralSpace R ≤ a₁) :
    (a₁ ⊓ (centralSpace R)ᗮ) ⊔ surplus R b = a₁ ⊓ (b ⊓ centralSpace R)ᗮ ∧
      (a₁ ⊓ (centralSpace R)ᗮ) ⊓ surplus R b = ⊥ := by
  let Z := centralSpace R
  constructor
  · apply le_antisymm
    · refine sup_le (inf_le_inf_left _ (orthogonal_le inf_le_right))
        (le_inf (surplus_le_fine hZa₁) ?_)
      exact (inf_le_right : surplus R b ≤ bᗮ).trans (orthogonal_le inf_le_left)
    · rintro y ⟨hy₁, hy⟩
      have hyb : Z.starProjection y ∈ bᗮ := by
        intro x hx
        rw [real_inner_comm, inner_starProjection_left_eq_right]
        exact inner_left_of_mem_orthogonal (K := b ⊓ centralSpace R)
          (Submodule.mem_inf.mpr ⟨hZ x hx, Z.starProjection_apply_mem x⟩) hy
      have h := add_mem (mem_sup_left (S := a₁ ⊓ Zᗮ) (T := surplus R b)
        ⟨sub_mem hy₁ (hZa₁ (Z.starProjection_apply_mem y)), Z.sub_starProjection_mem_orthogonal y⟩)
        (mem_sup_right (⟨Z.starProjection_apply_mem y, hyb⟩ : Z.starProjection y ∈ surplus R b))
      rwa [sub_add_cancel] at h
  · rw [eq_bot_iff]
    rintro x ⟨⟨_, hx⟩, hxs⟩
    have := inf_orthogonal_eq_bot Z
    rw [eq_bot_iff] at this
    exact this ⟨hxs.1, hx⟩

theorem starProjection_normal_eq (hZ : IsCentreSplit R b) (hZa₁ : centralSpace R ≤ a₁)
    {L : Submodule ℝ E} (hZL : centralSpace R ≤ L) {w : E} (hw : w ∈ Lᗮ) :
    (a₁ ⊓ bᗮ).starProjection w = (a₁ ⊓ (hull R b)ᗮ).starProjection w := by
  let U' := a₁ ⊓ (hull R b)ᗮ
  let Z := centralSpace R
  apply eq_starProjection_of_mem_of_inner_eq_zero
    (inf_le_inf_left _ (orthogonal_le le_hull) (U'.starProjection_apply_mem w))
  rintro u ⟨hu₁, hu⟩
  have hwZ : w ∈ Zᗮ := orthogonal_le hZL hw
  have hs := central_mem_surplus hu hZ
  have hmem : u - Z.starProjection u ∈ U' :=
    ⟨sub_mem hu₁ (hZa₁ (Z.starProjection_apply_mem u)), sub_central_mem_orthogonal_hull hu hZ⟩
  have hP : U'.starProjection w ∈ (hull R b)ᗮ := (U'.starProjection_apply_mem w).2
  have h1 := U'.starProjection_inner_eq_zero w _ hmem
  have h2 : ⟪w, Z.starProjection u⟫ = 0 :=
    inner_left_of_mem_orthogonal (Z.starProjection_apply_mem u) hwZ
  have h3 : ⟪U'.starProjection w, Z.starProjection u⟫ = 0 :=
    inner_left_of_mem_orthogonal (surplus_le_hull hs) hP
  calc ⟪w - U'.starProjection w, u⟫
      = ⟪w - U'.starProjection w, u - Z.starProjection u⟫ +
          (⟪w, Z.starProjection u⟫ - ⟪U'.starProjection w, Z.starProjection u⟫) := by
        rw [← inner_sub_left, ← inner_add_right, sub_add_cancel]
    _ = 0 := by rw [h1, h2, h3, sub_zero, add_zero]

/-- The descent coefficients for `b` with its central part and for the enlargement with the
full central space agree. -/
theorem dDescent_hull (hZ : IsCentreSplit R b) (hZa₁ : centralSpace R ≤ a₁)
    {L : Submodule ℝ E} (hZL : centralSpace R ≤ L) :
    dDescent b (b ⊓ centralSpace R) a₁ L = dDescent (hull R b) (centralSpace R) a₁ L := by
  obtain ⟨hU, hU'⟩ := normal_decomp hZ hZa₁ (b := b)
  obtain ⟨hV, hV'⟩ := noncentral_decomp hZ hZa₁ (b := b)
  have dU := finrank_eq_of_decomp hU hU'
  have dV := finrank_eq_of_decomp hV hV'
  unfold dDescent measureFactor
  by_cases h : finrank ℝ (a₁ ⊓ (hull R b)ᗮ : Submodule ℝ E) + finrank ℝ (a₁ ⊓ Lᗮ : Submodule ℝ E) =
      finrank ℝ (a₁ ⊓ (centralSpace R)ᗮ : Submodule ℝ E)
  · rw [ite_eq_left h, ite_eq_left (by omega), gramVolume_join_orthogonalProjection,
      gramVolume_join_orthogonalProjection]
    congr 1
    funext j
    rw [starProjection_orthogonal_val, starProjection_orthogonal_val,
      starProjection_normal_eq hZ hZa₁ hZL ((stdOrthonormalBasis ℝ (a₁ ⊓ Lᗮ : Submodule ℝ E) j).prop.2)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-! ### Descent points and sections -/

omit [FiniteDimensional ℝ E] in
theorem central_le_of_mem_leviSpaces (hZa₁ : centralSpace R ≤ a₁) {L : Submodule ℝ E}
    (hL : L ∈ leviSpaces R a₁) : centralSpace R ≤ L := by
  obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hL
  refine le_inf hZa₁ (le_iInf₂ fun α hα => ?_)
  exact iInf₂_le α (Finset.mem_filter.mp hα).1

theorem offset_hull (hZ : IsCentreSplit R b) (hZa₁ : centralSpace R ≤ a₁) {ξ : E}
    (hξ : ξ ∈ a₁ ⊓ bᗮ) : ξ - (centralSpace R).starProjection ξ ∈ a₁ ⊓ (hull R b)ᗮ :=
  ⟨sub_mem hξ.1 (hZa₁ ((centralSpace R).starProjection_apply_mem ξ)),
    sub_central_mem_orthogonal_hull hξ.2 hZ⟩

omit [FiniteDimensional ℝ E] in
theorem le_orthogonal_surplus : b ≤ (surplus R b)ᗮ :=
  b.le_orthogonal_orthogonal.trans (orthogonal_le inf_le_right)

/-- The descent points for the enlargement and the full central space correspond to those for
`b` and its central part, by adding the central component of the offset. -/
theorem descentPoint_hull_iff (hZ : IsCentreSplit R b) {L : Submodule ℝ E}
    (hZL : centralSpace R ≤ L) {ξ : E} (hξ : ξ ∈ bᗮ) (p : E) :
    (p ∈ L ⊓ (centralSpace R)ᗮ ∧
        p - (ξ - (centralSpace R).starProjection ξ) ∈ hull R b ⊓ (centralSpace R)ᗮ) ↔
      (p + (centralSpace R).starProjection ξ ∈ L ⊓ (b ⊓ centralSpace R)ᗮ ∧
        p + (centralSpace R).starProjection ξ - ξ ∈ b ⊓ (b ⊓ centralSpace R)ᗮ) := by
  let Z := centralSpace R
  let ξz := Z.starProjection ξ
  have hξz : ξz ∈ surplus R b := central_mem_surplus hξ hZ
  have hzorth : ξz ∈ (b ⊓ Z)ᗮ := orthogonal_le inf_le_left hξz.2
  have hsub : p + ξz - ξ = p - (ξ - ξz) := by abel
  have hZsplit : ∀ x : E, x ∈ (b ⊓ Z)ᗮ → x ∈ (surplus R b)ᗮ → x ∈ Zᗮ := by
    intro x h1 h2
    show x ∈ (centralSpace R)ᗮ
    rw [central_eq_sup hZ, ← Submodule.inf_orthogonal]
    exact ⟨h1, h2⟩
  change (p ∈ L ⊓ Zᗮ ∧ p - (ξ - ξz) ∈ hull R b ⊓ Zᗮ) ↔
    (p + ξz ∈ L ⊓ (b ⊓ Z)ᗮ ∧ p + ξz - ξ ∈ b ⊓ (b ⊓ Z)ᗮ)
  constructor
  · rintro ⟨⟨hpL, hpZ⟩, hh, hhZ⟩
    refine ⟨⟨L.add_mem hpL (hZL hξz.1), add_mem (orthogonal_le inf_le_right hpZ) hzorth⟩, ?_, ?_⟩
    · rw [hsub]
      exact mem_of_mem_hull hh (orthogonal_le inf_le_left hhZ)
    · rw [hsub]
      exact orthogonal_le inf_le_right hhZ
  · rintro ⟨⟨hpL, hpz⟩, hb', hbz⟩
    have hp : p = (p + ξz) - ξz := by abel
    have hp' : p = (p + ξz - ξ) + (ξ - ξz) := by abel
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hp]
      exact L.sub_mem hpL (hZL hξz.1)
    · apply hZsplit
      · rw [hp]
        exact sub_mem hpz hzorth
      · rw [hp']
        exact add_mem (le_orthogonal_surplus hb')
          (orthogonal_le inf_le_left (Z.sub_starProjection_mem_orthogonal ξ))
    · rw [← hsub]
      exact le_hull hb'
    · rw [← hsub]
      exact hZsplit _ hbz (le_orthogonal_surplus hb')

/-- The general-position condition on an offset, for a coarse subspace `b`, a central part `z`
and a fine flat `a₁`. -/
def IsGenericOffset (R : Finset E) (b z a₁ : Submodule ℝ E) (ξ : E) : Prop :=
  ∀ L ∈ leviSpaces R a₁, dDescent b z a₁ L ≠ 0 →
    ∀ p : E, p ∈ L ⊓ zᗮ → p - ξ ∈ b ⊓ zᗮ → IsRegular R L p

theorem isGenericOffset_hull_iff (hZ : IsCentreSplit R b) (hZa₁ : centralSpace R ≤ a₁)
    {ξ : E} (hξ : ξ ∈ bᗮ) :
    IsGenericOffset R b (b ⊓ centralSpace R) a₁ ξ ↔
      IsGenericOffset R (hull R b) (centralSpace R) a₁
        (ξ - (centralSpace R).starProjection ξ) := by
  let ξz := (centralSpace R).starProjection ξ
  have hξz : ξz ∈ centralSpace R := (centralSpace R).starProjection_apply_mem ξ
  unfold IsGenericOffset
  apply forall₂_congr
  intro L hL
  have hZL := central_le_of_mem_leviSpaces hZa₁ hL
  rw [dDescent_hull hZ hZa₁ hZL]
  apply imp_congr_right
  intro _
  constructor
  · intro H p hpL hpb
    obtain ⟨h1, h2⟩ := (descentPoint_hull_iff hZ hZL hξ p).mp ⟨hpL, hpb⟩
    exact (isRegular_add_central hξz (hZL hξz)).mp (H _ h1 h2)
  · intro H p hpL hpb
    have hpp : p - ξz + ξz = p := sub_add_cancel p ξz
    have hpt := (descentPoint_hull_iff hZ hZL hξ (p - ξz)).mpr ⟨by rwa [hpp], by rwa [hpp]⟩
    have h := (isRegular_add_central hξz (hZL hξz)).mpr (H _ hpt.1 hpt.2)
    rwa [hpp] at h

omit [FiniteDimensional ℝ E] in
theorem hull_le (hb : b ≤ a₁) (hZa₁ : centralSpace R ≤ a₁) : hull R b ≤ a₁ :=
  sup_le hb (surplus_le_fine hZa₁)

/-- The descent sections for `b` and for its enlargement agree. -/
theorem descentSection_hull (hZ : IsCentreSplit R b) (hb : b ≤ a₁)
    (hZa₁ : centralSpace R ≤ a₁) {L : Submodule ℝ E} (hZL : centralSpace R ≤ L) (hLa₁ : L ≤ a₁)
    (hd : dDescent (hull R b) (centralSpace R) a₁ L ≠ 0) {ξ : E} (hξ : ξ ∈ a₁ ⊓ bᗮ) :
    descentSection R b (b ⊓ centralSpace R) ξ L =
      descentSection R (hull R b) (centralSpace R) (ξ - (centralSpace R).starProjection ξ) L := by
  have hoff := offset_hull hZ hZa₁ hξ
  obtain ⟨p, ⟨hpL, hpA⟩, -⟩ := existsUnique_descentPoint (central_le_hull hZ) (hull_le hb hZa₁)
    hZL hLa₁ hd hoff
  rw [descentSection_eq_posSet (central_le_hull hZ) (hull_le hb hZa₁) hZL hLa₁ hd hoff hpL hpA]
  obtain ⟨h1, h2⟩ := (descentPoint_hull_iff hZ hZL hξ.2 p).mp ⟨hpL, hpA⟩
  rw [descentSection_eq_posSet inf_le_left hb (inf_le_right.trans hZL) hLa₁
    (by rwa [dDescent_hull hZ hZa₁ hZL]) hξ h1 h2,
    posSet_add_central ((centralSpace R).starProjection_apply_mem ξ)]

end CentreReduction

end Langlands.GMFamily
