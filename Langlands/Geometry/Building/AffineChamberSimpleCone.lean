import Langlands.Geometry.Building.AffineChamberWallComparisonProof
import Langlands.Geometry.Building.AffineWeylFacetFixing

/-!
# A chamber is cut out by its simple affine roots

For an affine root system (rank zero allowed) and the chamber `facet Ψ c` of a regular point
`c`, the chamber is the set of points where all simple affine roots are positive (KP, remark
after Definition 1.3.19) and its closure the set where they are nonnegative. Points of the
closure lie in the same facet exactly when the same simple affine roots vanish at them.
A chamber has finitely many simple affine roots and simple reflections.
-/

noncomputable section

universe uV uA

open Filter Topology

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- The simple affine roots of `C` vanishing at `x`. -/
def simpleZeroRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) (x : A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ simpleAffineRoots Ψ C ∧ ψ x = 0}

theorem mem_simpleZeroRoots {C : Set A} {x : A} {ψ : A →ᵃ[ℝ] ℝ} :
    ψ ∈ simpleZeroRoots Ψ C x ↔ ψ ∈ simpleAffineRoots Ψ C ∧ ψ x = 0 :=
  Iff.rfl

/-- Simple affine roots of a chamber are positive on it. -/
theorem pos_of_mem_simpleAffineRoots {C : Set A} {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ C) {x : A} (hx : x ∈ C) : 0 < ψ x :=
  hψ.1.2 x hx

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)
include hΨ

/-- A reflection across a wall of the chamber of a regular point is the reflection of a
simple affine root, and its root is a multiple of that simple root. -/
theorem exists_simple_smul_of_mem_wallReflections {c : A} (hc : IsRegular Ψ c)
    {ψ₀ : A →ᵃ[ℝ] ℝ} {v₀ : V} (hv₀ : IsCoroot Ψ ψ₀ v₀)
    (hs : affineReflection ψ₀ hv₀.1 ∈ wallReflections Ψ c) :
    ∃ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), ∃ r : ℝ, ψ₀ = r • ψ := by
  obtain ⟨s, ⟨ψ, hψ, v, hv, hsψ⟩, hs_eq⟩ :=
    exists_chamberSimple_of_mem_wallReflections hΨ hc hs
  have heq : affineReflection ψ₀ hv₀.1 = affineReflection ψ hv.1 := by
    rw [← hsψ]
    exact hs_eq.symm
  exact ⟨ψ, hψ, ψ₀.linear v / 2, eq_smul_of_hyperplane_le hv.1
    (hyperplane_le_of_affineReflection_eq hv.1 hv₀.1 heq)⟩

/-- A regular point on the positive side of every simple wall of the chamber of `c`
lies in that chamber. -/
theorem facetRel_of_simple_pos_of_isRegular {c y : A} (hc : IsRegular Ψ c)
    (hy : IsRegular Ψ y) (hpos : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 < ψ y) :
    facetRel Ψ c y := by
  by_cases hne : (separatingRoots Ψ c y).Nonempty
  · exfalso
    obtain ⟨ψ₀, hψ₀, v₀, hv₀, hwall, hsep⟩ :=
      exists_wall hΨ.isLocallyFiniteReflectionArrangement hc hy hne
    obtain ⟨ψ, hψ, r, rfl⟩ := exists_simple_smul_of_mem_wallReflections hΨ hc hv₀ hwall
    have h1 := pos_of_mem_simpleAffineRoots hψ (mem_facet_self Ψ c)
    have h2 := hpos ψ hψ
    simp only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] at hsep
    nlinarith [sq_nonneg r, mul_pos h1 h2]
  · intro η hη
    exact sign_eq_of_not_mul_neg (hc η hη) (hy η hη) fun h => hne ⟨η, hη, h⟩

/-- Points near `y` on the segment towards `c` keep every nonzero root sign of `y`. -/
theorem exists_segment_point {c y : A} :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ η ∈ Ψ, η y ≠ 0 →
      SignType.sign (η (ε • (c -ᵥ y) +ᵥ y)) = SignType.sign (η y) := by
  have h₁ := eventually_sign_smul_vadd hΨ.isLocallyFiniteReflectionArrangement y (c -ᵥ y)
  have h₂ : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := eventually_lt_nhds zero_lt_one
  obtain ⟨ε, hε, hlt, hsign⟩ := exists_pos_of_eventually (h₂.and h₁)
  exact ⟨ε, hε, hlt, hsign⟩

omit hΨ in
/-- The value of an affine functional on the segment point `ε • (c -ᵥ y) +ᵥ y`. -/
theorem apply_segment_point (η : A →ᵃ[ℝ] ℝ) (ε : ℝ) (c y : A) :
    η (ε • (c -ᵥ y) +ᵥ y) = ε * η c + (1 - ε) * η y := by
  rw [GalleryGeometry.apply_smul_vadd, AffineMap.linearMap_vsub, vsub_eq_sub]
  ring

/-- A point on the positive side of every simple wall lies in the closure of the
chamber. -/
theorem mem_facetClosure_of_simple_pos {c y : A} (hc : IsRegular Ψ c)
    (hpos : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 < ψ y) :
    y ∈ facetClosure Ψ c := by
  obtain ⟨ε, hε, hε1, hsign⟩ := exists_segment_point hΨ (c := c) (y := y)
  set z := ε • (c -ᵥ y) +ᵥ y with hz
  have hzreg : IsRegular Ψ z := by
    intro η hη hηz
    by_cases hηy : η y = 0
    · rw [hz, apply_segment_point, hηy, mul_zero, add_zero] at hηz
      exact hc η hη ((mul_eq_zero.mp hηz).resolve_left hε.ne')
    · have := hsign η hη hηy
      rw [hηz, sign_zero] at this
      exact hηy (sign_eq_zero_iff.mp this.symm)
  have hzpos : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 < ψ z := by
    intro ψ hψ
    rw [hz, apply_segment_point]
    have h1 := pos_of_mem_simpleAffineRoots hψ (mem_facet_self Ψ c)
    have h2 := hpos ψ hψ
    nlinarith
  have hcz := facetRel_of_simple_pos_of_isRegular hΨ hc hzreg hzpos
  intro η hη
  by_cases hηy : η y = 0
  · exact Or.inl (by rw [hηy, sign_zero])
  · exact Or.inr ((hsign η hη hηy).symm.trans (hcz η hη).symm)

/-- A point on the positive side of every simple wall is regular. -/
theorem isRegular_of_simple_pos {c y : A} (hc : IsRegular Ψ c)
    (hpos : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 < ψ y) : IsRegular Ψ y := by
  intro η hη hηy
  have hcl := mem_facetClosure_of_simple_pos hΨ hc hpos
  obtain ⟨w, hw⟩ := hΨ.exists_isCoroot η hη
  have hr := affineReflection_mem_rootStabilizer hw
  have hry : affineReflection η hw.1 y = y := affineReflection_apply_of_mem η hw.1 hηy
  have hc' : IsRegular Ψ (affineReflection η hw.1 c) := hc.apply hr
  have hcl' : y ∈ facetClosure Ψ (affineReflection η hw.1 c) := by
    have := (mem_facetClosure_apply_iff hr y c).2 hcl
    rwa [hry] at this
  have hsep : η c * η (affineReflection η hw.1 c) < 0 := by
    rw [apply_affineReflection]
    have := hc η hη
    nlinarith [sq_pos_of_ne_zero this]
  obtain ⟨ψ₀, hψ₀, v₀, hv₀, hwall, hsep₀⟩ :=
    exists_wall hΨ.isLocallyFiniteReflectionArrangement hc hc' ⟨η, hη, hsep⟩
  have h0 : ψ₀ y = 0 := root_eq_zero_of_mem_closures hcl hcl' hψ₀ hsep₀
  obtain ⟨ψ, hψ, r, hr'⟩ := exists_simple_smul_of_mem_wallReflections hΨ hc hv₀ hwall
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hΨ.linear_ne_zero ψ₀ hψ₀
    rw [hr', zero_smul, AffineMap.zero_linear]
  rw [hr', AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] at h0
  exact (hpos ψ hψ).ne' ((mul_eq_zero.mp h0).resolve_left hr0)

/-- A chamber is the set of points on the positive side of all its simple walls
(KP, remark after Definition 1.3.19). -/
theorem facetRel_iff_simple_pos {c : A} (hc : IsRegular Ψ c) (y : A) :
    facetRel Ψ c y ↔ ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 < ψ y := by
  refine ⟨fun h ψ hψ => pos_of_mem_simpleAffineRoots hψ ((mem_facet).2 h), fun hpos => ?_⟩
  exact facetRel_of_simple_pos_of_isRegular hΨ hc (isRegular_of_simple_pos hΨ hc hpos) hpos

/-- The closure of a chamber is the set of points on the nonnegative side of all its
simple walls. -/
theorem mem_facetClosure_iff_simple_nonneg {c : A} (hc : IsRegular Ψ c) (y : A) :
    y ∈ facetClosure Ψ c ↔ ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 ≤ ψ y := by
  constructor
  · intro hy ψ hψ
    have h1 := pos_of_mem_simpleAffineRoots hψ (mem_facet_self Ψ c)
    rcases hy ψ hψ.1.1 with h | h
    · exact (sign_eq_zero_iff.mp h).ge
    · rw [sign_pos h1, sign_eq_one_iff] at h
      exact h.le
  · intro hnn
    obtain ⟨ε, hε, hε1, hsign⟩ := exists_segment_point hΨ (c := c) (y := y)
    have hzpos : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 < ψ (ε • (c -ᵥ y) +ᵥ y) := by
      intro ψ hψ
      rw [apply_segment_point]
      have h1 := pos_of_mem_simpleAffineRoots hψ (mem_facet_self Ψ c)
      have h2 := hnn ψ hψ
      nlinarith
    have hcz := (facetRel_iff_simple_pos hΨ hc _).2 hzpos
    intro η hη
    by_cases hηy : η y = 0
    · exact Or.inl (by rw [hηy, sign_zero])
    · exact Or.inr ((hsign η hη hηy).symm.trans (hcz η hη).symm)


/-- Two points of the closure of a chamber on which the same simple affine roots vanish:
a root vanishing at the first point vanishes at the second. -/
theorem apply_eq_zero_of_simple_zero_iff {c x y : A} (hc : IsRegular Ψ c)
    (hx : x ∈ facetClosure Ψ c) (hy : y ∈ facetClosure Ψ c)
    (hxy : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), ψ x = 0 ↔ ψ y = 0)
    {η : A →ᵃ[ℝ] ℝ} (hη : η ∈ Ψ) (hηx : η x = 0) : η y = 0 := by
  by_contra hηy
  obtain ⟨t, ht, hsign⟩ := exists_pos_of_eventually
    (eventually_sign_smul_vadd hΨ.isLocallyFiniteReflectionArrangement x (x -ᵥ y))
  have happ : ∀ ζ : A →ᵃ[ℝ] ℝ, ζ (t • (x -ᵥ y) +ᵥ x) = ζ x + t * (ζ x - ζ y) := by
    intro ζ
    rw [GalleryGeometry.apply_smul_vadd, AffineMap.linearMap_vsub, vsub_eq_sub]
  have hz : t • (x -ᵥ y) +ᵥ x ∈ facetClosure Ψ c := by
    refine (mem_facetClosure_iff_simple_nonneg hΨ hc _).2 fun ψ hψ => ?_
    by_cases hψx : ψ x = 0
    · rw [happ, hψx, (hxy ψ hψ).1 hψx]
      simp
    · have hpos : 0 < ψ x :=
        lt_of_le_of_ne ((mem_facetClosure_iff_simple_nonneg hΨ hc x).1 hx ψ hψ) (Ne.symm hψx)
      have h := hsign ψ hψ.1.1 hψx
      rw [sign_pos hpos, sign_eq_one_iff] at h
      exact h.le
  have hηz : η (t • (x -ᵥ y) +ᵥ x) = -(t * η y) := by
    rw [happ, hηx]
    ring
  have hyc : SignType.sign (η y) = SignType.sign (η c) :=
    (hy η hη).resolve_left (by rwa [sign_eq_zero_iff])
  rcases hz η hη with h | h
  · rw [sign_eq_zero_iff, hηz, neg_eq_zero] at h
    exact hηy ((mul_eq_zero.mp h).resolve_left ht.ne')
  · rw [← hyc, hηz] at h
    rcases lt_or_gt_of_ne hηy with hlt | hlt
    · have hneg : 0 < -(t * η y) := by nlinarith
      rw [sign_pos hneg, sign_neg hlt] at h
      exact absurd h (by decide)
    · have hneg : -(t * η y) < 0 := by nlinarith
      rw [sign_neg hneg, sign_pos hlt] at h
      exact absurd h (by decide)

/-- Points of the closure of a chamber lie in the same facet exactly when the same simple
affine roots vanish at them. -/
theorem facetRel_iff_simple_zero_iff {c x y : A} (hc : IsRegular Ψ c)
    (hx : x ∈ facetClosure Ψ c) (hy : y ∈ facetClosure Ψ c) :
    facetRel Ψ x y ↔ ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), ψ x = 0 ↔ ψ y = 0 := by
  constructor
  · intro h ψ hψ
    have := h ψ hψ.1.1
    rw [← sign_eq_zero_iff, ← sign_eq_zero_iff (a := ψ y), this]
  · intro hxy η hη
    by_cases hηx : η x = 0
    · rw [hηx, apply_eq_zero_of_simple_zero_iff hΨ hc hx hy hxy hη hηx]
    · have hηy : η y ≠ 0 := fun h0 => hηx (apply_eq_zero_of_simple_zero_iff hΨ hc hy hx
        (fun ψ hψ => (hxy ψ hψ).symm) hη h0)
      rw [(hx η hη).resolve_left (by rwa [sign_eq_zero_iff]),
        (hy η hη).resolve_left (by rwa [sign_eq_zero_iff])]

/-- Points of the closure of a chamber lie in the same facet exactly when the same simple
affine roots vanish at them, stated with `simpleZeroRoots`. -/
theorem facetRel_iff_simpleZeroRoots_eq {c x y : A} (hc : IsRegular Ψ c)
    (hx : x ∈ facetClosure Ψ c) (hy : y ∈ facetClosure Ψ c) :
    facetRel Ψ x y ↔ simpleZeroRoots Ψ (facet Ψ c) x = simpleZeroRoots Ψ (facet Ψ c) y := by
  rw [facetRel_iff_simple_zero_iff hΨ hc hx hy]
  constructor
  · intro h
    ext ψ
    exact and_congr_right fun hψ => h ψ hψ
  · intro h ψ hψ
    have := congrArg (ψ ∈ ·) h
    simpa only [mem_simpleZeroRoots, hψ, true_and, eq_iff_iff] using this

omit hΨ in
/-- The wall of a simple affine root meets the closure of the chamber. -/
theorem exists_mem_facetClosure_apply_eq_zero {c : A} {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    ∃ p ∈ facetClosure Ψ c, ψ p = 0 := by
  obtain ⟨-, -, Fa, ⟨⟨y, rfl⟩, x, hx, hsub⟩, hspan⟩ := hψ.2.2
  refine ⟨y, ?_, ?_⟩
  · rw [← facetClosure_eq_of_facetRel (facet_eq_facet_iff.1 hx)]
    exact hsub (mem_facet_self Ψ y)
  · have hy : y ∈ affineSpan ℝ (facet Ψ y) := subset_affineSpan ℝ _ (mem_facet_self Ψ y)
    rw [hspan] at hy
    exact mem_hyperplane.1 hy

/-- Two simple affine roots of a chamber with the same derivative are equal. -/
theorem eq_of_mem_simpleAffineRoots_of_linear_eq {c : A} (hc : IsRegular Ψ c)
    {ψ η : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c))
    (hη : η ∈ simpleAffineRoots Ψ (facet Ψ c)) (hlin : ψ.linear = η.linear) : ψ = η := by
  have key : ∀ x y : A, ψ x - ψ y = η x - η y := by
    intro x y
    have h1 := ψ.linearMap_vsub x y
    have h2 := η.linearMap_vsub x y
    rw [hlin] at h1
    rw [vsub_eq_sub] at h1 h2
    linarith
  obtain ⟨p, hp, hψp⟩ := exists_mem_facetClosure_apply_eq_zero hψ
  obtain ⟨q, hq, hηq⟩ := exists_mem_facetClosure_apply_eq_zero hη
  have hηp := (mem_facetClosure_iff_simple_nonneg hΨ hc p).1 hp η hη
  have hψq := (mem_facetClosure_iff_simple_nonneg hΨ hc q).1 hq ψ hψ
  have hpq := key p q
  ext x
  have := key x q
  linarith

/-- A chamber has only finitely many simple affine roots. -/
theorem finite_simpleAffineRoots {c : A} (hc : IsRegular Ψ c) :
    (simpleAffineRoots Ψ (facet Ψ c)).Finite := by
  refine Set.Finite.of_finite_image (f := fun ψ : A →ᵃ[ℝ] ℝ => ψ.linear)
    (hΨ.finite_derivativeRoots.subset ?_) ?_
  · rintro _ ⟨ψ, hψ, rfl⟩
    exact linear_mem_derivativeRoots hψ.1.1
  · intro ψ hψ η hη hlin
    exact eq_of_mem_simpleAffineRoots_of_linear_eq hΨ hc hψ hη hlin

/-- A chamber has only finitely many simple reflections. -/
theorem finite_chamberSimpleReflections {c : A} (hc : IsRegular Ψ c) :
    (chamberSimpleReflections Ψ (facet Ψ c)).Finite := by
  refine ((finite_simpleAffineRoots hΨ hc).biUnion fun ψ _ =>
    (?_ : Set.Subsingleton {s : affineWeylGroup Ψ | ∃ (v : V) (hv : IsCoroot Ψ ψ v),
      (s : A ≃ᵃ[ℝ] A) = affineReflection ψ hv.1}).finite).subset ?_
  · rintro s ⟨v, hv, hs⟩ t ⟨w, hw, ht⟩
    have hvw := isCoroot_unique hΨ.isLocallyFiniteReflectionArrangement hv hw
    subst hvw
    exact Subtype.ext (hs.trans ht.symm)
  · rintro s ⟨ψ, hψ, v, hv, hs⟩
    exact Set.mem_biUnion hψ ⟨v, hv, hs⟩

end Langlands.Geometry.Building.AffineRootSystem
