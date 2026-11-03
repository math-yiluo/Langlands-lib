import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearAction
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines
import Langlands.GroupScheme.FlagCoreLimit

/-! # Homogeneous coordinates of rational points and closed sets of projective space -/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- A point `x` of projective space has homogeneous coordinates `c` when a homogeneous
polynomial lies in its homogeneous prime exactly when it vanishes at `c`. -/
def HasCoordinates (x : ProjectiveSpace K n) (c : Fin (n + 1) → K) : Prop :=
  ∀ (d : ℕ) (h : ProjectiveCoordinateRing K n), h.IsHomogeneous d →
    (h ∈ x.asHomogeneousIdeal ↔ eval c h = 0)

/-- The graded decomposition of the coordinate ring is by homogeneous components. -/
theorem decompose_coe_eq_homogeneousComponent (h : ProjectiveCoordinateRing K n) (d : ℕ) :
    (DirectSum.decompose (projectiveSpaceGrading K n) h d : ProjectiveCoordinateRing K n) =
      homogeneousComponent d h :=
  MvPolynomial.decomposition.decompose'_apply h d

/-- Membership in a homogeneous prime is membership of every homogeneous component. -/
theorem mem_asHomogeneousIdeal_iff_homogeneousComponent (x : ProjectiveSpace K n)
    (h : ProjectiveCoordinateRing K n) :
    h ∈ x.asHomogeneousIdeal ↔ ∀ d, homogeneousComponent d h ∈ x.asHomogeneousIdeal := by
  have hI := x.asHomogeneousIdeal.isHomogeneous
  change h ∈ x.asHomogeneousIdeal.toIdeal ↔
    ∀ d, homogeneousComponent d h ∈ x.asHomogeneousIdeal.toIdeal
  rw [Ideal.IsHomogeneous.mem_iff _ hI]
  refine forall_congr' fun d => ?_
  rw [decompose_coe_eq_homogeneousComponent]

/-- Homogeneous coordinates may be rescaled by any nonzero scalar. -/
theorem HasCoordinates.smul {x : ProjectiveSpace K n} {c : Fin (n + 1) → K}
    (hx : HasCoordinates x c) {a : K} (ha : a ≠ 0) : HasCoordinates x (a • c) := by
  intro d h hh
  rw [hx d h hh, GroupScheme.FlagCore.eval_smul_of_isHomogeneous hh, mul_eq_zero]
  simp [ha]

/-- Homogeneous coordinates are nonzero. -/
theorem HasCoordinates.ne_zero {x : ProjectiveSpace K n} {c : Fin (n + 1) → K}
    (hx : HasCoordinates x c) : c ≠ 0 := by
  rintro rfl
  apply x.not_irrelevant_le
  intro f hf
  have hf' := (HomogeneousIdeal.mem_irrelevant_iff _ f).mp hf
  refine (mem_asHomogeneousIdeal_iff_homogeneousComponent x f).mpr fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [homogeneousComponent_zero]
    have h0 : f.coeff 0 = 0 := by
      have e : (DirectSum.decompose (projectiveSpaceGrading K n) f 0 :
          ProjectiveCoordinateRing K n) = 0 := hf'
      rw [decompose_coe_eq_homogeneousComponent, homogeneousComponent_zero, C_eq_zero] at e
      exact e
    rw [h0, map_zero]
    exact zero_mem _
  · refine (hx d _ (homogeneousComponent_isHomogeneous d f)).mpr ?_
    rw [eval_eq']
    refine Finset.sum_eq_zero fun m hm => ?_
    have hdeg : ∑ i, m i = d := by
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact homogeneousComponent_isHomogeneous d f (mem_support_iff.mp hm)
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      simp [hcon] at hdeg
      omega
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [zero_pow hi]), mul_zero]

/-- A linear action moves homogeneous coordinates by the same linear map. -/
theorem HasCoordinates.linearAction {x : ProjectiveSpace K n} {c : Fin (n + 1) → K}
    (hx : HasCoordinates x c) (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    HasCoordinates (ProjectiveSpace.linearAction K n e x) (e c) := by
  intro d h hh
  rw [linearAction_mem_iff]
  have hsub : (linearSubstitution K n e.toLinearMap h).IsHomogeneous d := by
    have := (gradedLinearSubstitution K n e.toLinearMap).map_mem
      ((mem_homogeneousSubmodule d h).mpr hh)
    exact (mem_homogeneousSubmodule d _).mp this
  rw [hx d _ hsub]
  have heval : eval c (linearSubstitution K n e.toLinearMap h) = eval (e c) h := by
    change aeval c (linearSubstitution K n e.toLinearMap h) = aeval (e c) h
    rw [linearSubstitution, ← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext i
    rw [aeval_eq_eval, eval_linearFormPolynomialEquiv]
    rfl
  rw [heval]

/-- Homogeneous elements of positive degree are in the prime of a point exactly when the
point avoids their basic open. -/
theorem mem_asHomogeneousIdeal_iff_not_mem_basicOpen (x : ProjectiveSpace K n)
    (h : ProjectiveCoordinateRing K n) :
    h ∈ x.asHomogeneousIdeal ↔
      x ∉ Proj.basicOpen (projectiveSpaceGrading K n) h := by
  change _ ↔ ¬ (h ∉ x.asHomogeneousIdeal)
  exact not_not.symm

/-- If some coordinate of `c` is nonzero, evaluation at `c` maps the irrelevant ideal onto the
unit ideal of the global sections of the spectrum of the field. -/
theorem irrelevant_map_eval_eq_top (ψ : K →+* Γ(Spec (CommRingCat.of K), ⊤))
    {c : Fin (n + 1) → K} (hc : c ≠ 0) :
    (HomogeneousIdeal.irrelevant (projectiveSpaceGrading K n)).toIdeal.map
      (ψ.comp (eval c)) = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (funext hcon)
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem
      (projectiveSpaceGrading K n) Nat.one_pos (projectiveSpace_X_mem K n i)))
  simpa using (IsUnit.mk0 _ hi).map ψ

/-- The rational point defined by evaluation of the homogeneous coordinate ring at a nonzero
vector `c` has homogeneous coordinates `c`. -/
theorem hasCoordinates_fromOfGlobalSections (ψ : K →+* Γ(Spec (CommRingCat.of K), ⊤))
    (c : Fin (n + 1) → K)
    (hf : (HomogeneousIdeal.irrelevant (projectiveSpaceGrading K n)).toIdeal.map
      (ψ.comp (eval c)) = ⊤) :
    HasCoordinates
      ((Proj.fromOfGlobalSections (projectiveSpaceGrading K n) (ψ.comp (eval c)) hf :
        Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n) (IsLocalRing.closedPoint K)) c := by
  set p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n :=
    Proj.fromOfGlobalSections (projectiveSpaceGrading K n) (ψ.comp (eval c)) hf with hp
  intro d h hh
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hC : h = C (h.coeff 0) := by
      rw [← homogeneousComponent_zero, homogeneousComponent_of_mem
        ((mem_homogeneousSubmodule 0 h).mpr hh)]
      simp
    rw [hC, eval_C]
    constructor
    · intro hmem
      by_contra hne
      exact (p (IsLocalRing.closedPoint K)).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ hmem ((IsUnit.mk0 _ hne).map C))
    · intro h0
      rw [h0, map_zero]
      exact zero_mem _
  · refine (mem_asHomogeneousIdeal_iff_not_mem_basicOpen _ h).trans ?_
    have hpre := Proj.fromOfGlobalSections_preimage_basicOpen
      (projectiveSpaceGrading K n) (ψ.comp (eval c)) hf hd
      ((mem_homogeneousSubmodule d h).mpr hh)
    have hmem : p (IsLocalRing.closedPoint K) ∈ Proj.basicOpen (projectiveSpaceGrading K n) h ↔
        IsLocalRing.closedPoint K ∈
          (Spec (CommRingCat.of K)).basicOpen ((ψ.comp (eval c)) h) := by
      rw [← hpre]
      rfl
    have key : IsLocalRing.closedPoint K ∈
        (Spec (CommRingCat.of K)).basicOpen ((ψ.comp (eval c)) h) ↔ eval c h ≠ 0 := by
      by_cases h0 : eval c h = 0
      · simp only [RingHom.comp_apply, h0, map_zero, Scheme.basicOpen_zero, ne_eq,
          not_true_eq_false, iff_false]
        exact fun h => h
      · rw [RingHom.comp_apply, Scheme.basicOpen_of_isUnit _ ((IsUnit.mk0 _ h0).map ψ)]
        exact iff_of_true trivial h0
    exact (not_congr (hmem.trans key)).trans not_not

/-- Two systems of homogeneous coordinates of one point are proportional. -/
theorem HasCoordinates.exists_eq_smul {x : ProjectiveSpace K n} {c c' : Fin (n + 1) → K}
    (hx : HasCoordinates x c) (hx' : HasCoordinates x c') :
    ∃ a : K, a ≠ 0 ∧ c' = a • c := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx.ne_zero (funext hcon)
  have hlin : ∀ l, c i * c' l = c l * c' i := by
    intro l
    let L : ProjectiveCoordinateRing K n := C (c i) * X l - C (c l) * X i
    have hL : L.IsHomogeneous 1 :=
      ((isHomogeneous_X K l).C_mul (c i)).sub ((isHomogeneous_X K i).C_mul (c l))
    have h1 : eval c L = 0 := by
      simp only [L, map_sub, map_mul, eval_C, eval_X]
      ring
    have h2 := (hx' 1 L hL).mp ((hx 1 L hL).mpr h1)
    simp only [L, map_sub, map_mul, eval_C, eval_X] at h2
    linear_combination h2
  refine ⟨c' i / c i, ?_, ?_⟩
  · intro h0
    apply hx'.ne_zero
    funext l
    have := hlin l
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rw [h0, mul_zero] at this
      simpa [hi] using this
    · exact absurd h0 hi
  · funext l
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (hlin l)

/-- **Closed sets on rational points.** Let `Z` be a closed set of projective space and `S` a set
of vectors each of which is a system of homogeneous coordinates of a point of `Z`. If every
homogeneous polynomial vanishing on `S` vanishes at `c`, then every point with homogeneous
coordinates `c` lies in `Z`. -/
theorem mem_of_isClosed {Z : Set (ProjectiveSpace K n)} (hZ : IsClosed Z)
    (S : Set (Fin (n + 1) → K)) (hS : ∀ s ∈ S, ∃ x ∈ Z, HasCoordinates x s)
    {c : Fin (n + 1) → K}
    (hc : ∀ (f : ProjectiveCoordinateRing K n) (d : ℕ), f.IsHomogeneous d →
      (∀ s ∈ S, eval s f = 0) → eval c f = 0)
    {y : ProjectiveSpace K n} (hy : HasCoordinates y c) : y ∈ Z := by
  have hZ' : IsClosed (X := ProjectiveSpectrum (projectiveSpaceGrading K n)) Z := hZ
  have hcl : ProjectiveSpectrum.zeroLocus (projectiveSpaceGrading K n)
      (ProjectiveSpectrum.vanishingIdeal (𝒜 := projectiveSpaceGrading K n) Z) = Z :=
    (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).trans hZ'.closure_eq
  have hy' : y ∈ ProjectiveSpectrum.zeroLocus (projectiveSpaceGrading K n)
      (ProjectiveSpectrum.vanishingIdeal (𝒜 := projectiveSpaceGrading K n) Z) := by
    refine (ProjectiveSpectrum.mem_zeroLocus _ _ _).mpr ?_
    intro h hmem
    refine (mem_asHomogeneousIdeal_iff_homogeneousComponent y h).mpr fun d => ?_
    refine (hy d _ (homogeneousComponent_isHomogeneous d h)).mpr ?_
    refine hc _ d (homogeneousComponent_isHomogeneous d h) fun s hs => ?_
    obtain ⟨x, hxZ, hx⟩ := hS s hs
    refine (hx d _ (homogeneousComponent_isHomogeneous d h)).mp ?_
    exact (mem_asHomogeneousIdeal_iff_homogeneousComponent x h).mp
      ((ProjectiveSpectrum.mem_vanishingIdeal _ _).mp hmem x hxZ) d
  exact hcl ▸ hy'

end Langlands.AlgebraicGeometry.ProjectiveSpace
