import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts

/-! # Linear forms through a rational point of projective space -/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- Restriction of homogeneous coordinates to the line through `c`: `X j ↦ c j • t`. -/
def lineRestriction (c : Fin (m + 1) → K) : ProjectiveCoordinateRing K m →ₐ[K] Polynomial K :=
  aeval fun j => Polynomial.C (c j) * Polynomial.X

/-- Modulo the linear relations `X j = c j • X k`, every polynomial is congruent to its line
restriction evaluated at `X k`. -/
theorem sub_aeval_lineRestriction_mem (I : Ideal (ProjectiveCoordinateRing K m))
    (k : Fin (m + 1)) (c : Fin (m + 1) → K)
    (hI : ∀ j, (X j - C (c j) * X k : ProjectiveCoordinateRing K m) ∈ I)
    (h : ProjectiveCoordinateRing K m) :
    h - Polynomial.aeval (X k : ProjectiveCoordinateRing K m) (lineRestriction c h) ∈ I := by
  have key : (Ideal.Quotient.mkₐ K I).comp
      ((Polynomial.aeval (X k : ProjectiveCoordinateRing K m)).comp (lineRestriction c)) =
      Ideal.Quotient.mkₐ K I := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, lineRestriction, aeval_X, Polynomial.aeval_mul,
      Polynomial.aeval_C, Polynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, ← neg_sub, neg_mem_iff]
    simpa [MvPolynomial.algebraMap_eq] using hI j
  have := congrArg (fun φ => φ h) key
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  rw [← Ideal.Quotient.eq]
  exact this.symm

/-- In a homogeneous prime not containing `X k`, no nonzero polynomial in `X k` lies. -/
theorem eq_zero_of_aeval_X_mem (Q : HomogeneousIdeal (projectiveSpaceGrading K m))
    (hQ : Q.toIdeal.IsPrime) {k : Fin (m + 1)}
    (hk : (X k : ProjectiveCoordinateRing K m) ∉ Q) {p : Polynomial K}
    (hp : Polynomial.aeval (X k : ProjectiveCoordinateRing K m) p ∈ Q) : p = 0 := by
  by_contra hp0
  have hpow : ∀ i : ℕ, ((X k : ProjectiveCoordinateRing K m) ^ i) ∈
      MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K i :=
    fun i => (mem_homogeneousSubmodule i _).mpr (isHomogeneous_X_pow k i)
  have hcomp : homogeneousComponent p.natDegree
      (Polynomial.aeval (X k : ProjectiveCoordinateRing K m) p) =
      p.leadingCoeff • (X k : ProjectiveCoordinateRing K m) ^ p.natDegree := by
    rw [Polynomial.aeval_eq_sum_range, map_sum]
    simp_rw [map_smul]
    rw [Finset.sum_eq_single p.natDegree]
    · rw [homogeneousComponent_of_mem (hpow _)]
      simp
    · intro i _ hi
      rw [homogeneousComponent_of_mem (hpow _)]
      simp [Ne.symm hi]
    · intro h
      simp at h
  have hmem : homogeneousComponent p.natDegree
      (Polynomial.aeval (X k : ProjectiveCoordinateRing K m) p) ∈ Q := by
    have := (Ideal.IsHomogeneous.mem_iff _ Q.isHomogeneous).mp hp p.natDegree
    rwa [show (DirectSum.decompose (projectiveSpaceGrading K m)
        (Polynomial.aeval (X k : ProjectiveCoordinateRing K m) p) p.natDegree :
          ProjectiveCoordinateRing K m) =
        homogeneousComponent p.natDegree
          (Polynomial.aeval (X k : ProjectiveCoordinateRing K m) p) from
      MvPolynomial.decomposition.decompose'_apply _ _] at this
  rw [hcomp] at hmem
  have hX : (X k : ProjectiveCoordinateRing K m) ^ p.natDegree ∈ Q := by
    have := Q.toIdeal.mul_mem_left (C p.leadingCoeff⁻¹) hmem
    rwa [smul_eq_C_mul, ← mul_assoc, ← C_mul,
      inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp0), C_1, one_mul] at this
  exact hk (hQ.mem_of_pow_mem _ hX)

/-- A homogeneous prime containing the linear relations `X j = c j • X k` but not `X k` is the
kernel of restriction to the line through `c`. -/
theorem mem_iff_lineRestriction_eq_zero (Q : HomogeneousIdeal (projectiveSpaceGrading K m))
    (hQ : Q.toIdeal.IsPrime) {k : Fin (m + 1)} {c : Fin (m + 1) → K}
    (hk : (X k : ProjectiveCoordinateRing K m) ∉ Q)
    (hc : ∀ j, (X j - C (c j) * X k : ProjectiveCoordinateRing K m) ∈ Q)
    (h : ProjectiveCoordinateRing K m) :
    h ∈ Q ↔ lineRestriction c h = 0 := by
  have hsub := sub_aeval_lineRestriction_mem Q.toIdeal k c hc h
  constructor
  · intro hh
    refine eq_zero_of_aeval_X_mem Q hQ hk ?_
    simpa using Q.toIdeal.sub_mem hh hsub
  · intro h0
    rw [h0, map_zero, sub_zero] at hsub
    exact hsub

/-- The linear relation `X j - c j • X k` is a linear form. -/
theorem linearRelation_mem (k j : Fin (m + 1)) (a : K) :
    (X j - C a * X k : ProjectiveCoordinateRing K m) ∈ projectiveSpaceGrading K m 1 :=
  (mem_homogeneousSubmodule 1 _).mpr ((isHomogeneous_X K j).sub ((isHomogeneous_X K k).C_mul a))

/-- Let `P` have linear coordinates `c` relative to `X k`. A point `Q` whose homogeneous prime
contains every linear form in the homogeneous prime of `P` equals `P`. -/
theorem eq_of_forall_linear_mem {P Q : ProjectiveSpace K m} {k : Fin (m + 1)}
    {c : Fin (m + 1) → K}
    (hk : (X k : ProjectiveCoordinateRing K m) ∉ P.asHomogeneousIdeal)
    (hc : ∀ j, (X j - C (c j) * X k : ProjectiveCoordinateRing K m) ∈ P.asHomogeneousIdeal)
    (hPQ : ∀ f : projectiveSpaceGrading K m 1,
      (f : ProjectiveCoordinateRing K m) ∈ P.asHomogeneousIdeal →
        (f : ProjectiveCoordinateRing K m) ∈ Q.asHomogeneousIdeal) :
    Q = P := by
  have hcQ : ∀ j, (X j - C (c j) * X k : ProjectiveCoordinateRing K m) ∈ Q.asHomogeneousIdeal :=
    fun j => hPQ ⟨_, linearRelation_mem k j (c j)⟩ (hc j)
  have hkQ : (X k : ProjectiveCoordinateRing K m) ∉ Q.asHomogeneousIdeal := by
    intro hXk
    apply Q.not_irrelevant_le
    rw [← toIdeal_le_toIdeal_iff]
    refine (projectiveSpace_irrelevant_le_span_X K m).trans (Ideal.span_le.mpr ?_)
    rintro _ ⟨j, rfl⟩
    have := Q.asHomogeneousIdeal.toIdeal.add_mem (hcQ j)
      (Q.asHomogeneousIdeal.toIdeal.mul_mem_left (C (c j)) hXk)
    simpa using this
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  ext h
  change h ∈ Q.asHomogeneousIdeal ↔ h ∈ P.asHomogeneousIdeal
  rw [mem_iff_lineRestriction_eq_zero _ Q.isPrime hkQ hcQ,
    mem_iff_lineRestriction_eq_zero _ P.isPrime hk hc]

/-- The point of a section of projective space over a field has linear coordinates relative to
some coordinate variable. -/
theorem exists_linearCoordinates_of_section
    (σ : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K m)
    (hσ : σ ≫ projectiveSpaceToSpec K m = 𝟙 _) :
    ∃ (k : Fin (m + 1)) (c : Fin (m + 1) → K),
      (X k : ProjectiveCoordinateRing K m) ∉ (σ (IsLocalRing.closedPoint K)).asHomogeneousIdeal ∧
      ∀ j, (X j - C (c j) * X k : ProjectiveCoordinateRing K m) ∈
        (σ (IsLocalRing.closedPoint K)).asHomogeneousIdeal := by
  have hcov : σ (IsLocalRing.closedPoint K) ∈ ⨆ j, projectiveSpaceCoordinateOpen K m j := by
    rw [iSup_projectiveSpaceCoordinateOpen]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  obtain ⟨ι, hι⟩ : ∃ ι : Spec (CommRingCat.of
      (HomogeneousLocalization.Away (projectiveSpaceGrading K m) (X k))) ⟶ ProjectiveSpace K m,
      ι = Proj.awayι (projectiveSpaceGrading K m) (X k) (projectiveSpace_X_mem K m k)
        Nat.one_pos := ⟨_, rfl⟩
  have : IsOpenImmersion ι := by
    subst hι
    exact isOpenImmersion_affineOpenCover_f K m k
  have hopens : ι.opensRange = projectiveSpaceCoordinateOpen K m k := by
    subst hι
    exact affineOpenCover_opensRange K m k
  have htoSpec : ι ≫ projectiveSpaceToSpec K m = Spec.map (CommRingCat.ofHom (algebraMap K
      (HomogeneousLocalization.Away (projectiveSpaceGrading K m) (X k)))) := by
    subst hι
    exact affineOpenCover_comp_toSpec K m k
  have hpreimage : ∀ (g : ProjectiveCoordinateRing K m) (hg : g ∈ projectiveSpaceGrading K m 1),
      ι ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading K m) g = PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem (projectiveSpace_X_mem K m k) hg) := by
    intro g hg
    subst hι
    exact Proj.awayι_preimage_basicOpen (projectiveSpaceGrading K m)
      (projectiveSpace_X_mem K m k) Nat.one_pos hg Nat.one_pos
  have hrange : Set.range σ ⊆ Set.range ι := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint K), ← Scheme.Hom.coe_opensRange, hopens]
    exact hk
  have hfac : IsOpenImmersion.lift ι σ hrange ≫ ι = σ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift ι σ hrange)
  have hψalg : ∀ a : K, ψ.hom (algebraMap K
      (HomogeneousLocalization.Away (projectiveSpaceGrading K m) (X k)) a) = a := by
    have h1 : Spec.map ψ ≫ ι ≫ projectiveSpaceToSpec K m = 𝟙 _ := by
      rw [hψ, ← Category.assoc, hfac, hσ]
    rw [htoSpec, ← Spec.map_comp, Spec.map_eq_id] at h1
    intro a
    exact congrArg (fun φ => φ.hom a) h1
  let r : Fin (m + 1) → HomogeneousLocalization.Away (projectiveSpaceGrading K m) (X k) :=
    fun j => HomogeneousLocalization.Away.mk (projectiveSpaceGrading K m)
      (projectiveSpace_X_mem K m k) 1 (X j) (by simpa using projectiveSpace_X_mem K m j)
  refine ⟨k, fun j => ψ.hom (r j), hk, fun j => ?_⟩
  by_contra hj
  have hg := linearRelation_mem k j (ψ.hom (r j))
  have hmem : σ (IsLocalRing.closedPoint K) ∈ Proj.basicOpen (projectiveSpaceGrading K m)
      (X j - C (ψ.hom (r j)) * X k) := hj
  rw [← hfac, ← hψ] at hmem
  have hpre : (Spec.map ψ) (IsLocalRing.closedPoint K) ∈
      ι ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading K m) (X j - C (ψ.hom (r j)) * X k) := hmem
  rw [hpreimage _ hg] at hpre
  apply hpre
  change ψ.hom _ ∈ (IsLocalRing.closedPoint K).asIdeal
  have hv : ∀ a : K, (algebraMap K
      (HomogeneousLocalization.Away (projectiveSpaceGrading K m) (X k)) a).val =
      algebraMap (ProjectiveCoordinateRing K m)
        (Localization.Away (X k : ProjectiveCoordinateRing K m)) (C a) := fun _ => rfl
  have helem : HomogeneousLocalization.Away.isLocalizationElem (projectiveSpace_X_mem K m k) hg =
      r j - algebraMap K _ (ψ.hom (r j)) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_sub, HomogeneousLocalization.Away.val_mk,
      HomogeneousLocalization.Away.val_mk, hv, ← Localization.mk_one_eq_algebraMap,
      Localization.sub_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp; ring⟩
  rw [helem, map_sub, hψalg, sub_self]
  exact Ideal.zero_mem _

end Langlands.AlgebraicGeometry.ProjectiveSpace
