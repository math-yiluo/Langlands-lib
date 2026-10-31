import Langlands.AlgebraicGeometry.LinearSystem.ChartMap
import Langlands.AlgebraicGeometry.LinearSystem.SectionRatio
import Langlands.AlgebraicGeometry.ProjectiveSpace

/-! # The morphism to projective space defined by base-point-free sections

Let `X` be a scheme over a field `K`, `L` a line bundle on `X` and `s 0, …, s n` global
sections of `L` with no common zero. On the nonvanishing locus `U_j` of `s j`, the ratios
`s i / s j` define a morphism `U_j ⟶ D₊(X_j)` into projective space. These morphisms agree
on overlaps and glue to `linearSystemMap : X ⟶ ProjectiveSpace K n`. For a `T`-point `g`
of `X` landing in `U_j`, `g ≫ linearSystemMap` is the chart map given by the pulled-back
ratios. Hence two `T`-points in `U_j` over the same `T`-point of `Spec K` have the same
image exactly when their ratios agree.
-/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.LinearSystem

/-- Scaling all variables by `c` scales a homogeneous polynomial of degree `m` by `c ^ m`. -/
lemma eval₂_mul_of_isHomogeneous {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : ι → S) (c : S) {φ : MvPolynomial ι R} {m : ℕ}
    (hφ : φ.IsHomogeneous m) :
    MvPolynomial.eval₂ f (fun i ↦ c * x i) φ = c ^ m * MvPolynomial.eval₂ f x φ := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hφ.degree_eq_sum_deg_support hd]
  ring

variable {K : Type u} [Field K] {X T T' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
  {L : LineBundle X} {n : ℕ} (s : Fin (n + 1) → GlobalSections L.obj)

section scalars

/-- The global scalars of a composite. -/
lemma scalarsFromBase_comp {R : CommRingCat.{u}} (g : T ⟶ X) (q : X ⟶ Spec R) :
    Scheme.Modules.scalarsFromBase (g ≫ q) =
      g.appTop.hom.comp (Scheme.Modules.scalarsFromBase q) := by
  simp only [Scheme.Modules.scalarsFromBase, Scheme.Hom.comp_appTop]
  rfl

/-- A morphism to `Spec R` is recovered from its global scalars. -/
lemma toSpecΓ_SpecMap_scalarsFromBase {R : CommRingCat.{u}} (q : T ⟶ Spec R) :
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Scheme.Modules.scalarsFromBase q)) = q := by
  rw [Scheme.Modules.scalarsFromBase, CommRingCat.ofHom_hom, Spec.map_comp,
    ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Every global function on `Spec K` is a scalar of a rational point. -/
lemma exists_scalarsFromBase_eq {x : Spec (CommRingCat.of K) ⟶ X} (hx : x ≫ p = 𝟙 _)
    (r : Γ(Spec (CommRingCat.of K), ⊤)) :
    ∃ α : K, Scheme.Modules.scalarsFromBase (x ≫ p) α = r := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom r, ?_⟩
  rw [hx, Scheme.Modules.scalarsFromBase, Scheme.Hom.id_appTop, Category.comp_id]
  exact Iso.hom_inv_id_apply _ r

end scalars

/-- The `K`-linear combination `∑ i, c i • s i` of the sections. -/
def linComb (c : Fin (n + 1) → K) : GlobalSections L.obj :=
  ∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i

/-- Ratios of a linear combination are the linear combinations of the ratios. -/
lemma sectionRatio_linComb {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) (c : Fin (n + 1) → K) :
    sectionRatio L g (linComb p s c) s₀ =
      ∑ i, Scheme.Modules.scalarsFromBase (g ≫ p) (c i) * sectionRatio L g (s i) s₀ := by
  rw [linComb, sectionRatio_sum hg]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sectionRatio_smul_left hg, scalarsFromBase_comp]
  rfl

/-- The coefficient vector of `s i - α • s j`. -/
def basisDiff (i j : Fin (n + 1)) (α : K) : Fin (n + 1) → K :=
  Pi.single i 1 - Pi.single j α

lemma sum_scalarsFromBase_single (q : T ⟶ Spec (CommRingCat.of K)) (r : Fin (n + 1) → Γ(T, ⊤))
    (i : Fin (n + 1)) (a : K) :
    ∑ k, Scheme.Modules.scalarsFromBase q ((Pi.single i a : Fin (n + 1) → K) k) * r k =
      Scheme.Modules.scalarsFromBase q a * r i := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma sectionRatio_linComb_basisDiff {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) (i j : Fin (n + 1)) (α : K) :
    sectionRatio L g (linComb p s (basisDiff i j α)) s₀ =
      sectionRatio L g (s i) s₀ -
        Scheme.Modules.scalarsFromBase (g ≫ p) α * sectionRatio L g (s j) s₀ := by
  rw [sectionRatio_linComb p s hg]
  simp only [basisDiff, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib,
    sum_scalarsFromBase_single, map_one, one_mul]

/-- `s i - α • s j` vanishes along a point of `U_j` exactly when the ratio `s i / s j`
there is `α`. -/
lemma vanishesAlong_linComb_basisDiff_iff {g : T ⟶ X} {j : Fin (n + 1)}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) (i : Fin (n + 1)) (α : K) :
    VanishesAlong L g (linComb p s (basisDiff i j α)) ↔
      sectionRatio L g (s i) (s j) = Scheme.Modules.scalarsFromBase (g ≫ p) α := by
  rw [vanishesAlong_iff_sectionRatio_eq_zero hg, sectionRatio_linComb_basisDiff p s hg,
    sectionRatio_self hg, mul_one, sub_eq_zero]

section pointMap

/-- The ring map `X_i ↦ s_i / s_j` from the homogeneous coordinate ring, for a `T`-point
`g` of `X`. -/
def chartRingHom (g : T ⟶ X) (j : Fin (n + 1)) : ProjectiveCoordinateRing K n →+* Γ(T, ⊤) :=
  MvPolynomial.eval₂Hom (Scheme.Modules.scalarsFromBase (g ≫ p))
    (fun i ↦ sectionRatio L g (s i) (s j))

@[simp]
lemma chartRingHom_X (g : T ⟶ X) (j i : Fin (n + 1)) :
    chartRingHom p s g j (MvPolynomial.X i) = sectionRatio L g (s i) (s j) :=
  MvPolynomial.eval₂Hom_X' _ _ _

@[simp]
lemma chartRingHom_C (g : T ⟶ X) (j : Fin (n + 1)) (k : K) :
    chartRingHom p s g j (MvPolynomial.C k) = Scheme.Modules.scalarsFromBase (g ≫ p) k :=
  MvPolynomial.eval₂Hom_C _ _ _

lemma isUnit_chartRingHom_X {g : T ⟶ X} {j : Fin (n + 1)}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) :
    IsUnit (chartRingHom p s g j (MvPolynomial.X j)) := by
  rw [chartRingHom_X, sectionRatio_self hg]
  exact isUnit_one

lemma sectionRatio_linComb_eq_chartRingHom {g : T ⟶ X} {j : Fin (n + 1)}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) (c : Fin (n + 1) → K) :
    sectionRatio L g (linComb p s c) (s j) =
      chartRingHom p s g j (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) := by
  rw [sectionRatio_linComb p s hg, map_sum]
  simp only [map_mul, chartRingHom_C, chartRingHom_X]

/-- The morphism `T ⟶ ℙⁿ` through the chart `D₊(X_j)` given by the pulled-back ratios
`s_i / s_j`, for a `T`-point `g` landing in the nonvanishing locus of `s j`. -/
def pointMap (g : T ⟶ X) (j : Fin (n + 1)) (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) :
    T ⟶ ProjectiveSpace K n :=
  chartMap (projectiveSpaceGrading K n) (chartRingHom p s g j) (projectiveSpace_X_mem K n j)
    one_pos (isUnit_chartRingHom_X p s hg)

lemma pointMap_congr {g g' : T ⟶ X} (h : g = g') {j : Fin (n + 1)}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) :
    pointMap p s g j hg = pointMap p s g' j (h ▸ hg) := by
  subst h
  rfl

lemma chartRingHom_scale {g : T ⟶ X} {j k : Fin (n + 1)}
    (hj : ∀ t, g t ∈ trivializationOpen L.obj (s j))
    (hk : ∀ t, g t ∈ trivializationOpen L.obj (s k)) (m : ℕ)
    (a : ProjectiveCoordinateRing K n) (ha : a ∈ projectiveSpaceGrading K n m) :
    chartRingHom p s g k a = sectionRatio L g (s j) (s k) ^ m * chartRingHom p s g j a := by
  have hx : (fun i ↦ sectionRatio L g (s i) (s k)) =
      fun i ↦ sectionRatio L g (s j) (s k) * sectionRatio L g (s i) (s j) := by
    funext i
    rw [mul_comm, sectionRatio_mul hk hj]
  rw [chartRingHom, chartRingHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, hx]
  exact eval₂_mul_of_isHomogeneous _ _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ha)

/-- The point map does not depend on the chart. -/
lemma pointMap_eq {g : T ⟶ X} {j k : Fin (n + 1)}
    (hj : ∀ t, g t ∈ trivializationOpen L.obj (s j))
    (hk : ∀ t, g t ∈ trivializationOpen L.obj (s k)) :
    pointMap p s g j hj = pointMap p s g k hk := by
  have hu : IsUnit (chartRingHom p s g j (MvPolynomial.X k)) := by
    rw [chartRingHom_X]
    exact isUnit_sectionRatio hj hk
  rw [pointMap, pointMap, chartMap_eq _ _ (projectiveSpace_X_mem K n j) one_pos
    (projectiveSpace_X_mem K n k) one_pos _ hu]
  exact (chartMap_eq_of_scale _ (chartRingHom p s g j) (chartRingHom p s g k)
    (projectiveSpace_X_mem K n k) one_pos hu (isUnit_chartRingHom_X p s hk) _
    (chartRingHom_scale p s hj hk)).symm

lemma comp_chartRingHom (h : T' ⟶ T) (g : T ⟶ X) (j : Fin (n + 1))
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) :
    h.appTop.hom.comp (chartRingHom p s g j) = chartRingHom p s (h ≫ g) j := by
  apply MvPolynomial.ringHom_ext
  · intro k
    rw [RingHom.comp_apply, chartRingHom_C, chartRingHom_C, Category.assoc,
      scalarsFromBase_comp h (g ≫ p)]
    rfl
  · intro i
    rw [RingHom.comp_apply, chartRingHom_X, chartRingHom_X, sectionRatio_comp hg]

/-- Point maps are natural in the source. -/
lemma comp_pointMap (h : T' ⟶ T) {g : T ⟶ X} {j : Fin (n + 1)}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) :
    h ≫ pointMap p s g j hg = pointMap p s (h ≫ g) j (fun t ↦ hg (h t)) := by
  rw [pointMap, pointMap, comp_chartMap]
  exact chartMap_ringHom_congr _ (comp_chartRingHom p s h g j hg) _ _ _

/-- Point maps lie over `Spec K`. -/
lemma pointMap_toSpec {g : T ⟶ X} {j : Fin (n + 1)}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) :
    pointMap p s g j hg ≫ projectiveSpaceToSpec K n = g ≫ p := by
  change chartMap (projectiveSpaceGrading K n) _ _ _ _ ≫
    Proj.toSpecZero (projectiveSpaceGrading K n) ≫
      Spec.map (CommRingCat.ofHom (projectiveSpaceConstants K n)) = g ≫ p
  rw [← Category.assoc, chartMap_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  conv_rhs => rw [← toSpecΓ_SpecMap_scalarsFromBase (g ≫ p)]
  congr 3
  ext k
  rw [RingHom.comp_apply, RingHom.comp_apply]
  erw [awayLift_fromZeroRingHom]
  exact chartRingHom_C p s g j k

/-- The preimage of a coordinate chart under a point map. -/
lemma pointMap_preimage {g : T ⟶ X} {j : Fin (n + 1)}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) (i : Fin (n + 1)) :
    pointMap p s g j hg ⁻¹ᵁ projectiveSpaceCoordinateOpen K n i =
      T.basicOpen (sectionRatio L g (s i) (s j)) := by
  rw [← chartRingHom_X p s g j i]
  exact chartMap_preimage_basicOpen _ _ _ one_pos (projectiveSpace_X_mem K n i) one_pos _

/-- Equal point maps over the same chart have equal ratios. -/
lemma chartRingHom_eq_of_pointMap_eq {g₁ g₂ : T ⟶ X} {j : Fin (n + 1)}
    (h₁ : ∀ t, g₁ t ∈ trivializationOpen L.obj (s j))
    (h₂ : ∀ t, g₂ t ∈ trivializationOpen L.obj (s j))
    (H : pointMap p s g₁ j h₁ = pointMap p s g₂ j h₂) :
    chartRingHom p s g₁ j = chartRingHom p s g₂ j := by
  have hA := awayLift_eq_of_chartMap_eq _ _ _ _ one_pos _ _ H
  have het : chartRingHom p s g₁ j (MvPolynomial.X j) = chartRingHom p s g₂ j (MvPolynomial.X j) := by
    rw [chartRingHom_X, chartRingHom_X, sectionRatio_self h₁, sectionRatio_self h₂]
  apply MvPolynomial.ringHom_ext
  · intro k
    exact eq_of_awayLift_eq _ _ _ (projectiveSpace_X_mem K n j) _ _ het hA 0 _
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (by simpa using MvPolynomial.isHomogeneous_C (Fin (n + 1)) k))
  · intro i
    exact eq_of_awayLift_eq _ _ _ (projectiveSpace_X_mem K n j) _ _ het hA 1 _
      (by simpa using projectiveSpace_X_mem K n i)

end pointMap

section glue

variable {s}

lemma exists_mem_trivializationOpen (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
    (x : X) : ∃ i, x ∈ trivializationOpen L.obj (s i) := by
  obtain ⟨i, hi⟩ := hs x
  refine ⟨i, ?_⟩
  rw [← SetLike.mem_coe, ← lineBundleResidueOpenComparison X L (s i)]
  exact hi

lemma isOpenCover_trivializationOpen (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    TopologicalSpace.IsOpenCover fun i ↦ trivializationOpen L.obj (s i) :=
  eq_top_iff.mpr fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr (exists_mem_trivializationOpen hs x)

lemma ι_mem (U : X.Opens) : ∀ t, U.ι t ∈ U := fun t ↦ by simp

variable (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))

/-- The morphism to projective space defined by base-point-free sections, glued from the
point maps of the inclusions of the nonvanishing loci. -/
def linearSystemMap : X ⟶ ProjectiveSpace K n :=
  (X.openCoverOfIsOpenCover _ (isOpenCover_trivializationOpen hs)).glueMorphisms
    (fun j ↦ pointMap p s (trivializationOpen L.obj (s j)).ι j (ι_mem _)) fun j k ↦ by
      rw [comp_pointMap, comp_pointMap]
      exact (pointMap_congr p s Limits.pullback.condition _).trans (pointMap_eq p s _ _)

lemma ι_linearSystemMap (j : Fin (n + 1)) :
    (trivializationOpen L.obj (s j)).ι ≫ linearSystemMap p hs =
      pointMap p s (trivializationOpen L.obj (s j)).ι j (ι_mem _) :=
  (X.openCoverOfIsOpenCover _ (isOpenCover_trivializationOpen hs)).ι_glueMorphisms _ _ j

/-- Along a point landing in `U_j`, the linear system map is the point map of the chart. -/
lemma comp_linearSystemMap (g : T ⟶ X) (j : Fin (n + 1))
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) :
    g ≫ linearSystemMap p hs = pointMap p s g j hg := by
  apply Scheme.hom_ext_of_forall
  intro t
  obtain ⟨k, hk⟩ := exists_mem_trivializationOpen hs (g t)
  refine ⟨g ⁻¹ᵁ trivializationOpen L.obj (s k), hk, ?_⟩
  rw [← morphismRestrict_ι_assoc, ι_linearSystemMap, comp_pointMap, comp_pointMap,
    pointMap_congr p s (morphismRestrict_ι g _)]
  exact pointMap_eq p s _ _

lemma linearSystemMap_toSpec : linearSystemMap p hs ≫ projectiveSpaceToSpec K n = p := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨k, hk⟩ := exists_mem_trivializationOpen hs x
  refine ⟨_, hk, ?_⟩
  rw [← Category.assoc, comp_linearSystemMap p hs _ k (ι_mem _), pointMap_toSpec]

/-- Two points of `U_j` with the same image have the same ratios. -/
lemma chartRingHom_eq_of_comp_eq {g₁ g₂ : T ⟶ X} {j : Fin (n + 1)}
    (h₁ : ∀ t, g₁ t ∈ trivializationOpen L.obj (s j))
    (h₂ : ∀ t, g₂ t ∈ trivializationOpen L.obj (s j))
    (H : g₁ ≫ linearSystemMap p hs = g₂ ≫ linearSystemMap p hs) :
    chartRingHom p s g₁ j = chartRingHom p s g₂ j := by
  rw [comp_linearSystemMap p hs g₁ j h₁, comp_linearSystemMap p hs g₂ j h₂] at H
  exact chartRingHom_eq_of_pointMap_eq p s h₁ h₂ H

/-- Two points of `U_j` with the same image are cut out by the same linear combinations. -/
lemma vanishesAlong_linComb_iff_of_comp_eq {g₁ g₂ : T ⟶ X} {j : Fin (n + 1)}
    (h₁ : ∀ t, g₁ t ∈ trivializationOpen L.obj (s j))
    (h₂ : ∀ t, g₂ t ∈ trivializationOpen L.obj (s j))
    (H : g₁ ≫ linearSystemMap p hs = g₂ ≫ linearSystemMap p hs) (c : Fin (n + 1) → K) :
    VanishesAlong L g₁ (linComb p s c) ↔ VanishesAlong L g₂ (linComb p s c) := by
  rw [vanishesAlong_iff_sectionRatio_eq_zero h₁, vanishesAlong_iff_sectionRatio_eq_zero h₂,
    sectionRatio_linComb_eq_chartRingHom p s h₁, sectionRatio_linComb_eq_chartRingHom p s h₂,
    chartRingHom_eq_of_comp_eq p hs h₁ h₂ H]

/-- Two points of `U_j` over the same point of `Spec K` with the same ratios have the same
image. -/
lemma comp_eq_of_sectionRatio_eq {g₁ g₂ : T ⟶ X} {j : Fin (n + 1)}
    (h₁ : ∀ t, g₁ t ∈ trivializationOpen L.obj (s j))
    (h₂ : ∀ t, g₂ t ∈ trivializationOpen L.obj (s j)) (hp : g₁ ≫ p = g₂ ≫ p)
    (hr : ∀ i, sectionRatio L g₁ (s i) (s j) = sectionRatio L g₂ (s i) (s j)) :
    g₁ ≫ linearSystemMap p hs = g₂ ≫ linearSystemMap p hs := by
  rw [comp_linearSystemMap p hs g₁ j h₁, comp_linearSystemMap p hs g₂ j h₂]
  have he : chartRingHom p s g₁ j = chartRingHom p s g₂ j := by
    apply MvPolynomial.ringHom_ext
    · intro k
      rw [chartRingHom_C, chartRingHom_C, hp]
    · intro i
      rw [chartRingHom_X, chartRingHom_X, hr]
  exact chartMap_ringHom_congr _ he _ _ _

/-- A field-valued point whose image lies in the chart `D₊(X_i)` lands in the nonvanishing
locus of `s i`. -/
lemma mem_trivializationOpen_of_comp_mem {K' : Type u} [Field K']
    (y : Spec (CommRingCat.of K') ⟶ X) (i : Fin (n + 1))
    (hy : (y ≫ linearSystemMap p hs) (IsLocalRing.closedPoint K') ∈
      projectiveSpaceCoordinateOpen K n i) :
    y (IsLocalRing.closedPoint K') ∈ trivializationOpen L.obj (s i) := by
  obtain ⟨k, hk⟩ := exists_mem_trivializationOpen hs (y (IsLocalRing.closedPoint K'))
  have hk' : ∀ t, y t ∈ trivializationOpen L.obj (s k) := fun t ↦ by
    rwa [Subsingleton.elim t (IsLocalRing.closedPoint K')]
  rw [comp_linearSystemMap p hs y k hk'] at hy
  have h2 : IsLocalRing.closedPoint K' ∈
      pointMap p s y k hk' ⁻¹ᵁ projectiveSpaceCoordinateOpen K n i := hy
  rw [pointMap_preimage] at h2
  by_contra hmem
  rw [← vanishesAlong_iff_not_mem, vanishesAlong_iff_sectionRatio_eq_zero hk'] at hmem
  rw [hmem, Scheme.basicOpen_zero] at h2
  exact h2

/-- A point landing in `U_j` maps into the chart `D₊(X_j)`. -/
lemma comp_mem_coordinateOpen {g : T ⟶ X} {j : Fin (n + 1)}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s j)) (t : T) :
    (g ≫ linearSystemMap p hs) t ∈ projectiveSpaceCoordinateOpen K n j := by
  rw [comp_linearSystemMap p hs g j hg]
  change t ∈ pointMap p s g j hg ⁻¹ᵁ projectiveSpaceCoordinateOpen K n j
  rw [pointMap_preimage, sectionRatio_self hg, Scheme.basicOpen_one]
  trivial

end glue

end Langlands.AlgebraicGeometry.LinearSystem
