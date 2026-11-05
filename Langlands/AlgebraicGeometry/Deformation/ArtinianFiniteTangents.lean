import Langlands.AlgebraicGeometry.Deformation.ArtinianDualNumbers
import Langlands.AlgebraicGeometry.Deformation.ArtinianQuotients
import Mathlib.LinearAlgebra.Pi

/-! # Actual finite split tangent tests -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianTest.FiniteTangents

variable (k K ι : Type u) [CommRing k] [Field K] [Algebra k K] [Fintype ι]

/-- The actual square-zero ring with one independent direction per index. -/
abbrev ring := TrivSqZeroExt K (ι → K)

instance : IsLocalRing (ring K ι) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rw [add_comm, ← eq_sub_iff_add_eq] at h
    rcases eq_or_ne a.fst 0 with ha | ha <;>
      simp [TrivSqZeroExt.isUnit_iff_isUnit_fst, h, ha]

instance : IsArtinianRing (ring K ι) := by
  have h : IsArtinian K (ring K ι) :=
    inferInstanceAs (IsArtinian K (K × (ι → K)))
  let : IsScalarTower K (ring K ι) (ring K ι) := ⟨by
    intro r x y
    apply TrivSqZeroExt.ext
    · change (r * x.fst) * y.fst = r * (x.fst * y.fst)
      exact mul_assoc _ _ _
    · funext i
      change (r * x.fst) * y.snd i + (r * x.snd i) * y.fst =
        r * (x.fst * y.snd i + x.snd i * y.fst)
      ring⟩
  exact isArtinian_of_tower K (S := ring K ι) h

/-- The actual augmented Artinian test on this ring. -/
def test : ArtinianTest k K :=
  mk (ring K ι) (TrivSqZeroExt.fstHom k K (ι → K))
    (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩)

/-- Its augmentation as an actual arrow to the residue test. -/
def reduction : test k K ι ⟶ residue k K :=
  homMk (TrivSqZeroExt.fstHom k K (ι → K)) (by ext; rfl)

/-- The constant section of this particular split test. -/
def sectionMap : residue k K ⟶ test k K ι :=
  homMk (TrivSqZeroExt.inlAlgHom k K (ι → K)) (by ext; rfl)

@[simp]
lemma sectionMap_reduction :
    sectionMap k K ι ≫ reduction k K ι = 𝟙 (residue k K) := by
  apply ArtinianTest.hom_ext
  rfl

/-- The entire multi-direction augmentation is an elementary surjection. -/
lemma reduction_elementary : IsElementarySurjection (reduction k K ι) := by
  refine ⟨fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩, ?_⟩
  rw [← ker_augmentation (test k K ι)]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx' : x.fst = 0 := hx
  have hy' : y.fst = 0 := hy
  change x * y = 0
  apply TrivSqZeroExt.ext
  · change x.fst * y.fst = 0
    rw [hx', zero_mul]
  · funext i
    change x.fst * y.snd i + x.snd i * y.fst = 0
    rw [hx', hy', zero_mul, mul_zero, zero_add]

variable {ι}

/-- An actual coordinate projection to the dual-number test. -/
def axis (i : ι) : test k K ι ⟶ dualNumbers k K :=
  homMk ((TrivSqZeroExt.map (LinearMap.proj i : (ι → K) →ₗ[K] K)).restrictScalars k)
    (by
      apply AlgHom.ext
      intro z
      exact TrivSqZeroExt.fst_map (LinearMap.proj i : (ι → K) →ₗ[K] K) z)

/-- Simultaneous weighted projection to one dual-number direction. -/
def weighted (c : ι → K) : test k K ι ⟶ dualNumbers k K :=
  homMk ((TrivSqZeroExt.map
    (∑ i, c i • (LinearMap.proj i : (ι → K) →ₗ[K] K))).restrictScalars k)
    (by
      apply AlgHom.ext
      intro z
      exact TrivSqZeroExt.fst_map
        (∑ i, c i • (LinearMap.proj i : (ι → K) →ₗ[K] K)) z)

@[simp]
lemma axis_reduction (i : ι) :
    axis k K i ≫ dualReduction k K = reduction k K ι := by
  apply ArtinianTest.hom_ext
  apply AlgHom.ext
  intro z
  exact TrivSqZeroExt.fst_map (LinearMap.proj i : (ι → K) →ₗ[K] K) z

@[simp]
lemma weighted_reduction (c : ι → K) :
    weighted k K c ≫ dualReduction k K = reduction k K ι := by
  apply ArtinianTest.hom_ext
  apply AlgHom.ext
  intro z
  exact TrivSqZeroExt.fst_map
    (∑ i, c i • (LinearMap.proj i : (ι → K) →ₗ[K] K)) z

@[simp]
lemma sectionMap_weighted (c : ι → K) :
    sectionMap k K ι ≫ weighted k K c = dualSection k K := by
  apply ArtinianTest.hom_ext
  apply AlgHom.ext
  intro z
  exact TrivSqZeroExt.map_inl
    (∑ i, c i • (LinearMap.proj i : (ι → K) →ₗ[K] K)) z

variable [DecidableEq ι]

/-- The actual inclusion of one dual-number direction. -/
def includeAxis (i : ι) : dualNumbers k K ⟶ test k K ι :=
  homMk ((TrivSqZeroExt.map (LinearMap.single K (fun _ : ι ↦ K) i)).restrictScalars k)
    (by
      apply AlgHom.ext
      intro z
      exact TrivSqZeroExt.fst_map (LinearMap.single K (fun _ : ι ↦ K) i) z)

@[simp]
lemma includeAxis_reduction (i : ι) :
    includeAxis k K i ≫ reduction k K ι = dualReduction k K := by
  apply ArtinianTest.hom_ext
  apply AlgHom.ext
  intro z
  exact TrivSqZeroExt.fst_map (LinearMap.single K (fun _ : ι ↦ K) i) z

omit [DecidableEq ι] in
@[simp]
lemma sectionMap_axis (i : ι) :
    sectionMap k K ι ≫ axis k K i = dualSection k K := by
  apply ArtinianTest.hom_ext
  apply AlgHom.ext
  intro z
  exact TrivSqZeroExt.map_inl (LinearMap.proj i : (ι → K) →ₗ[K] K) z

/-- The exact diagonal and off-diagonal coordinate equations. -/
lemma includeAxis_axis (i j : ι) :
    includeAxis k K i ≫ axis k K j =
      if i = j then 𝟙 (dualNumbers k K) else dualReduction k K ≫ dualSection k K := by
  by_cases h : i = j
  · subst j
    rw [ite_eq_left (rfl : i = i)]
    apply ArtinianTest.hom_ext
    apply AlgHom.ext
    intro z
    change DualNumber K at z
    change TrivSqZeroExt.map (LinearMap.proj i : (ι → K) →ₗ[K] K)
      (TrivSqZeroExt.map (LinearMap.single K (fun _ : ι ↦ K) i) z) = z
    apply TrivSqZeroExt.ext <;> simp
  · rw [ite_eq_right h]
    apply ArtinianTest.hom_ext
    apply AlgHom.ext
    intro z
    change DualNumber K at z
    change TrivSqZeroExt.map (LinearMap.proj j : (ι → K) →ₗ[K] K)
      (TrivSqZeroExt.map (LinearMap.single K (fun _ : ι ↦ K) i) z) =
        TrivSqZeroExt.inl z.fst
    apply TrivSqZeroExt.ext <;> simp [LinearMap.single_apply, Ne.symm h]

/-- A weighted projection restricts on each included direction to epsilon scaling. -/
@[simp]
lemma includeAxis_weighted (i : ι) (c : ι → K) :
    includeAxis k K i ≫ weighted k K c = dualScale k K (c i) := by
  apply ArtinianTest.hom_ext
  apply AlgHom.ext
  intro z
  change DualNumber K at z
  apply TrivSqZeroExt.ext
  · change (TrivSqZeroExt.map
      (∑ j, c j • (LinearMap.proj j : (ι → K) →ₗ[K] K))
      (TrivSqZeroExt.map (LinearMap.single K (fun _ : ι ↦ K) i) z)).fst = _
    simp [dualScale_fst]
  · change (TrivSqZeroExt.map
      (∑ j, c j • (LinearMap.proj j : (ι → K) →ₗ[K] K))
      (TrivSqZeroExt.map (LinearMap.single K (fun _ : ι ↦ K) i) z)).snd = _
    simp [dualScale_snd, LinearMap.sum_apply, LinearMap.single_apply, Pi.single_apply]

end Langlands.AlgebraicGeometry.Deformation.ArtinianTest.FiniteTangents
