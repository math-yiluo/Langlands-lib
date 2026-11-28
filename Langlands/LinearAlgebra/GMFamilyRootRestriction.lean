import Langlands.LinearAlgebra.GMFamilyLeviRootBasis
import Langlands.LinearAlgebra.GMFamiliesRoots
import Langlands.LinearAlgebra.GMFamilyGramVolume
import Langlands.LinearAlgebra.GMFamilyDescentVolume
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Restricting a root arrangement along an isometric embedding -/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open Classical Submodule

namespace Langlands.GMFamily

namespace RootRestriction

variable {E E₀ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  (φ : E →ₗᵢ[ℝ] E₀)

/-- Restriction of a vector of the larger space: the adjoint of the embedding. -/
def res : E₀ →ₗ[ℝ] E := LinearMap.adjoint φ.toLinearMap

variable {φ}

theorem inner_res (γ : E₀) (x : E) : ⟪res φ γ, x⟫ = ⟪γ, φ x⟫ := by
  rw [res, LinearMap.adjoint_inner_left]
  rfl

theorem res_apply_self (x : E) : res φ (φ x) = x := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_res, LinearIsometry.inner_map_map]

variable (φ)

/-- The nonzero restrictions of the roots. -/
def restrictRoots (R₀ : Finset E₀) : Finset E := (R₀.image (res φ)).erase 0

/-- The roots of the larger space whose restriction lies in a given set. -/
def up (R₀ : Finset E₀) (S : Finset E) : Finset E₀ := R₀.filter (fun γ => res φ γ ∈ S)

variable {φ} {R₀ : Finset E₀}

theorem mem_restrictRoots {α : E} :
    α ∈ restrictRoots φ R₀ ↔ α ≠ 0 ∧ ∃ γ ∈ R₀, res φ γ = α := by
  simp [restrictRoots, Finset.mem_erase, Finset.mem_image]

theorem mem_up {S : Finset E} {γ : E₀} : γ ∈ up φ R₀ S ↔ γ ∈ R₀ ∧ res φ γ ∈ S :=
  Finset.mem_filter

theorem posSet_restrictRoots (h : E) :
    posSet (restrictRoots φ R₀) h = (posSet R₀ (φ h)).image (res φ) := by
  ext α
  simp only [mem_posSet_iff, Finset.mem_image, mem_restrictRoots]
  constructor
  · rintro ⟨⟨_, γ, hγ, rfl⟩, hpos⟩
    exact ⟨γ, ⟨hγ, by rwa [← inner_res]⟩, rfl⟩
  · rintro ⟨γ, ⟨hγ, hpos⟩, rfl⟩
    rw [← inner_res] at hpos
    refine ⟨⟨fun h0 => ?_, γ, hγ, rfl⟩, hpos⟩
    rw [h0, inner_zero_left] at hpos
    exact lt_irrefl _ hpos

theorem up_posSet (h : E) : up φ R₀ (posSet (restrictRoots φ R₀) h) = posSet R₀ (φ h) := by
  ext γ
  rw [mem_up, posSet_restrictRoots, Finset.mem_image]
  constructor
  · rintro ⟨hγ, γ', hγ', he⟩
    refine mem_posSet_iff.mpr ⟨hγ, ?_⟩
    rw [← inner_res, ← he, inner_res]
    exact (mem_posSet_iff.mp hγ').2
  · intro hγ
    exact ⟨(mem_posSet_iff.mp hγ).1, γ, hγ, rfl⟩

theorem res_image_posSet (h : E) :
    (posSet R₀ (φ h)).image (res φ) = posSet (restrictRoots φ R₀) h :=
  (posSet_restrictRoots h).symm

/-! ### Subspaces -/

/-- The image of a subspace. -/
abbrev mapSub (V : Submodule ℝ E) : Submodule ℝ E₀ := V.map φ.toLinearMap

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem mem_mapSub_iff {V : Submodule ℝ E} {x : E} : φ x ∈ mapSub (φ := φ) V ↔ x ∈ V := by
  constructor
  · rintro ⟨y, hy, he⟩
    have : y = x := φ.injective he
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem coe_restrictedRoot_mapSub (V : Submodule ℝ E) (γ : E₀) :
    (restrictedRoot (mapSub (φ := φ) V) γ : E₀) = φ (restrictedRoot V (res φ γ) : E) := by
  change (mapSub (φ := φ) V).starProjection γ = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨_, (restrictedRoot V (res φ γ)).prop, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    change ⟪γ - φ (restrictedRoot V (res φ γ) : E), φ v⟫ = 0
    rw [inner_sub_left, LinearIsometry.inner_map_map, ← inner_res,
      ← inner_restrictedRoot hv (a := V), sub_self]

theorem restrictedRoot_mapSub_eq_zero_iff (V : Submodule ℝ E) (γ : E₀) :
    restrictedRoot (mapSub (φ := φ) V) γ = 0 ↔ restrictedRoot V (res φ γ) = 0 := by
  rw [← Submodule.coe_eq_zero, coe_restrictedRoot_mapSub, ← Submodule.coe_eq_zero (x := restrictedRoot V _)]
  constructor
  · intro h
    exact φ.injective (h.trans φ.map_zero.symm)
  · intro h
    rw [h, φ.map_zero]

theorem isRegular_mapSub_iff (V : Submodule ℝ E) (h : E) :
    IsRegular R₀ (mapSub (φ := φ) V) (φ h) ↔ IsRegular (restrictRoots φ R₀) V h := by
  unfold IsRegular
  rw [mem_mapSub_iff]
  apply and_congr_right
  intro _
  constructor
  · intro H α hα hne
    obtain ⟨-, γ, hγ, rfl⟩ := mem_restrictRoots.mp hα
    rw [inner_res]
    exact H γ hγ (fun h0 => hne ((restrictedRoot_mapSub_eq_zero_iff V γ).mp h0))
  · intro H γ hγ hne
    rw [← inner_res]
    have hne' := fun h0 => hne ((restrictedRoot_mapSub_eq_zero_iff V γ).mpr h0)
    have hγ0 : res φ γ ≠ 0 := by
      intro h0
      apply hne'
      rw [h0]
      simp [restrictedRoot]
    exact H _ (mem_restrictRoots.mpr ⟨hγ0, γ, hγ, rfl⟩) hne'

/-! ### Chambers -/

/-- Restriction of a set of roots of the larger space. -/
def down (S₀ : Finset E₀) : Finset E := S₀.image (res φ)

theorem mem_parabolics_mapSub_iff {V : Submodule ℝ E} {S₀ : Finset E₀} :
    S₀ ∈ parabolics R₀ (mapSub (φ := φ) V) ↔
      ∃ h : E, IsRegular (restrictRoots φ R₀) V h ∧ S₀ = posSet R₀ (φ h) := by
  rw [mem_parabolics_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h, -, rfl⟩ := hx.1
    exact ⟨h, (isRegular_mapSub_iff V h).mp hx, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨φ h, (isRegular_mapSub_iff V h).mpr hh, rfl⟩

theorem down_mem_parabolics {V : Submodule ℝ E} {S₀ : Finset E₀}
    (hS : S₀ ∈ parabolics R₀ (mapSub (φ := φ) V)) :
    down (φ := φ) S₀ ∈ parabolics (restrictRoots φ R₀) V := by
  obtain ⟨h, hh, rfl⟩ := mem_parabolics_mapSub_iff.mp hS
  exact mem_parabolics_iff.mpr ⟨h, hh, res_image_posSet h⟩

theorem up_mem_parabolics {V : Submodule ℝ E} {S : Finset E}
    (hS : S ∈ parabolics (restrictRoots φ R₀) V) :
    up φ R₀ S ∈ parabolics R₀ (mapSub (φ := φ) V) := by
  obtain ⟨h, hh, rfl⟩ := mem_parabolics_iff.mp hS
  exact mem_parabolics_mapSub_iff.mpr ⟨h, hh, up_posSet h⟩

theorem up_down {V : Submodule ℝ E} {S₀ : Finset E₀}
    (hS : S₀ ∈ parabolics R₀ (mapSub (φ := φ) V)) : up φ R₀ (down (φ := φ) S₀) = S₀ := by
  obtain ⟨h, -, rfl⟩ := mem_parabolics_mapSub_iff.mp hS
  rw [down, res_image_posSet, up_posSet]

theorem down_up {V : Submodule ℝ E} {S : Finset E}
    (hS : S ∈ parabolics (restrictRoots φ R₀) V) : down (φ := φ) (up φ R₀ S) = S := by
  obtain ⟨h, -, rfl⟩ := mem_parabolics_iff.mp hS
  rw [up_posSet, down, res_image_posSet]

/-! ### The isometric equivalence of subspaces -/

/-- A subspace and its image. -/
def mapEquiv (V : Submodule ℝ E) : V ≃ₗ[ℝ] mapSub (φ := φ) V where
  toFun v := ⟨φ v, v, v.prop, rfl⟩
  invFun w := ⟨res φ w, by
    obtain ⟨v, hv, he⟩ := w.prop
    rw [← he]
    change res φ (φ v) ∈ V
    rw [res_apply_self]
    exact hv⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
  left_inv v := by ext; exact res_apply_self (v : E)
  right_inv w := by
    obtain ⟨v, hv, he⟩ := w.prop
    ext
    change φ (res φ (w : E₀)) = w
    rw [← he]
    change φ (res φ (φ v)) = φ v
    rw [res_apply_self]

theorem coe_mapEquiv (V : Submodule ℝ E) (v : V) : (mapEquiv (φ := φ) V v : E₀) = φ v := rfl

theorem inner_mapEquiv (V : Submodule ℝ E) (v w : V) :
    ⟪(mapEquiv (φ := φ) V v : E₀), (mapEquiv (φ := φ) V w : E₀)⟫ = ⟪(v : E), (w : E)⟫ :=
  φ.inner_map_map _ _

theorem restrictedRoot_mapSub (V : Submodule ℝ E) (γ : E₀) :
    restrictedRoot (mapSub (φ := φ) V) γ = mapEquiv (φ := φ) V (restrictedRoot V (res φ γ)) :=
  Subtype.ext (coe_restrictedRoot_mapSub V γ)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem gramVolume_map {ι : Type*} [Fintype ι] (v : ι → E) :
    gramVolume (fun i => φ (v i)) = gramVolume v := by
  unfold gramVolume
  congr 2
  ext i j
  simp [LinearIsometry.inner_map_map]

/-- The restricted roots of a lifted set are the images of the restricted roots. -/
theorem restrictedRoots_up {V : Submodule ℝ E} {S : Finset E}
    (hS : S ⊆ restrictRoots φ R₀) :
    restrictedRoots (mapSub (φ := φ) V) (up φ R₀ S) =
      (restrictedRoots V S).image (mapEquiv (φ := φ) V) := by
  ext w
  simp only [restrictedRoots, Finset.mem_image, mem_up]
  constructor
  · rintro ⟨γ, ⟨_, hγS⟩, rfl⟩
    exact ⟨restrictedRoot V (res φ γ), ⟨res φ γ, hγS, rfl⟩, (restrictedRoot_mapSub V γ).symm⟩
  · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    obtain ⟨-, γ, hγ, rfl⟩ := mem_restrictRoots.mp (hS hα)
    exact ⟨γ, ⟨hγ, hα⟩, restrictedRoot_mapSub V γ⟩

theorem simpleRoots_up {V : Submodule ℝ E} {S : Finset E} (hS : S ⊆ restrictRoots φ R₀) :
    simpleRoots (mapSub (φ := φ) V) (up φ R₀ S) =
      (simpleRoots V S).image (mapEquiv (φ := φ) V) := by
  let f := mapEquiv (φ := φ) V
  ext w
  simp only [simpleRoots, Finset.mem_filter, Finset.mem_image, restrictedRoots_up hS]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hind⟩
    refine ⟨v, ⟨hv, fun ⟨u, hu, x, hx, he⟩ => hind ⟨f u, ⟨u, hu, rfl⟩, f x, ⟨x, hx, rfl⟩, ?_⟩⟩, rfl⟩
    rw [he, map_add]
  · rintro ⟨v, ⟨hv, hind⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨x, hx, rfl⟩, he⟩
    apply hind
    refine ⟨u, hu, x, hx, f.injective ?_⟩
    rw [he, map_add]

/-- The bijection between the simple roots of a set and of its lift. -/
def simpleEquiv {V : Submodule ℝ E} {S : Finset E} (hS : S ⊆ restrictRoots φ R₀) :
    simpleRoots V S ≃ simpleRoots (mapSub (φ := φ) V) (up φ R₀ S) :=
  Equiv.ofBijective (fun v => ⟨mapEquiv (φ := φ) V v, by
      rw [simpleRoots_up hS]
      exact Finset.mem_image_of_mem _ v.prop⟩)
    ⟨fun v w h => Subtype.ext ((mapEquiv (φ := φ) V).injective (congrArg Subtype.val h)),
      fun w => by
        have hw : (w : mapSub (φ := φ) V) ∈ (simpleRoots V S).image (mapEquiv (φ := φ) V) := by
          rw [← simpleRoots_up hS]
          exact w.prop
        obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hw
        exact ⟨⟨v, hv⟩, Subtype.ext he⟩⟩

theorem coe_simpleEquiv {V : Submodule ℝ E} {S : Finset E} (hS : S ⊆ restrictRoots φ R₀)
    (v : simpleRoots V S) :
    ((simpleEquiv hS v : mapSub (φ := φ) V) : E₀) = φ ((v : V) : E) := rfl

/-- The parameter on a subspace corresponding to a parameter on its image. -/
def pullParam (V : Submodule ℝ E) (Λ₀ : StrongDual ℝ (mapSub (φ := φ) V)) : StrongDual ℝ V :=
  Λ₀.comp (LinearMap.toContinuousLinearMap (mapEquiv (φ := φ) V).toLinearMap)

theorem pullParam_apply (V : Submodule ℝ E) (Λ₀ : StrongDual ℝ (mapSub (φ := φ) V)) (v : V) :
    pullParam V Λ₀ v = Λ₀ (mapEquiv (φ := φ) V v) := rfl

theorem theta_up {V : Submodule ℝ E} {S : Finset E} (hS : S ⊆ restrictRoots φ R₀)
    (Λ₀ : StrongDual ℝ (mapSub (φ := φ) V)) :
    theta (mapSub (φ := φ) V) (up φ R₀ S) Λ₀ = theta V S (pullParam V Λ₀) := by
  let e := simpleEquiv (φ := φ) (V := V) hS
  unfold theta thetaOf
  congr 1
  · congr 2
    rw [← gramVolume_reindex e]
    change gramVolume (fun v : simpleRoots V S => φ ((v : V) : E)) = _
    exact gramVolume_map _
  · exact (Fintype.prod_equiv e _ _ (fun v => rfl)).symm


/-- The parameter on the image of a subspace corresponding to a parameter on the subspace. -/
def pushParam (V : Submodule ℝ E) (Λ : StrongDual ℝ V) : StrongDual ℝ (mapSub (φ := φ) V) :=
  Λ.comp (LinearMap.toContinuousLinearMap (mapEquiv (φ := φ) V).symm.toLinearMap)

theorem pullParam_pushParam (V : Submodule ℝ E) (Λ : StrongDual ℝ V) :
    pullParam V (pushParam (φ := φ) V Λ) = Λ := by
  ext v
  simp [pullParam, pushParam]

theorem pushParam_pullParam (V : Submodule ℝ E) (Λ₀ : StrongDual ℝ (mapSub (φ := φ) V)) :
    pushParam V (pullParam V Λ₀) = Λ₀ := by
  ext w
  simp [pullParam, pushParam]

/-- Pulling back parameters as a continuous linear equivalence. -/
def pullEquiv (V : Submodule ℝ E) : StrongDual ℝ (mapSub (φ := φ) V) ≃L[ℝ] StrongDual ℝ V :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := pullParam V
      invFun := pushParam V
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := pushParam_pullParam V
      right_inv := pullParam_pushParam V }

theorem coe_pullEquiv (V : Submodule ℝ E) : ⇑(pullEquiv (φ := φ) V) = pullParam V := rfl

theorem coe_pullEquiv_symm (V : Submodule ℝ E) : ⇑(pullEquiv (φ := φ) V).symm = pushParam V := rfl

variable (φ) in
/-- A family on the larger space from a family on the smaller one. -/
def pushFam (V : Submodule ℝ E) (c : Finset E → StrongDual ℝ V → ℂ) :
    Finset E₀ → StrongDual ℝ (mapSub (φ := φ) V) → ℂ :=
  fun S₀ Λ₀ => c (down (φ := φ) S₀) (pullParam V Λ₀)

theorem pushFam_up {V : Submodule ℝ E} {c : Finset E → StrongDual ℝ V → ℂ} {S : Finset E}
    (hS : S ∈ parabolics (restrictRoots φ R₀) V) (Λ₀ : StrongDual ℝ (mapSub (φ := φ) V)) :
    pushFam φ V c (up φ R₀ S) Λ₀ = c S (pullParam V Λ₀) := by
  rw [pushFam, down_up hS]

theorem parabolics_subset_restrictRoots {V : Submodule ℝ E} {S : Finset E}
    (hS : S ∈ parabolics (restrictRoots φ R₀) V) : S ⊆ restrictRoots φ R₀ :=
  Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1

/-- Sums over the chambers of the image of a subspace. -/
theorem sum_parabolics_mapSub {M : Type*} [AddCommMonoid M] (V : Submodule ℝ E)
    (F : Finset E₀ → M) :
    ∑ S₀ ∈ parabolics R₀ (mapSub (φ := φ) V), F S₀ =
      ∑ S ∈ parabolics (restrictRoots φ R₀) V, F (up φ R₀ S) := by
  symm
  apply Finset.sum_nbij' (fun S => up φ R₀ S) (fun S₀ => down (φ := φ) S₀)
  · intro S hS
    exact up_mem_parabolics hS
  · intro S₀ hS₀
    exact down_mem_parabolics hS₀
  · intro S hS
    exact down_up hS
  · intro S₀ hS₀
    exact up_down hS₀
  · intro S _
    rfl

/-- The supplementary function of a pushed family. -/
theorem cM_pushFam (V : Submodule ℝ E) (c : Finset E → StrongDual ℝ V → ℂ)
    (Λ₀ : StrongDual ℝ (mapSub (φ := φ) V)) :
    cM R₀ (mapSub (φ := φ) V) (pushFam φ V c) Λ₀ =
      cM (restrictRoots φ R₀) V c (pullParam V Λ₀) := by
  unfold cM
  rw [sum_parabolics_mapSub]
  apply Finset.sum_congr rfl
  intro S hS
  rw [pushFam_up hS, theta_up (parabolics_subset_restrictRoots hS)]

theorem mem_simpleRoots_up_iff {V : Submodule ℝ E} {S : Finset E}
    (hS : S ⊆ restrictRoots φ R₀) (v : V) :
    mapEquiv (φ := φ) V v ∈ simpleRoots (mapSub (φ := φ) V) (up φ R₀ S) ↔
      v ∈ simpleRoots V S := by
  rw [simpleRoots_up hS]
  exact (mapEquiv (φ := φ) V).injective.mem_finset_image

/-- Adjacency of chambers is the same in both spaces. -/
theorem isAdjacentAlong_up_iff {V : Submodule ℝ E} {S S' : Finset E}
    (hS : S ⊆ restrictRoots φ R₀) (hS' : S' ⊆ restrictRoots φ R₀) (v : V) :
    IsAdjacentAlong R₀ (mapSub (φ := φ) V) (up φ R₀ S) (up φ R₀ S') (mapEquiv (φ := φ) V v) ↔
      IsAdjacentAlong (restrictRoots φ R₀) V S S' v := by
  unfold IsAdjacentAlong
  rw [mem_simpleRoots_up_iff hS, ← map_neg, mem_simpleRoots_up_iff hS']
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  have hprop (γ : E₀) : (∀ t : ℝ, restrictedRoot (mapSub (φ := φ) V) γ ≠
      t • mapEquiv (φ := φ) V v) ↔ ∀ t : ℝ, restrictedRoot V (res φ γ) ≠ t • v := by
    apply forall_congr'; intro t
    rw [restrictedRoot_mapSub, ← map_smul, Ne, Ne,
      (mapEquiv (φ := φ) V).injective.eq_iff]
  constructor
  · intro H α hα hne
    obtain ⟨-, γ, hγ, rfl⟩ := mem_restrictRoots.mp hα
    have h := H γ hγ ((hprop γ).mpr hne)
    simpa only [mem_up, hγ, true_and] using h
  · intro H γ hγ hne
    rw [hprop] at hne
    by_cases h0 : res φ γ = 0
    · exfalso
      apply hne 0
      rw [h0, zero_smul]
      simp [restrictedRoot]
    · have h := H (res φ γ) (mem_restrictRoots.mpr ⟨h0, γ, hγ, rfl⟩) hne
      simpa only [mem_up, hγ, true_and] using h

/-- A family is a `(G, M)`-family exactly when its push is. -/
theorem isFamily_pushFam_iff (V : Submodule ℝ E) (c : Finset E → StrongDual ℝ V → ℂ) :
    IsFamily R₀ (mapSub (φ := φ) V) (pushFam φ V c) ↔ IsFamily (restrictRoots φ R₀) V c := by
  unfold IsFamily
  constructor
  · rintro ⟨hsm, hadj⟩
    refine ⟨fun S hS => ?_, fun S hS S' hS' v hv Λ hΛ => ?_⟩
    · have h := hsm _ (up_mem_parabolics hS)
      have h' : pushFam φ V c (up φ R₀ S) = c S ∘ pullEquiv (φ := φ) V := by
        funext Λ₀
        exact pushFam_up hS Λ₀
      rw [h'] at h
      exact (ContinuousLinearEquiv.contDiff_comp_iff _).mp h
    · have h := hadj _ (up_mem_parabolics hS) _ (up_mem_parabolics hS') (mapEquiv (φ := φ) V v)
        ((isAdjacentAlong_up_iff (parabolics_subset_restrictRoots hS)
          (parabolics_subset_restrictRoots hS') v).mpr hv) (pushParam V Λ)
        (by simpa [pushParam] using hΛ)
      rwa [pushFam_up hS, pushFam_up hS', pullParam_pushParam] at h
  · rintro ⟨hsm, hadj⟩
    refine ⟨fun S₀ hS₀ => ?_, fun S₀ hS₀ S₀' hS₀' v₀ hv Λ₀ hΛ => ?_⟩
    · have h' : ContDiff ℝ ∞ (c (down (φ := φ) S₀) ∘ ⇑(pullEquiv (φ := φ) V)) :=
        (ContinuousLinearEquiv.contDiff_comp_iff _).mpr (hsm _ (down_mem_parabolics hS₀))
      exact h'
    · have hd := down_mem_parabolics hS₀
      have hd' := down_mem_parabolics hS₀'
      rw [← up_down hS₀, ← up_down hS₀'] at hv
      have hv' : IsAdjacentAlong R₀ (mapSub (φ := φ) V) (up φ R₀ (down (φ := φ) S₀))
          (up φ R₀ (down (φ := φ) S₀'))
          (mapEquiv (φ := φ) V ((mapEquiv (φ := φ) V).symm v₀)) := by
        rwa [LinearEquiv.apply_symm_apply]
      rw [isAdjacentAlong_up_iff (parabolics_subset_restrictRoots hd)
        (parabolics_subset_restrictRoots hd')] at hv'
      exact hadj _ hd _ hd' _ hv' (pullParam V Λ₀) (by
        rw [pullParam_apply, LinearEquiv.apply_symm_apply]
        exact hΛ)


/-! ### Faces and Levi flats -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem mem_faces_mapSub_iff {V : Submodule ℝ E} {Q₀ : Finset E₀} :
    Q₀ ∈ faces R₀ (mapSub (φ := φ) V) ↔ ∃ h ∈ V, Q₀ = posSet R₀ (φ h) := by
  rw [mem_faces_iff]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨φ h, ⟨h, hh, rfl⟩, rfl⟩

theorem up_mem_faces {V : Submodule ℝ E} {Q : Finset E}
    (hQ : Q ∈ faces (restrictRoots φ R₀) V) : up φ R₀ Q ∈ faces R₀ (mapSub (φ := φ) V) := by
  obtain ⟨h, hh, rfl⟩ := mem_faces_iff.mp hQ
  exact mem_faces_mapSub_iff.mpr ⟨h, hh, up_posSet h⟩

theorem down_mem_faces {V : Submodule ℝ E} {Q₀ : Finset E₀}
    (hQ : Q₀ ∈ faces R₀ (mapSub (φ := φ) V)) :
    down (φ := φ) Q₀ ∈ faces (restrictRoots φ R₀) V := by
  obtain ⟨h, hh, rfl⟩ := mem_faces_mapSub_iff.mp hQ
  exact mem_faces_iff.mpr ⟨h, hh, res_image_posSet h⟩

theorem up_down_of_faces {V : Submodule ℝ E} {Q₀ : Finset E₀}
    (hQ : Q₀ ∈ faces R₀ (mapSub (φ := φ) V)) : up φ R₀ (down (φ := φ) Q₀) = Q₀ := by
  obtain ⟨h, -, rfl⟩ := mem_faces_mapSub_iff.mp hQ
  rw [down, res_image_posSet, up_posSet]

theorem down_up_of_faces {V : Submodule ℝ E} {Q : Finset E}
    (hQ : Q ∈ faces (restrictRoots φ R₀) V) : down (φ := φ) (up φ R₀ Q) = Q := by
  obtain ⟨h, -, rfl⟩ := mem_faces_iff.mp hQ
  rw [up_posSet, down, res_image_posSet]

theorem faces_mapSub (V : Submodule ℝ E) :
    faces R₀ (mapSub (φ := φ) V) = (faces (restrictRoots φ R₀) V).image (up φ R₀) := by
  ext Q₀
  rw [Finset.mem_image]
  constructor
  · intro hQ
    exact ⟨_, down_mem_faces hQ, up_down_of_faces hQ⟩
  · rintro ⟨Q, hQ, rfl⟩
    exact up_mem_faces hQ

theorem res_neg (γ : E₀) : res φ (-γ) = -res φ γ := map_neg _ _

/-- The restrictions of the roots of a Levi component are the roots of the restricted Levi
component. -/
theorem restrictRoots_leviRoots (hR₀ : ∀ γ ∈ R₀, -γ ∈ R₀) (Q : Finset E) :
    restrictRoots φ (leviRoots R₀ (up φ R₀ Q)) = leviRoots (restrictRoots φ R₀) Q := by
  ext α
  simp only [mem_restrictRoots, leviRoots, Finset.mem_filter, mem_up, not_and]
  constructor
  · rintro ⟨h0, γ, ⟨hγ, h1, h2⟩, rfl⟩
    refine ⟨⟨h0, γ, hγ, rfl⟩, h1 hγ, fun h => h2 (hR₀ γ hγ) ?_⟩
    rwa [res_neg]
  · rintro ⟨⟨h0, γ, hγ, rfl⟩, h1, h2⟩
    refine ⟨h0, γ, ⟨hγ, fun _ => h1, fun _ h => h2 ?_⟩, rfl⟩
    rwa [res_neg] at h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem mem_iInf_orthogonal_iff {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (S : Finset F) (x : F) : x ∈ ⨅ α ∈ S, (ℝ ∙ α)ᗮ ↔ ∀ α ∈ S, ⟪α, x⟫ = 0 := by
  simp only [Submodule.mem_iInf, Submodule.mem_orthogonal_singleton_iff_inner_right]

theorem map_mem_iInf_orthogonal_iff (S₀ : Finset E₀) (x : E) :
    φ x ∈ ⨅ γ ∈ S₀, (ℝ ∙ γ)ᗮ ↔ x ∈ ⨅ α ∈ restrictRoots φ S₀, (ℝ ∙ α)ᗮ := by
  rw [mem_iInf_orthogonal_iff, mem_iInf_orthogonal_iff]
  constructor
  · intro H α hα
    obtain ⟨-, γ, hγ, rfl⟩ := mem_restrictRoots.mp hα
    rw [inner_res]
    exact H γ hγ
  · intro H γ hγ
    rw [← inner_res]
    by_cases h0 : res φ γ = 0
    · rw [h0, inner_zero_left]
    · exact H _ (mem_restrictRoots.mpr ⟨h0, γ, hγ, rfl⟩)

theorem mapSub_inf_iInf (V : Submodule ℝ E) (S₀ : Finset E₀) :
    mapSub (φ := φ) V ⊓ ⨅ γ ∈ S₀, (ℝ ∙ γ)ᗮ =
      mapSub (φ := φ) (V ⊓ ⨅ α ∈ restrictRoots φ S₀, (ℝ ∙ α)ᗮ) := by
  ext x₀
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    exact ⟨x, ⟨hx, (map_mem_iInf_orthogonal_iff S₀ x).mp h⟩, rfl⟩
  · rintro ⟨x, ⟨hx, h⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (map_mem_iInf_orthogonal_iff S₀ x).mpr h⟩

theorem faceSpace_up (hR₀ : ∀ γ ∈ R₀, -γ ∈ R₀) (V : Submodule ℝ E) (Q : Finset E) :
    faceSpace R₀ (mapSub (φ := φ) V) (up φ R₀ Q) =
      mapSub (φ := φ) (faceSpace (restrictRoots φ R₀) V Q) := by
  rw [faceSpace, mapSub_inf_iInf, restrictRoots_leviRoots hR₀, faceSpace]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem mapSub_injective : Function.Injective (mapSub (φ := φ)) :=
  Submodule.map_injective_of_injective φ.injective

theorem leviSpaces_mapSub (hR₀ : ∀ γ ∈ R₀, -γ ∈ R₀) (V : Submodule ℝ E) :
    leviSpaces R₀ (mapSub (φ := φ) V) =
      (leviSpaces (restrictRoots φ R₀) V).image (mapSub (φ := φ)) := by
  rw [leviSpaces, leviSpaces, faces_mapSub, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro Q _
  exact faceSpace_up hR₀ V Q

theorem sum_leviSpaces_mapSub {M : Type*} [AddCommMonoid M] (hR₀ : ∀ γ ∈ R₀, -γ ∈ R₀)
    (V : Submodule ℝ E) (F : Submodule ℝ E₀ → M) :
    ∑ L₀ ∈ leviSpaces R₀ (mapSub (φ := φ) V), F L₀ =
      ∑ L ∈ leviSpaces (restrictRoots φ R₀) V, F (mapSub (φ := φ) L) := by
  rw [leviSpaces_mapSub hR₀, Finset.sum_image (fun L _ L' _ h => mapSub_injective h)]

/-- The relative supplementary function of a pushed family. -/
theorem cQM_pushFam (hR₀ : ∀ γ ∈ R₀, -γ ∈ R₀) (V : Submodule ℝ E)
    (c : Finset E → StrongDual ℝ V → ℂ) {Q : Finset E} (hQ : Q ∈ faces (restrictRoots φ R₀) V)
    (Λ₀ : StrongDual ℝ (mapSub (φ := φ) V)) :
    cQM R₀ (mapSub (φ := φ) V) (pushFam φ V c) (up φ R₀ Q) Λ₀ =
      cQM (restrictRoots φ R₀) V c Q (pullParam V Λ₀) := by
  have hl := restrictRoots_leviRoots (φ := φ) hR₀ Q
  unfold cQM
  rw [sum_parabolics_mapSub (R₀ := leviRoots R₀ (up φ R₀ Q)), hl]
  apply Finset.sum_congr rfl
  intro S hS
  have hS' : S ∈ parabolics (restrictRoots φ (leviRoots R₀ (up φ R₀ Q))) V := hl ▸ hS
  rw [theta_up (parabolics_subset_restrictRoots hS'), pushFam, down, Finset.image_union]
  change c (down (φ := φ) (up φ R₀ Q) ∪ down (φ := φ) (up φ (leviRoots R₀ (up φ R₀ Q)) S)) _ * _ = _
  rw [down_up_of_faces hQ, down_up hS']

/-! ### Volumes -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem mem_orthogonal_mapSub_iff {V : Submodule ℝ E} {x : E} :
    φ x ∈ (mapSub (φ := φ) V)ᗮ ↔ x ∈ Vᗮ := by
  simp only [Submodule.mem_orthogonal]
  constructor
  · intro H u hu
    have h := H (φ u) ⟨u, hu, rfl⟩
    rwa [LinearIsometry.inner_map_map] at h
  · rintro H _ ⟨u, hu, rfl⟩
    change ⟪φ u, φ x⟫ = 0
    rw [LinearIsometry.inner_map_map]
    exact H u hu

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem mapSub_inf_orthogonal (W V : Submodule ℝ E) :
    mapSub (φ := φ) W ⊓ (mapSub (φ := φ) V)ᗮ = mapSub (φ := φ) (W ⊓ Vᗮ) := by
  ext x₀
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    exact ⟨x, ⟨hx, mem_orthogonal_mapSub_iff.mp h⟩, rfl⟩
  · rintro ⟨x, ⟨hx, h⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, mem_orthogonal_mapSub_iff.mpr h⟩

variable (φ) in
/-- A subspace and its image, as an isometry. -/
def mapIsometry (V : Submodule ℝ E) : V ≃ₗᵢ[ℝ] mapSub (φ := φ) V :=
  (mapEquiv (φ := φ) V).isometryOfInner (inner_mapEquiv V)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem gramVolume_sum_swap {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (u : ι → F) (w : κ → F) :
    gramVolume (Sum.elim u w) = gramVolume (Sum.elim w u) := by
  rw [← gramVolume_reindex (Equiv.sumComm ι κ) (Sum.elim w u)]
  congr 1
  funext i
  rcases i with i | i <;> rfl

theorem gramVolume_join_indep {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ]
    (U : Submodule ℝ F) (b : OrthonormalBasis ι ℝ U) (b' : OrthonormalBasis ι' ℝ U)
    (w : κ → F) :
    gramVolume (Sum.elim (fun i => (b i : F)) w) = gramVolume (Sum.elim (fun i => (b' i : F)) w) := by
  rw [gramVolume_join_orthogonalProjection, gramVolume_join_orthogonalProjection]

/-- The volume factor of images of subspaces. -/
theorem measureFactor_mapSub (U W V : Submodule ℝ E) :
    measureFactor (mapSub (φ := φ) U) (mapSub (φ := φ) W) (mapSub (φ := φ) V) =
      measureFactor U W V := by
  unfold measureFactor
  have hU := (mapEquiv (φ := φ) U).finrank_eq
  have hW := (mapEquiv (φ := φ) W).finrank_eq
  have hV := (mapEquiv (φ := φ) V).finrank_eq
  by_cases h : Module.finrank ℝ U + Module.finrank ℝ W = Module.finrank ℝ V
  · rw [ite_eq_left h, ite_eq_left (by rw [← hU, ← hW, ← hV]; exact h)]
    let bU := (stdOrthonormalBasis ℝ U).map (mapIsometry φ U)
    let bW := (stdOrthonormalBasis ℝ W).map (mapIsometry φ W)
    rw [gramVolume_join_indep _ _ bU, gramVolume_sum_swap, gramVolume_join_indep _ _ bW,
      gramVolume_sum_swap, ← gramVolume_map (φ := φ)]
    congr 1
    funext i
    rcases i with i | i <;> rfl
  · rw [ite_eq_right h, ite_eq_right (by rw [← hU, ← hW, ← hV]; exact h)]

theorem dDescent_mapSub (a z a₁ L : Submodule ℝ E) :
    dDescent (mapSub (φ := φ) a) (mapSub (φ := φ) z) (mapSub (φ := φ) a₁) (mapSub (φ := φ) L) =
      dDescent a z a₁ L := by
  rw [dDescent, mapSub_inf_orthogonal, mapSub_inf_orthogonal, mapSub_inf_orthogonal,
    measureFactor_mapSub, dDescent]

/-! ### Parameters and sections -/

theorem extendParam_pushParam {V W : Submodule ℝ E} (Λ : StrongDual ℝ V) :
    extendParam (mapSub (φ := φ) V) (mapSub (φ := φ) W) (pushParam V Λ) =
      pushParam W (extendParam V W Λ) := by
  ext ⟨_, w, hw, rfl⟩
  change Λ ((mapEquiv (φ := φ) V).symm (restrictedRoot (mapSub (φ := φ) V) (φ w))) =
    Λ (restrictedRoot V (((mapEquiv (φ := φ) W).symm ⟨φ w, w, hw, rfl⟩ : W) : E))
  rw [restrictedRoot_mapSub, LinearEquiv.symm_apply_apply, res_apply_self]
  congr 2
  change w = res φ (φ w)
  rw [res_apply_self]

theorem descentSection_mapSub {a z a₁ L : Submodule ℝ E} (hza : z ≤ a) (haa₁ : a ≤ a₁)
    (hzL : z ≤ L) (hLa₁ : L ≤ a₁) (hd : dDescent a z a₁ L ≠ 0) {ξ : E} (hξ : ξ ∈ a₁ ⊓ aᗮ) :
    descentSection R₀ (mapSub (φ := φ) a) (mapSub (φ := φ) z) (φ ξ) (mapSub (φ := φ) L) =
      up φ R₀ (descentSection (restrictRoots φ R₀) a z ξ L) := by
  obtain ⟨p, ⟨hpL, hpA⟩, -⟩ := existsUnique_descentPoint hza haa₁ hzL hLa₁ hd hξ
  rw [descentSection_eq_posSet hza haa₁ hzL hLa₁ hd hξ hpL hpA, up_posSet]
  have hmono {X Y : Submodule ℝ E} (h : X ≤ Y) : mapSub (φ := φ) X ≤ mapSub (φ := φ) Y :=
    Submodule.map_mono h
  apply descentSection_eq_posSet (hmono hza) (hmono haa₁) (hmono hzL) (hmono hLa₁)
    (by rwa [dDescent_mapSub])
  · rw [mapSub_inf_orthogonal]
    exact ⟨ξ, hξ, rfl⟩
  · rw [mapSub_inf_orthogonal]
    exact ⟨p, hpL, rfl⟩
  · rw [mapSub_inf_orthogonal]
    exact ⟨p - ξ, hpA, by simp⟩

end RootRestriction

end Langlands.GMFamily
