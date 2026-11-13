import Langlands.Geometry.Building.GaloisApartmentQuotientAction
import Langlands.Geometry.Building.AffineFacetTransport

/-! # Coefficient transport preserves the actual affine roots -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hD : GaloisStable k K i D)

/-- Inverse precomposition by the actual coefficient affine action. -/
def galoisAffineFunctional (σ : K ≃ₐ[k] K) :
    (D.Apartment →ᵃ[ℝ] ℝ) ≃ₗ[ℝ] (D.Apartment →ᵃ[ℝ] ℝ) :=
  AffineRootSystem.affineFunctionalTransport (galoisAffineAction k K i D hD σ)

@[simp] theorem galoisAffineFunctional_apply_map (σ : K ≃ₐ[k] K)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (x : D.Apartment) :
    galoisAffineFunctional k K i D hD σ ψ (galoisAction k K i D hD σ x) = ψ x :=
  congrArg ψ ((galoisAffineAction k K i D hD σ).symm_apply_apply x)

/-- The derivative follows the actual Galois action on relative roots. -/
theorem galoisAffineFunctional_linear_eq_rootForm_iff (σ : K ≃ₐ[k] K)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (a : relativeRoots (T := T_K) i_K) :
    (galoisAffineFunctional k K i D hD σ ψ).linear =
        rootForm (S := T_K) i_K (galoisRootAction k K i σ a) ↔
      ψ.linear = rootForm (S := T_K) i_K a := by
  have heval (v : TranslationSpace (S := T_K) i_K) :
      (galoisAffineFunctional k K i D hD σ ψ).linear
          (galoisTranslationAction k K i σ v) = ψ.linear v :=
    congrArg ψ.linear ((galoisTranslationAction k K i σ).symm_apply_apply v)
  constructor
  · intro hψ
    apply LinearMap.ext
    intro v
    rw [← heval, hψ, rootForm_galoisTranslationAction]
  · intro hψ
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := (galoisTranslationAction k K i σ).surjective v
    rw [heval, hψ, rootForm_galoisTranslationAction]

/-- Coefficient conjugation preserves all affine root groups. -/
theorem rationalConjugate_mem_affineRootGroup_iff (σ : K ≃ₐ[k] K)
    (a : characterLattice T_K) (ψ : D.Apartment →ᵃ[ℝ] ℝ) (g : rationalPoints G_K) :
    rationalConjugate k K G σ g ∈
        D.affineRootGroup (characterLattice.galoisRepresentation k K T σ a)
          (galoisAffineFunctional k K i D hD σ ψ) ↔
      g ∈ D.affineRootGroup a ψ := by
  simp only [affineRootGroup, Subgroup.mem_iInf]
  constructor
  · intro hg x
    have hx := hg (galoisAction k K i D hD σ x)
    rw [galoisAffineFunctional_apply_map] at hx
    exact (rationalConjugate_mem_filtration_iff k K i D hD σ x a (ψ x) g).mp hx
  · intro hg y
    obtain ⟨x, rfl⟩ := (galoisAction k K i D hD σ).surjective y
    rw [galoisAffineFunctional_apply_map]
    exact (rationalConjugate_mem_filtration_iff k K i D hD σ x a (ψ x) g).mpr (hg x)

theorem map_affineRootGroup_galois (σ : K ≃ₐ[k] K)
    (a : characterLattice T_K) (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (D.affineRootGroup a ψ).map (rationalConjugate k K G σ).toMonoidHom =
      D.affineRootGroup (characterLattice.galoisRepresentation k K T σ a)
        (galoisAffineFunctional k K i D hD σ ψ) := by
  ext y
  obtain ⟨g, rfl⟩ := (rationalConjugate k K G σ).surjective y
  exact (Subgroup.mem_map_iff_mem
    (f := (rationalConjugate k K G σ).toMonoidHom)
    (rationalConjugate k K G σ).injective).trans
      (rationalConjugate_mem_affineRootGroup_iff k K i D hD σ a ψ g).symm

theorem galoisAffineFunctional_add_const (σ : K ≃ₐ[k] K)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (c : ℝ) :
    galoisAffineFunctional k K i D hD σ (ψ + AffineMap.const ℝ D.Apartment c) =
      galoisAffineFunctional k K i D hD σ ψ + AffineMap.const ℝ D.Apartment c := by
  ext y
  rfl

/-- Strict root groups also follow the same coefficient conjugation. -/
theorem rationalConjugate_mem_affineRootGroupPlus_iff (σ : K ≃ₐ[k] K)
    (a : characterLattice T_K) (ψ : D.Apartment →ᵃ[ℝ] ℝ) (g : rationalPoints G_K) :
    rationalConjugate k K G σ g ∈
        D.affineRootGroupPlus (characterLattice.galoisRepresentation k K T σ a)
          (galoisAffineFunctional k K i D hD σ ψ) ↔
      g ∈ D.affineRootGroupPlus a ψ := by
  rw [mem_affineRootGroupPlus, mem_affineRootGroupPlus]
  constructor
  · rintro ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    rw [← galoisAffineFunctional_add_const] at hg
    exact (rationalConjugate_mem_affineRootGroup_iff k K i D hD σ a _ g).mp hg
  · rintro ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    rw [← galoisAffineFunctional_add_const]
    exact (rationalConjugate_mem_affineRootGroup_iff k K i D hD σ a _ g).mpr hg

theorem map_affineRootGroupPlus_galois (σ : K ≃ₐ[k] K)
    (a : characterLattice T_K) (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (D.affineRootGroupPlus a ψ).map (rationalConjugate k K G σ).toMonoidHom =
      D.affineRootGroupPlus (characterLattice.galoisRepresentation k K T σ a)
        (galoisAffineFunctional k K i D hD σ ψ) := by
  ext y
  obtain ⟨g, rfl⟩ := (rationalConjugate k K G σ).surjective y
  exact (Subgroup.mem_map_iff_mem
    (f := (rationalConjugate k K G σ).toMonoidHom)
    (rationalConjugate k K G σ).injective).trans
      (rationalConjugate_mem_affineRootGroupPlus_iff k K i D hD σ a ψ g).symm

omit [IsAffineHom G.X.hom]
  [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] in
/-- Coefficient conjugation maps each actual root subgroup onto its transport. -/
theorem map_rootGroupPoints_galois (σ : K ≃ₐ[k] K) (a : characterLattice T_K) :
    (rootGroupPoints (S := T_K) i_K a).map
        (rationalConjugate k K G σ).toMonoidHom =
      rootGroupPoints (S := T_K) i_K
        (characterLattice.galoisRepresentation k K T σ a) := by
  apply Subgroup.ext
  intro y
  obtain ⟨g, rfl⟩ := (rationalConjugate k K G σ).surjective y
  exact (Subgroup.mem_map_iff_mem
    (f := (rationalConjugate k K G σ).toMonoidHom)
    (rationalConjugate k K G σ).injective).trans
      (RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ a g).symm

omit [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] in
/-- The missing-double-root convention is respected as well. -/
theorem map_doubleRootGroupPoints_galois (σ : K ≃ₐ[k] K) (a : characterLattice T_K) :
    (doubleRootGroupPoints (S := T_K) i_K a).map
        (rationalConjugate k K G σ).toMonoidHom =
      doubleRootGroupPoints (S := T_K) i_K
        (characterLattice.galoisRepresentation k K T σ a) := by
  classical
  have h2 : 2 • characterLattice.galoisRepresentation k K T σ a ∈
        relativeRoots (T := T_K) i_K ↔ 2 • a ∈ relativeRoots (T := T_K) i_K := by
    rw [← map_nsmul]
    exact mem_roots_galois_iff k K i σ (2 • a)
  by_cases ha : 2 • a ∈ relativeRoots (T := T_K) i_K
  · rw [doubleRootGroupPoints, ite_eq_left ha, doubleRootGroupPoints,
      ite_eq_left (h2.mpr ha)]
    exact (map_rootGroupPoints_galois k K i σ (2 • a)).trans
      (congrArg (rootGroupPoints (S := T_K) i_K)
        (map_nsmul (characterLattice.galoisRepresentation k K T σ) 2 a))
  · rw [doubleRootGroupPoints, ite_eq_right ha, doubleRootGroupPoints,
      ite_eq_right (fun hroot => ha (h2.mp hroot)), Subgroup.map_bot]

/-- The actual noncontainment test for an ordinary affine root is invariant. -/
theorem affineRootGroup_subset_mul_galois_iff (σ : K ≃ₐ[k] K)
    (a : characterLattice T_K) (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (D.affineRootGroup (characterLattice.galoisRepresentation k K T σ a)
        (galoisAffineFunctional k K i D hD σ ψ) : Set (rationalPoints G_K)) ⊆
      (D.affineRootGroupPlus (characterLattice.galoisRepresentation k K T σ a)
        (galoisAffineFunctional k K i D hD σ ψ) : Set (rationalPoints G_K)) *
        (doubleRootGroupPoints (S := T_K) i_K
          (characterLattice.galoisRepresentation k K T σ a) : Set (rationalPoints G_K)) ↔
    (D.affineRootGroup a ψ : Set (rationalPoints G_K)) ⊆
      (D.affineRootGroupPlus a ψ : Set (rationalPoints G_K)) *
        (doubleRootGroupPoints (S := T_K) i_K a : Set (rationalPoints G_K)) := by
  conv_rhs =>
    rw [← Set.image_subset_image_iff (rationalConjugate k K G σ).injective, Set.image_mul]
  change _ ↔
    ((D.affineRootGroup a ψ).map (rationalConjugate k K G σ).toMonoidHom :
        Set (rationalPoints G_K)) ⊆
      ((D.affineRootGroupPlus a ψ).map (rationalConjugate k K G σ).toMonoidHom :
        Set (rationalPoints G_K)) *
        ((doubleRootGroupPoints (S := T_K) i_K a).map
          (rationalConjugate k K G σ).toMonoidHom : Set (rationalPoints G_K))
  rw [map_affineRootGroup_galois, map_affineRootGroupPlus_galois,
    map_doubleRootGroupPoints_galois]

/-- Ordinary affine roots are preserved and reflected, including multipliable roots. -/
theorem galoisAffineFunctional_mem_affineRoots_iff (σ : K ≃ₐ[k] K)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    galoisAffineFunctional k K i D hD σ ψ ∈ D.affineRoots ↔ ψ ∈ D.affineRoots := by
  constructor
  · rintro ⟨a', hψ, hnot⟩
    obtain ⟨a, rfl⟩ := (galoisRootAction k K i σ).surjective a'
    refine ⟨a, (galoisAffineFunctional_linear_eq_rootForm_iff k K i D hD σ ψ a).mp hψ,
      fun hs => hnot ((affineRootGroup_subset_mul_galois_iff k K i D hD σ a ψ).mpr hs)⟩
  · rintro ⟨a, hψ, hnot⟩
    refine ⟨galoisRootAction k K i σ a,
      (galoisAffineFunctional_linear_eq_rootForm_iff k K i D hD σ ψ a).mpr hψ,
      fun hs => hnot ((affineRootGroup_subset_mul_galois_iff k K i D hD σ a ψ).mp hs)⟩

/-- The full actual affine-root set maps onto itself. -/
theorem transportedRoots_galoisAffineAction (σ : K ≃ₐ[k] K) :
    AffineRootSystem.transportedRoots (galoisAffineAction k K i D hD σ) D.affineRoots =
      D.affineRoots := by
  ext ψ
  constructor
  · rintro ⟨phi, hphi, rfl⟩
    exact (galoisAffineFunctional_mem_affineRoots_iff k K i D hD σ phi).mpr hphi
  · intro hψ
    obtain ⟨phi, rfl⟩ := (galoisAffineFunctional k K i D hD σ).surjective ψ
    exact ⟨phi, (galoisAffineFunctional_mem_affineRoots_iff k K i D hD σ phi).mp hψ, rfl⟩

/-- The actual coefficient affine action preserves the entire ordinary-root arrangement. -/
def GaloisAffineRootStabilityStatement : Prop :=
  ∀ σ : K ≃ₐ[k] K,
    AffineRootSystem.transportedRoots (galoisAffineAction k K i D hD σ) D.affineRoots =
      D.affineRoots

theorem galoisAffineRootStability : GaloisAffineRootStabilityStatement k K i D hD :=
  transportedRoots_galoisAffineAction k K i D hD

end Langlands.Geometry.Building.KPApartmentData
