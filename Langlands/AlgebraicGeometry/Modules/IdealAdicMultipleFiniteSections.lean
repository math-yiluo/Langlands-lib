import Langlands.AlgebraicGeometry.Modules.IdealAdicMultipleSectionImage
import Mathlib.LinearAlgebra.Pi

/-! # Ideal multiples in finite families of affine sections -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

private lemma mem_ideal_smul_top_pi_iff {A : Type u} [CommRing A]
    {ι : Type v} [Fintype ι] {V : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
    (J : Ideal A) (x : ∀ i, V i) :
    x ∈ J • (⊤ : Submodule A (∀ i, V i)) ↔
      ∀ i, x i ∈ J • (⊤ : Submodule A (V i)) := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      exact Submodule.smul_mem_smul hr (Submodule.mem_top)
    · intro y z hy hz
      exact add_mem hy hz
  · intro hx
    classical
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i hi
    refine Submodule.smul_induction_on (hx i) ?_ ?_
    · intro r hr m hm
      change (LinearMap.single A V i) (r • m) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem_smul hr (Submodule.mem_top)
    · intro y z hy hz
      change (LinearMap.single A V i) (y + z) ∈ _
      rw [map_add]
      exact add_mem hy hz

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (M : X.Modules) {ι : Type v} (U : ι → X.Opens)

/-- The product of the actual ideal-multiple inclusion maps over a family of opens. -/
def inclusionFamilySections :
    (∀ i, (OModulePresheaf.ofModules f (multiple f J M)).obj (U i)) →ₗ[R]
      (∀ i, (OModulePresheaf.ofModules f M).obj (U i)) :=
  LinearMap.pi fun i => (inclusionSections f J M (U i)).comp (LinearMap.proj i)

@[simp]
lemma inclusionFamilySections_apply
    (x : ∀ i, (OModulePresheaf.ofModules f (multiple f J M)).obj (U i)) (i : ι) :
    inclusionFamilySections f J M U x i = (inclusion f J M).app (U i) (x i) := rfl

/-- The product inclusion is injective, with no restriction on the family of opens. -/
lemma inclusionFamilySections_injective :
    Function.Injective (inclusionFamilySections f J M U) := by
  intro x y h
  funext i
  exact inclusion_app_injective f J M (U i) (congrFun h i)

/-- A family lifts to the actual ideal multiple exactly when every affine component
is an ideal multiple for the base-ring action. -/
lemma mem_range_inclusionFamilySections_iff [M.IsQuasicoherent] (hJ : J.FG)
    (hU : ∀ i, IsAffineOpen (U i))
    (x : ∀ i, (OModulePresheaf.ofModules f M).obj (U i)) :
    x ∈ LinearMap.range (inclusionFamilySections f J M U) ↔
      ∀ i, x i ∈ J • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).obj (U i))) := by
  constructor
  · rintro ⟨y, rfl⟩ i
    rw [← range_inclusionSections f J M hJ (hU i)]
    exact ⟨y i, rfl⟩
  · intro hx
    have hy : ∀ i, ∃ y, inclusionSections f J M (U i) y = x i := by
      intro i
      have hi : x i ∈ LinearMap.range (inclusionSections f J M (U i)) := by
        rw [range_inclusionSections f J M hJ (hU i)]
        exact hx i
      exact hi
    choose y hy using hy
    exact ⟨y, funext hy⟩

/-- For a finite family of affine opens, the product inclusion has exactly
`J` times the full product of sections as its range. -/
lemma range_inclusionFamilySections [Fintype ι] [M.IsQuasicoherent] (hJ : J.FG)
    (hU : ∀ i, IsAffineOpen (U i)) :
    LinearMap.range (inclusionFamilySections f J M U) =
      J • (⊤ : Submodule R (∀ i, (OModulePresheaf.ofModules f M).obj (U i))) := by
  ext x
  exact (mem_range_inclusionFamilySections_iff f J M U hJ hU x).trans
    (mem_ideal_smul_top_pi_iff J x).symm

end Langlands.AlgebraicGeometry.Modules.IdealAdic
