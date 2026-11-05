import Langlands.AlgebraicGeometry.Modules.CechResolution.Naturality
import Langlands.AlgebraicGeometry.Modules.IdealAdicMultipleFiniteSections
import Langlands.AlgebraicGeometry.Modules.ProperAdicCohomologyStableImageReduction
import Mathlib.RingTheory.Noetherian.Defs

/-! # From ambient Čech boundary lifts to actual adic cohomology kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

open CechResolution

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (M : X.Modules) (𝒰 : X.OrderedAffineCover)

/-- Every ambient boundary in `I` times cochains has a primitive in `J` times cochains. -/
def CechBoundaryLift (I J : Ideal R) (p : ℕ) : Prop :=
  ∀ y : (OModulePresheaf.ofModules f M).cochain 𝒰 p,
    (OModulePresheaf.ofModules f M).d 𝒰 p y ∈
        I • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).cochain 𝒰 (p + 1))) →
      ∃ y' ∈ J • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).cochain 𝒰 p)),
        (OModulePresheaf.ofModules f M).d 𝒰 p y' =
          (OModulePresheaf.ofModules f M).d 𝒰 p y

/-- The inclusion on Čech cochains is the product of the actual section inclusions. -/
lemma cochainMap_inclusion_eq (J : Ideal R) (p : ℕ) :
    cochainMap f (inclusion f J M) 𝒰 p =
      inclusionFamilySections f J M (fun s : 𝒰.Idx p => 𝒰.inter s) := by
  ext x s
  rfl

/-- The actual inclusion is injective on Čech cochains. -/
lemma cochainMap_inclusion_injective (J : Ideal R) (p : ℕ) :
    Function.Injective (cochainMap f (inclusion f J M) 𝒰 p) := by
  rw [cochainMap_inclusion_eq]
  exact inclusionFamilySections_injective f J M _

/-- On a separated scheme, the inclusion on a finite affine Čech term has
range equal to the ideal multiple of the ambient cochains. -/
lemma range_cochainMap_inclusion [IsSeparated f] [M.IsQuasicoherent]
    (J : Ideal R) (hJ : J.FG) (p : ℕ) :
    LinearMap.range (cochainMap f (inclusion f J M) 𝒰 p) =
      J • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).cochain 𝒰 p)) := by
  rw [cochainMap_inclusion_eq]
  exact range_inclusionFamilySections f J M _ hJ
    (fun s => 𝒰.isAffineOpen_inter f s)

/-- A boundary lift in the ambient Čech complex gives the corresponding
kernel containment for the actual ideal-multiple sheaves. -/
lemma ker_inclusion_le_of_cech_boundary_lift [IsSeparated f] [M.IsQuasicoherent]
    {I J : Ideal R} (h : I ≤ J) (hI : I.FG) (hJ : J.FG) (p : ℕ)
    (hbound : CechBoundaryLift f M 𝒰 I J p) :
    LinearMap.ker
        ((DerivedSections.relativeCohomology f (p + 1)).map (inclusion f I M)).hom ≤
      LinearMap.ker
        ((DerivedSections.relativeCohomology f (p + 1)).map (multipleMap f h M)).hom := by
  let := isQuasicoherent_multiple f I M hI
  let := isQuasicoherent_multiple f J M hJ
  apply ker_relativeCohomology_map_le f 𝒰 (inclusion f I M) (multipleMap f h M) p
  intro z _ hz
  obtain ⟨y, hy⟩ := hz
  have hdy : (OModulePresheaf.ofModules f M).d 𝒰 p y ∈
      I • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).cochain 𝒰 (p + 1))) := by
    rw [hy, ← range_cochainMap_inclusion f M 𝒰 I hI (p + 1)]
    exact ⟨z, rfl⟩
  obtain ⟨y', hy'mem, hy'eq⟩ := hbound y hdy
  have hy'lift : y' ∈ LinearMap.range (cochainMap f (inclusion f J M) 𝒰 p) := by
    rw [range_cochainMap_inclusion f M 𝒰 J hJ p]
    exact hy'mem
  obtain ⟨w, hw⟩ := hy'lift
  refine ⟨w, cochainMap_inclusion_injective f M 𝒰 J (p + 1) ?_⟩
  calc
    cochainMap f (inclusion f J M) 𝒰 (p + 1)
        ((OModulePresheaf.ofModules f (multiple f J M)).d 𝒰 p w) =
        (OModulePresheaf.ofModules f M).d 𝒰 p
          (cochainMap f (inclusion f J M) 𝒰 p w) :=
      congrArg (fun g => g w) (cochainMap_comp_d f (inclusion f J M) 𝒰 p)
    _ = (OModulePresheaf.ofModules f M).d 𝒰 p y' := congrArg _ hw
    _ = (OModulePresheaf.ofModules f M).d 𝒰 p y := hy'eq
    _ = cochainMap f (inclusion f I M) 𝒰 (p + 1) z := hy
    _ = cochainMap f (inclusion f J M) 𝒰 (p + 1)
        (cochainMap f (multipleMap f h M) 𝒰 (p + 1) z) := by
      funext s
      change (inclusion f I M).app (𝒰.inter s) (z s) =
        (inclusion f J M).app (𝒰.inter s) ((multipleMap f h M).app (𝒰.inter s) (z s))
      exact (congrArg (fun g : multiple f I M ⟶ M =>
        g.app (𝒰.inter s) (show Γ(multiple f I M, 𝒰.inter s) from z s))
          (multipleMap_inclusion f h M)).symm

/-- A uniform ambient boundary-lifting bound implies stable images of the
actual adic quotient cohomology, with the same bound. -/
lemma adic_stable_image_of_cech_boundary_lift [IsNoetherianRing R] [IsSeparated f]
    [M.IsQuasicoherent] (I : Ideal R) (p c : ℕ)
    (hc : ∀ n k : ℕ, n + c ≤ k →
      CechBoundaryLift f M 𝒰 (I ^ k) (I ^ n) p) :
    ∀ n k : ℕ, ∀ h : n + c ≤ k,
      LinearMap.range
          ((DerivedSections.relativeCohomology f p).map
            (adicTransition f I M (Nat.le_trans (Nat.le_add_right n c) h))).hom =
        LinearMap.range
          ((DerivedSections.relativeCohomology f p).map (adicProjection f I M n)).hom := by
  apply adic_cohomology_stable_image_of_ker_le f I M p c
  intro n k h
  exact ker_inclusion_le_of_cech_boundary_lift f M 𝒰
    (Ideal.pow_le_pow_right (Nat.le_trans (Nat.le_add_right n c) h))
    (I ^ k).fg_of_isNoetherianRing (I ^ n).fg_of_isNoetherianRing p (hc n k h)

end Langlands.AlgebraicGeometry.Modules.IdealAdic
