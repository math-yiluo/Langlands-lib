import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCreation
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqRefine

/-! # Naturality and refinement of positive-degree creation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.Cohomology.Cech

section Pull

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {I J : Type u}
  (U : I → X.Opens) (V : J → Y.Opens) (α : J → I)
  (hα : ∀ j, V j ≤ f ⁻¹ᵁ U (α j))

/-- Pullback preserves cup product by a one-cochain in every degree. -/
lemma pull_cup₁_all {q : ℕ} (z : C (ab X.presheaf) U 1)
    (b : C (ab X.presheaf) U q) :
    pull f U V α hα (q + 1) (cup₁ X.presheaf U z b) =
      cup₁ Y.presheaf V (pull f U V α hα 1 z) (pull f U V α hα q b) := by
  funext τ
  rw [pull_apply, cup₁_apply, cup₁_apply, map_mul, face_pull, face_pull]

end Pull

section Refine

variable {X : Scheme.{u}} {I J : Type u} (U : I → X.Opens)
  (V : J → X.Opens) (β : J → I) (hβ : ∀ j, V j ≤ U (β j))

/-- Refinement preserves cup product by a one-cochain in every degree. -/
lemma refine_cup₁_all {q : ℕ} (z : C (ab X.presheaf) U 1)
    (b : C (ab X.presheaf) U q) :
    refine (ab X.presheaf) U V β hβ (q + 1) (cup₁ X.presheaf U z b) =
      cup₁ X.presheaf V (refine (ab X.presheaf) U V β hβ 1 z)
        (refine (ab X.presheaf) U V β hβ q b) := by
  funext τ
  rw [refine_apply, cup₁_apply, cup₁_apply, res_mul, face_refine, face_refine]

end Refine

end Langlands.Cohomology.Cech

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech DerivedSections

section Pull

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)} (h : Y ⟶ X)
  {I J : Type u} [Fintype I] [Fintype J] (U : I → X.left.Opens)
  (V : J → Y.left.Opens) (α : J → I)
  (hα : ∀ j, V j ≤ h.left ⁻¹ᵁ U (α j))

/-- Canonical pullback of structure-sheaf cohomology, with the pullback-unit comparison. -/
def unitCohomologyPullback (n : ℕ) :
    (relativeCohomology X.hom n).obj (unitModule X.left) ⟶
      (relativeCohomology Y.hom n).obj (unitModule Y.left) :=
  relativeCohomologyPullback h (unitModule X.left) n ≫
    (relativeCohomology Y.hom n).map
      (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom

lemma unitCochainMap_cup_all {q : ℕ} (z : cochain X.hom U (unitModule X.left) 1)
    (b : cochain X.hom U (unitModule X.left) q) :
    (unitCochainMap h U V α hα).f (q + 1) (cup X.hom U z b) =
      cup Y.hom V ((unitCochainMap h U V α hα).f 1 z)
        ((unitCochainMap h U V α hα).f q b) := by
  rw [unitCochainMap_eq_pull]
  change pull h.left U V α hα (q + 1) (cup₁ X.left.presheaf U z b) =
    cup₁ Y.left.presheaf V ((unitCochainMap h U V α hα).f 1 z)
      ((unitCochainMap h U V α hα).f q b)
  rw [unitCochainMap_eq_pull, unitCochainMap_eq_pull, pull_cup₁_all]

/-- Pullback commutes with creation on positive-degree ordered Čech cohomology. -/
lemma homologyMap_creationH (n : ℕ)
    (x : (cochainComplex X.hom U (unitModule X.left)).homology 1)
    (y : (cochainComplex X.hom U (unitModule X.left)).homology (n + 1)) :
    HomologicalComplex.homologyMap (unitCochainMap h U V α hα) (n + 2)
        (creationH X.hom U (n + 1) x y) =
      creationH Y.hom V (n + 1)
        (HomologicalComplex.homologyMap (unitCochainMap h U V α hα) 1 x)
        (HomologicalComplex.homologyMap (unitCochainMap h U V α hα) (n + 1) y) := by
  obtain ⟨z, rfl⟩ := classMap_surjective X.hom U (unitModule X.left) 0 x
  obtain ⟨b, rfl⟩ := classMap_surjective X.hom U (unitModule X.left) n y
  rw [creationH_classMap_classMap,
    homologyMap_classMap _ (n + 1) _ (chainMap_mem_ker U V _ (n + 1) _),
    homologyMap_classMap _ 0 _ (chainMap_mem_ker U V _ 0 z),
    homologyMap_classMap _ n _ (chainMap_mem_ker U V _ n b),
    creationH_classMap_classMap]
  congr 1
  apply Subtype.ext
  exact unitCochainMap_cup_all h U V α hα
    (z : cochain X.hom U (unitModule X.left) 1)
    (b : cochain X.hom U (unitModule X.left) (n + 1))

variable [IsSeparated X.hom] [IsSeparated Y.hom]
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤)
  (hUa : ∀ i, IsAffineOpen (U i)) (hVa : ∀ j, IsAffineOpen (V j))

include α hα in
/-- The actual structure-sheaf pullback commutes with creation in each positive degree. -/
theorem pull_creationCanonical (n : ℕ)
    (x : (relativeCohomology X.hom 1).obj (unitModule X.left))
    (y : (relativeCohomology X.hom (n + 1)).obj (unitModule X.left)) :
    unitCohomologyPullback h (n + 2)
        (creationCanonical X.hom U hU hUa (n + 1) x y) =
      creationCanonical Y.hom V hV hVa (n + 1)
        (unitCohomologyPullback h 1 x) (unitCohomologyPullback h (n + 1) y) := by
  unfold unitCohomologyPullback
  obtain ⟨x', rfl⟩ := (cohomologyEquiv X.hom U hU hUa 1).surjective x
  obtain ⟨y', rfl⟩ := (cohomologyEquiv X.hom U hU hUa (n + 1)).surjective y
  rw [creationCanonical_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    pull_cohomologyEquiv h U V α hα hU hV hUa hVa, homologyMap_creationH,
    pull_cohomologyEquiv h U V α hα hU hV hUa hVa,
    pull_cohomologyEquiv h U V α hα hU hV hUa hVa, creationCanonical_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end Pull

section Refine

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  {I J : Type u} [Fintype I] [Fintype J] (U : I → X.Opens)
  (V : J → X.Opens) (β : J → I) (hβ : ∀ j, V j ≤ U (β j))

lemma refineCochain_cup_all {q : ℕ} (z : cochain π U (unitModule X) 1)
    (b : cochain π U (unitModule X) q) :
    (refineCochain π U V β hβ (unitModule X)).f (q + 1) (cup π U z b) =
      cup π V ((refineCochain π U V β hβ (unitModule X)).f 1 z)
        ((refineCochain π U V β hβ (unitModule X)).f q b) := by
  rw [refineCochain_unit_eq]
  change Cech.refine (ab X.presheaf) U V β hβ (q + 1) (cup₁ X.presheaf U z b) =
    cup₁ X.presheaf V ((refineCochain π U V β hβ (unitModule X)).f 1 z)
      ((refineCochain π U V β hβ (unitModule X)).f q b)
  rw [refineCochain_unit_eq, refineCochain_unit_eq, refine_cup₁_all]

variable [IsSeparated π] (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤)
  (hUa : ∀ i, IsAffineOpen (U i)) (hVa : ∀ j, IsAffineOpen (V j))

include β hβ in
/-- Creation on positive-degree actual cohomology is invariant under a cover refinement. -/
theorem creationCanonical_refine (n : ℕ)
    (x : (relativeCohomology π 1).obj (unitModule X))
    (y : (relativeCohomology π (n + 1)).obj (unitModule X)) :
    creationCanonical π V hV hVa (n + 1) x y =
      creationCanonical π U hU hUa (n + 1) x y := by
  obtain ⟨z, rfl⟩ := canonicalClass_surjective π U hU hUa 0 x
  obtain ⟨b, rfl⟩ := canonicalClass_surjective π U hU hUa n y
  rw [creationCanonical_canonicalClass,
    canonicalClass_refine π U V β hβ hU hV hUa hVa 0 z,
    canonicalClass_refine π U V β hβ hU hV hUa hVa n b,
    creationCanonical_canonicalClass,
    canonicalClass_refine π U V β hβ hU hV hUa hVa (n + 1)
      ⟨cup π U z b, creation_cup_mem_ker π U z n b⟩]
  congr 1
  apply Subtype.ext
  exact (refineCochain_cup_all π U V β hβ
    (z : cochain π U (unitModule X) 1)
    (b : cochain π U (unitModule X) (n + 1))).symm

end Refine

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
