import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCup
import Langlands.Cohomology.CechRefine

/-!
# Refinement of ordered Čech covers
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology

section Sheaf

variable {X : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J] {U : I → X.Opens}
  {V : J → X.Opens} (β : J → I) (hβ : ∀ j, V j ≤ U (β j)) (M : X.Modules)

omit [Fintype I] [Fintype J] in
include hβ in
lemma inter_le_refine {n : ℕ} (τ : Fin n → J) : inter V τ ≤ inter U (β ∘ τ) :=
  le_iInf fun a => (inter_le_apply τ a).trans (hβ (τ a))

/-- The refinement map in degree `p`: its `τ`-component restricts the `β ∘ τ`-component. -/
def refineTerm (p : ℕ) : term U M p ⟶ term V M p :=
  biproduct.lift fun τ => biproduct.π (fun σ : Fin (p + 1) → I => sheafOn M (inter U σ)) (β ∘ τ) ≫
    res M (inter_le_refine β hβ τ)

@[reassoc]
lemma refineTerm_π (p : ℕ) (τ : Fin (p + 1) → J) :
    refineTerm β hβ M p ≫ biproduct.π (fun τ : Fin (p + 1) → J => sheafOn M (inter V τ)) τ =
      biproduct.π (fun σ : Fin (p + 1) → I => sheafOn M (inter U σ)) (β ∘ τ) ≫
        res M (inter_le_refine β hβ τ) :=
  biproduct.lift_π _ _

lemma refineTerm_d (p : ℕ) :
    refineTerm β hβ M p ≫ d V M p = d U M p ≫ refineTerm β hβ M (p + 1) := by
  refine biproduct.hom_ext _ _ fun t => ?_
  rw [Category.assoc, d_π, Category.assoc, refineTerm_π, ← Category.assoc, d_π]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.assoc, refineTerm_π_assoc, res_comp]
  rfl

/-- The refinement map of sheafified ordered Čech complexes. -/
def refineComplex : complex U M ⟶ complex V M :=
  CochainComplex.ofHom (refineTerm β hβ M) (fun p => by
    change refineTerm β hβ M p ≫ (complex V M).d p (p + 1) =
      (complex U M).d p (p + 1) ≫ refineTerm β hβ M (p + 1)
    simpa only [complex, CochainComplex.of_d] using refineTerm_d β hβ M p)

@[simp]
lemma refineComplex_f (p : ℕ) : (refineComplex β hβ M).f p = refineTerm β hβ M p := rfl

lemma augmentation_refineTerm :
    augmentation U M ≫ refineTerm β hβ M 0 = augmentation V M := by
  refine biproduct.hom_ext _ _ fun s => ?_
  rw [Category.assoc, refineTerm_π, augmentation_π_assoc, augmentation_π, unit_res]

lemma aug_refineComplex :
    aug U M ≫ refineComplex β hβ M = (CochainComplex.single₀ X.Modules).map (𝟙 M) ≫ aug V M := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  ext : 1
  simpa only [HomologicalComplex.comp_f, aug, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    refineComplex_f] using augmentation_refineTerm β hβ M

end Sheaf

section Cochain

open DerivedSections

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) {I J : Type u} [Fintype I]
  [Fintype J] (U : I → X.Opens) (V : J → X.Opens) (β : J → I) (hβ : ∀ j, V j ≤ U (β j))
  (M : X.Modules)

/-- The refinement map of ordered Čech cochain complexes. -/
def refineCochain : cochainComplex π U M ⟶ cochainComplex π V M :=
  (sectionsComplexIso π U M).inv ≫
    ((relativeGlobalSections π).mapHomologicalComplex _).map (refineComplex β hβ M) ≫
      (sectionsComplexIso π V M).hom

/-- On cochains, the refinement map restricts the `β ∘ τ`-component. -/
lemma refineCochain_f_apply (p : ℕ) (c : cochain π U M p) (τ : Fin (p + 1) → J) :
    (refineCochain π U V β hβ M).f p c τ =
      M.presheaf.map (homOfLE (inter_le_refine β hβ τ)).op (c (β ∘ τ)) := by
  set x := (sectionsComplexIso π U M).inv.f p c with hxdef
  have hx : toCochainFun U M x = c := by
    have e : (sectionsComplexIso π U M).hom.f p ((sectionsComplexIso π U M).inv.f p c) = c := by
      rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
        HomologicalComplex.id_f, ConcreteCategory.id_apply]
    exact e
  have e1 : (refineCochain π U V β hβ M).f p c =
      toCochainFun V M ((refineTerm β hβ M p).app ⊤ x) := by
    simp only [refineCochain, HomologicalComplex.comp_f]
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    rfl
  rw [e1, ← hx]
  simp only [toCochainFun, cr_def, toSec]
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, refineTerm_π,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, res_app]
  exact map_map_eq M _ _ _ _ _

variable [IsSeparated π] [M.IsQuasicoherent] (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤)
  (hUa : ∀ i, IsAffineOpen (U i)) (hVa : ∀ j, IsAffineOpen (V j))

/-- **Independence of the cover.** The ordered Čech descriptions of actual cohomology for a
cover and a refinement are related by the refinement map. -/
theorem cohomologyIso_refine (n : ℕ) :
    HomologicalComplex.homologyMap (refineCochain π U V β hβ M) n ≫
        (cohomologyIso π V M hV hVa n).hom = (cohomologyIso π U M hU hUa n).hom := by
  have := quasiIso_aug U M hU
  have := quasiIso_aug V M hV
  have key := AcyclicResolution.resolutionComparison_naturality (relativeGlobalSections π)
    (aug U M) (aug V M) (𝟙 M) (refineComplex β hβ M) (aug_refineComplex β hβ M) n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at key
  have e : HomologicalComplex.homologyMap (refineCochain π U V β hβ M) n ≫
      HomologicalComplex.homologyMap (sectionsComplexIso π V M).inv n =
      HomologicalComplex.homologyMap (sectionsComplexIso π U M).inv n ≫
        HomologicalComplex.homologyMap
          (((relativeGlobalSections π).mapHomologicalComplex _).map (refineComplex β hβ M)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      refineCochain]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [cohomologyIso, cohomologyIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom]
  rw [← key]
  exact ((reassoc_of% e) _).trans rfl

end Cochain

section Unit

open DerivedSections Cech

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) [IsSeparated π] {I J : Type u}
  [Fintype I] [Fintype J] (U : I → X.Opens) (V : J → X.Opens) (β : J → I)
  (hβ : ∀ j, V j ≤ U (β j)) (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤)
  (hUa : ∀ i, IsAffineOpen (U i)) (hVa : ∀ j, IsAffineOpen (V j))

omit [IsSeparated π] in
/-- On structure-sheaf cochains, the refinement map is the Library's `Cech.refine`. -/
lemma refineCochain_unit_eq (p : ℕ) (c : cochain π U (unitModule X) p) :
    ((refineCochain π U V β hβ (unitModule X)).f p c : C (ab X.presheaf) V p) =
      Cech.refine (ab X.presheaf) U V β hβ p (c : C (ab X.presheaf) U p) := by
  funext τ
  rw [refineCochain_f_apply]
  rfl

omit [IsSeparated π] in
lemma refine_mem_ker (n : ℕ) (z : LinearMap.ker (dCochain π U (unitModule X) (n + 1))) :
    (refineCochain π U V β hβ (unitModule X)).f (n + 1)
        (show (cochainComplex π U (unitModule X)).X (n + 1) from
          (z : cochain π U (unitModule X) (n + 1))) ∈
      LinearMap.ker (dCochain π V (unitModule X) (n + 1)) := by
  rw [LinearMap.mem_ker]
  have e := congrArg (fun f => f (show (cochainComplex π U (unitModule X)).X (n + 1) from
    (z : cochain π U (unitModule X) (n + 1)))) ((refineCochain π U V β hβ (unitModule X)).comm
      (n + 1) (n + 2))
  simp only [ConcreteCategory.comp_apply, cochainComplex_d] at e
  refine e.trans ?_
  change (refineCochain π U V β hβ (unitModule X)).f (n + 2)
    (dCochain π U (unitModule X) (n + 1) (z : cochain π U (unitModule X) (n + 1))) = 0
  rw [z.2, map_zero]

/-- The actual class of a cocycle is the class of its refinement. -/
lemma canonicalClass_refine (n : ℕ)
    (z : LinearMap.ker (dCochain π U (unitModule X) (n + 1))) :
    canonicalClass π U hU hUa n z = canonicalClass π V hV hVa n ⟨_, refine_mem_ker π U V β hβ n z⟩ := by
  have key := cohomologyIso_refine π U V β hβ (unitModule X) hU hV hUa hVa (n + 1)
  have h := congrArg (fun f => f (classMap π U (unitModule X) n z)) key
  simp only [ConcreteCategory.comp_apply] at h
  rw [homologyMap_classMap] at h
  exact h.symm

omit [IsSeparated π] in
lemma refineCochain_cup (z w : cochain π U (unitModule X) 1) :
    (refineCochain π U V β hβ (unitModule X)).f 2 (cup π U z w) =
      cup π V ((refineCochain π U V β hβ (unitModule X)).f 1 z)
        ((refineCochain π U V β hβ (unitModule X)).f 1 w) := by
  change ((refineCochain π U V β hβ (unitModule X)).f 2 (cup π U z w) : C (ab X.presheaf) V 2) =
    cup₁ X.presheaf V ((refineCochain π U V β hβ (unitModule X)).f 1 z : C (ab X.presheaf) V 1)
      ((refineCochain π U V β hβ (unitModule X)).f 1 w : C (ab X.presheaf) V 1)
  rw [refineCochain_unit_eq, refineCochain_unit_eq, refineCochain_unit_eq]
  change Cech.refine (ab X.presheaf) U V β hβ 2 (cup₁ X.presheaf U (z : C (ab X.presheaf) U 1)
      (w : C (ab X.presheaf) U 1)) = _
  rw [cup₁_eq_prod, Cech.refine_prod, cup₁_eq_prod]
  congr 1
  funext k
  fin_cases k <;> rfl

include β hβ in
/-- **The cup product does not depend on the cover**: it agrees on a cover and on any
refinement. -/
theorem cupCanonical_refine (x y : (relativeCohomology π 1).obj (unitModule X)) :
    cupCanonical π V hV hVa x y = cupCanonical π U hU hUa x y := by
  obtain ⟨z, rfl⟩ := canonicalClass_surjective π U hU hUa 0 x
  obtain ⟨w, rfl⟩ := canonicalClass_surjective π U hU hUa 0 y
  rw [cupCanonical_canonicalClass, canonicalClass_refine π U V β hβ hU hV hUa hVa 0 z,
    canonicalClass_refine π U V β hβ hU hV hUa hVa 0 w, cupCanonical_canonicalClass,
    canonicalClass_refine π U V β hβ hU hV hUa hVa 1 (cupZ π U z w)]
  congr 1
  apply Subtype.ext
  simp only [cupZ_apply]
  exact (refineCochain_cup π U V β hβ z w).symm

end Unit

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
