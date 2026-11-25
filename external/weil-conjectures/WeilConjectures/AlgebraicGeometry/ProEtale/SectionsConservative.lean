/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Evaluation on affine weakly contractible objects is conservative

## References

* Stacks Project, Tag 03DA
* Stacks Project, Tag 0947(1)
* Stacks Project, Tags 0946, 0947, 05RT, and 0115
-/

@[expose] public section

set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{t}}

/-- The module-sheaf category is abelian in the common site/coefficient universe. -/
noncomputable instance sections_module_abelian (R : Sheaf (topology X) RingCat.{u}) :
    Abelian (ringedSiteModules.{max u (t + 1)} R) := by
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses (topology X) R
  infer_instance

/-- Evaluation of module sheaves on a site object is additive. -/
noncomputable instance sections_evaluation_additive
    (R : Sheaf (topology X) RingCat.{u}) (W : X.ProEt) :
    (SheafOfModules.evaluation.{max u (t + 1)} R (op W)).Additive :=
  inferInstanceAs ((SheafOfModules.forget R ⋙
    PresheafOfModules.evaluation R.obj (op W)).Additive)

/-- Exactness is detected on affine weakly contractible objects by local lifting. -/
private theorem exact_sections_iff
    (R : Sheaf (topology X) RingCat.{u})
    (S : ShortComplex (ringedSiteModules.{max u (t + 1)} R)) :
    S.Exact ↔ ∀ (W : X.ProEt), IsAffine W.left →
      (topology X).IsWeaklyContractible.{max u (t + 1)} W →
        (S.map (SheafOfModules.evaluation R (op W))).Exact := by
  have : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  have : HasSheafify (topology X) AddCommGrpCat.{max u (t + 1)} :=
    siteAbelianHasSheafify (topology X)
  have : (topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    siteAbelianWEqualsLocallyBijective (topology X)
  let F := SheafOfModules.toSheaf.{max u (t + 1)} R
  have : PreservesFiniteColimits F :=
    (moduleSheaves_colimits_forgetful.{t + 1, t, u, max u (t + 1)} R).2.2.1
  have key (W : X.ProEt) :
      (S.map (SheafOfModules.evaluation R (op W))).Exact ↔
        Function.Surjective ((F.map (kernel.lift S.g S.f S.zero)).hom.app (op W)) := by
    rw [ShortComplex.exact_map_iff_epi_map_kernel_lift, ModuleCat.epi_iff_surjective]
    rfl
  simp_rw [key]
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  constructor
  · intro h W _ hW
    have : Epi (F.map (kernel.lift S.g S.f S.zero)) := inferInstance
    exact hW ((sheafCompose (topology X) (CategoryTheory.forget AddCommGrpCat)).map
      (F.map (kernel.lift S.g S.f S.zero)))
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1
        ((Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)}
          (F.map (kernel.lift S.g S.f S.zero))).2 inferInstance))
  · intro h
    apply F.epi_of_epi_map (f := kernel.lift S.g S.f S.zero)
    apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)}
      (F.map (kernel.lift S.g S.f S.zero))).1
    refine ⟨fun {V} s ↦ ?_⟩
    obtain ⟨ι, W, f, hcov, hW⟩ := exists_wContractible_affine_cover X V
    have hcov' : Sieve.ofArrows W f ∈ topology X V :=
      Precoverage.generate_mem_toGrothendieck hcov
    refine (topology X).superset_covering ?_ hcov'
    rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
    obtain ⟨D, hD, e, _⟩ := hW i
    have : IsWContractibleRing D := hD
    have ha : IsAffine (W i).left := IsAffine.of_isIso e.inv
    have hw : (topology X).IsWeaklyContractible.{max u (t + 1)} (W i) :=
      isWeaklyContractible_of_iso e.symm
    exact (Presheaf.imageSieve _ s).downward_closed (h _ ha hw _) a

/-- Evaluation on affine weakly contractible objects detects exact sequences, acyclic
complexes, isomorphisms, and quasi-isomorphisms of modules on the small pro-etale site. -/
theorem sections_conservative
    (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) :
    (∀ (A B C : ringedSiteModules.{max u (t + 1)} R)
        (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).Exact ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            ((ShortComplex.mk f g h).map
              (SheafOfModules.evaluation.{max u (t + 1)} R (op W))).Exact) ∧
    (∀ (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ),
      K.Acyclic ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            HomologicalComplex.Acyclic
              ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj K)) ∧
    (∀ (A B : ringedSiteModules.{max u (t + 1)} R) (f : A ⟶ B),
      IsIso f ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            Function.Bijective
              ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).map f).hom) ∧
    (∀ (K L : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
        (f : K ⟶ L),
      QuasiIso f ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            QuasiIso
              (((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f)) := by
  have hacyclic (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ) :
      K.Acyclic ↔ ∀ (W : X.ProEt), IsAffine W.left →
        (topology X).IsWeaklyContractible.{max u (t + 1)} W →
          ((SheafOfModules.evaluation R (op W)).mapHomologicalComplex
            (ComplexShape.up ℤ) |>.obj K).Acyclic := by
    constructor
    · intro h W ha hw i
      exact (exact_sections_iff R (K.sc i)).1 (h i) W ha hw
    · intro h i
      exact (exact_sections_iff R (K.sc i)).2 (fun W ha hw ↦ h W ha hw i)
  refine ⟨fun A B C f g h ↦ exact_sections_iff R (ShortComplex.mk f g h),
    hacyclic, ?_, ?_⟩
  · intro A B f
    constructor
    · intro hf W _ _
      have := hf
      exact (ConcreteCategory.isIso_iff_bijective _).1
        (inferInstanceAs (IsIso ((SheafOfModules.evaluation R (op W)).map f)))
    · intro hf
      have hm : Mono f := by
        let S := ShortComplex.mk (0 : A ⟶ A) f (by simp)
        apply (S.exact_iff_mono rfl).1
        apply (exact_sections_iff R S).2
        intro W ha hw
        have : Mono ((SheafOfModules.evaluation R (op W)).map f) :=
          (ModuleCat.mono_iff_injective _).2 (hf W ha hw).1
        exact ((S.map (SheafOfModules.evaluation R (op W))).exact_iff_mono
          (by simp [S])).2
          (show Mono ((SheafOfModules.evaluation R (op W)).map f) from inferInstance)
      have he : Epi f := by
        let S := ShortComplex.mk f (0 : B ⟶ B) (by simp)
        apply (S.exact_iff_epi rfl).1
        apply (exact_sections_iff R S).2
        intro W ha hw
        have : Epi ((SheafOfModules.evaluation R (op W)).map f) :=
          (ModuleCat.epi_iff_surjective _).2 (hf W ha hw).2
        exact ((S.map (SheafOfModules.evaluation R (op W))).exact_iff_epi
          (by simp [S])).2
          (show Epi ((SheafOfModules.evaluation R (op W)).map f) from inferInstance)
      exact isIso_of_mono_of_epi f
  · intro K L f
    rw [CochainComplex.mappingCone.quasiIso_iff_acyclic, hacyclic]
    constructor
    · intro h W ha hw
      rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
      exact fun i ↦ (h W ha hw i).of_iso
        (CochainComplex.mappingCone.mapHomologicalComplexIso f
          (SheafOfModules.evaluation R (op W)))
    · intro h W ha hw
      have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic _).1 (h W ha hw)
      exact fun i ↦ (hc i).of_iso
        (CochainComplex.mappingCone.mapHomologicalComplexIso f
          (SheafOfModules.evaluation R (op W))).symm

end AlgebraicGeometry.Scheme.ProEt
