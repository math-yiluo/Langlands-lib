/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleAffineEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Exact sections at an algebraically closed pro-etale point

## References

* Stacks Project, Tags 0982 and 098H
* Tag 0946
* Tags 015F and 014X
* Stacks Project, Tag 03CW
* Tag 010N
-/

@[expose] public section

universe u w w'

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- Sections of module sheaves at the final small pro-etale object, with their actual
section-ring action. This is exactly Mathlib evaluation, after forgetting commutativity
of the coefficient sheaf; it introduces no different module category or section functor. -/
noncomputable abbrev pointModuleSections (k : Type u) [Field k]
    (A : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :
    ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) ⥤
      ModuleCat.{u + 1}
        (((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj.obj
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) :=
  SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

/-- Sections at an algebraically closed pro-etale point are exact, and their termwise
extension induces the specified unbounded derived functor with natural cohomology comparison. -/
theorem point_proEtale_sections_exact (k : Type u) [Field k] [IsAlgClosed k] :
    (∀ (F G : Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1})
      (f : F ⟶ G), Epi f →
      Function.Surjective
        ((((sheafSections (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).map f).hom)) ∧
    (∀ A : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
      PreservesFiniteLimits (pointModuleSections k A) ∧
      PreservesFiniteColimits (pointModuleSections k A) ∧
      (∀ (K L : CochainComplex (ringedSiteModules.{u + 1}
          ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ)
        (f : K ⟶ L), QuasiIso f →
        QuasiIso (((pointModuleSections k A).mapHomologicalComplex (.up ℤ)).map f)) ∧
      (∀ [HasDerivedCategory.{w} (ringedSiteModules.{u + 1}
          ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))]
        [HasDerivedCategory.{w'}
          (ModuleCat.{u + 1}
            (((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj.obj
                (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))))]
        [PreservesFiniteLimits (pointModuleSections k A)]
        [PreservesFiniteColimits (pointModuleSections k A)],
        Nonempty (Functor.CommShift (pointModuleSections k A).mapDerivedCategory ℤ) ∧
        Functor.IsTriangulated (pointModuleSections k A).mapDerivedCategory ∧
        Nonempty
          (DerivedCategory.Q ⋙ (pointModuleSections k A).mapDerivedCategory ≅
            (pointModuleSections k A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ∧
        ∀ i : ℤ, Nonempty
          ((pointModuleSections k A).mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ i ≅
            DerivedCategory.homologyFunctor _ i ⋙ pointModuleSections k A))) := by
  classical
  have : WLocalSpace (PrimeSpectrum k) :=
    { eq_of_specializes := fun _ _ _ _ ↦ Subsingleton.elim _ _
      isClosed_closedPoints := by
        have : closedPoints (PrimeSpectrum k) = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact mem_closedPoints_iff.mpr isClosed_singleton
        rw [this]
        exact isClosed_univ }
  have : IsWLocalRing k := ⟨inferInstance⟩
  have : IsAlgClosed (IsLocalRing.ResidueField k) :=
    IsAlgClosed.of_ringEquiv k _
      (RingEquiv.ofBijective (IsLocalRing.residue k)
        ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩)
  have : IsStrictlyHenselianLocalRing k := ⟨inferInstance⟩
  have hstrict (m : Ideal k) [m.IsMaximal] :
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
    apply IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.atUnits k m.primeCompl (S := Localization.AtPrime m) ?_).toRingEquiv
    intro x hx
    exact isUnit_iff_ne_zero.mpr (fun he ↦ hx (he ▸ m.zero_mem))
  have hretract (B : Type u) [CommRing B] (φ : k →+* B)
      (hf : φ.FaithfullyFlat) (hw : φ.WeaklyEtale) :
      ∃ r : B →+* k, r.comp φ = RingHom.id k :=
    RingHom.exists_retraction_of_wlocal_geometric_criterion hstrict φ hf hw
  have hW (F G : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1)))
      (f : F ⟶ G) (hf : Epi f) :
      Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
    exact Scheme.ProEt.surjective_app_of_affine_ring_retractions.{u, u}
      (Spec (.of k)) k (𝟙 _) hretract F G f
  constructor
  · intro F G f hf
    have : Epi f := hf
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} f).mpr hf
    let g := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).map f
    exact hW _ _ g inferInstance
  · intro A
    have : IsAffine (Scheme.ProEt.mk (𝟙 (Spec (.of k)))).left :=
      inferInstanceAs (IsAffine (Spec (.of k)))
    obtain ⟨hlim, hcol, -⟩ := Scheme.ProEt.affine_weaklyContractible_evaluation_colimits
      (Spec (.of k)) A (Scheme.ProEt.mk (𝟙 _)) hW
    have : PreservesFiniteLimits (pointModuleSections k A) := hlim
    have : PreservesFiniteColimits (pointModuleSections k A) := hcol
    refine ⟨hlim, hcol, ?_, ?_⟩
    · intro K L f hf
      have : QuasiIso f := hf
      infer_instance
    · intro _ _ _ _
      refine ⟨⟨inferInstance⟩, inferInstance,
        ⟨(pointModuleSections k A).mapDerivedCategoryFactors⟩, ?_⟩
      intro i
      exact ⟨((pointModuleSections k A).mapDerivedCategoryHomologyFunctorIso i).symm⟩

end AlgebraicGeometry.ProEtale
