import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsIsoTransportStatement
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsScalarTowerProof

/-! # Isomorphism transport of fixed universal representatives: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- Changing the actual coefficient by an isomorphism preserves the given
universal representative. -/
theorem isUniversalPerfectSectionsRepresentative_of_iso
    {R : CommRingCat.{u}} {X : Scheme.{u}} {f : X ⟶ Spec R}
    {M N : X.Modules} (η : M ≅ N)
    {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsUniversalPerfectSectionsRepresentative f N K) :
    IsUniversalPerfectSectionsRepresentative f M K := by
  refine ⟨hK.1, ?_, ?_⟩
  · obtain ⟨α⟩ := hK.2.1
    exact ⟨α ≪≫
      (DerivedPlus.derivedComplex (DerivedSections.relativeGlobalSections f) ⋙
        DerivedCategory.Plus.ι).mapIso η.symm⟩
  · intro T φ
    obtain ⟨α⟩ := hK.2.2 T φ
    exact ⟨α ≪≫
      (DerivedPlus.derivedComplex
        (DerivedSections.relativeGlobalSections (pullback.snd f (Spec.map φ))) ⋙
        DerivedCategory.Plus.ι).mapIso
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map φ))).mapIso η.symm)⟩

namespace DerivedSections

/-- Derived sections of the pulled-back coefficient on isomorphic affine
base changes agree, with the usual pullback projections. -/
def relativeDerivedSectionsBaseChangeSchemeIso
    {R T : CommRingCat.{u}} {X Y : Scheme.{u}} (e : X ≅ Y)
    (g : Y ⟶ Spec R) (φ : R ⟶ T) (N : Y.Modules) :
    (DerivedPlus.derivedComplex
        (relativeGlobalSections (pullback.snd (e.hom ≫ g) (Spec.map φ))) ⋙
        DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback
            (pullback.fst (e.hom ≫ g) (Spec.map φ))).obj
              ((Scheme.Modules.pullback e.hom).obj N)) ≅
      (DerivedPlus.derivedComplex
        (relativeGlobalSections (pullback.snd g (Spec.map φ))) ⋙
        DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback (pullback.fst g (Spec.map φ))).obj N) := by
  let eT := asIso
    (pullback.map (e.hom ≫ g) (Spec.map φ) g (Spec.map φ)
      e.hom (𝟙 _) (𝟙 _) (by simp) (by simp))
  have hf : eT.hom ≫ pullback.snd g (Spec.map φ) =
      pullback.snd (e.hom ≫ g) (Spec.map φ) := by
    simp [eT, pullback.map, pullback.lift_snd]
  have ha : eT.hom ≫ pullback.fst g (Spec.map φ) =
      pullback.fst (e.hom ≫ g) (Spec.map φ) ≫ e.hom := by
    simp [eT, pullback.map, pullback.lift_fst]
  exact
    (DerivedPlus.derivedComplex
      (relativeGlobalSections (pullback.snd (e.hom ≫ g) (Spec.map φ))) ⋙
      DerivedCategory.Plus.ι).mapIso
        ((Scheme.Modules.pullbackComp
          (pullback.fst (e.hom ≫ g) (Spec.map φ)) e.hom).app N) ≪≫
      relativeDerivedSectionsIsoOfComp eT hf ha N

end DerivedSections

/-- Scheme and coefficient isomorphisms retain the same fixed complex. -/
theorem universalPerfectSectionsIsoTransport :
    UniversalPerfectSectionsIsoTransportStatement.{u} := by
  intro R X Y e g M N η K hK
  apply isUniversalPerfectSectionsRepresentative_of_iso η
  refine ⟨hK.1, ?_, ?_⟩
  · obtain ⟨α⟩ := hK.2.1
    exact ⟨α ≪≫ ((DerivedSections.relativeDerivedSectionsPullbackIso e g).app N).symm⟩
  · intro T φ
    obtain ⟨α⟩ := hK.2.2 T φ
    exact ⟨α ≪≫
      (DerivedSections.relativeDerivedSectionsBaseChangeSchemeIso e g φ N).symm⟩

end Langlands.AlgebraicGeometry.Modules
