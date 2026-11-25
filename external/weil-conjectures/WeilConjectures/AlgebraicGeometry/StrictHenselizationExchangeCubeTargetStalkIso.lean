/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons
import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

set_option linter.unusedVariables false in
/-- Component theorem: the target strict-local cube stalk comparison is invertible.
Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-target-stalk-iso). -/
theorem Etale.isIso_strictHenselization_exchangeCube_target_stalkComparison
    {S T X X' : Scheme.{u}} {g : T ⟶ S} {f : X ⟶ S}
    [QuasiCompact f] [QuasiSeparated f] {f' : X' ⟶ T} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictLocalizationToBase (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    {X₀ X₁ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f
      (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))
    (p₁ : X₁ ⟶ X₀) (f₁ : X₁ ⟶ Spec (.of B))
    (sq₁ : IsPullback p₁ f₁ f₀ (Spec.map (CommRingCat.ofHom φ)))
    (b : X₁ ⟶ X')
    (sqB : IsPullback b f₁ f'
      (eB.hom ≫ strictLocalizationToBase (ν ≫ τ)))
    (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let jA := eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)
    let jB := eB.hom ≫ strictLocalizationToBase (ν ≫ τ)
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    let ht : t ≫ jB = τ := by simpa only [t, jB, Category.assoc] using hρB
    let h : jB ≫ g = g₀ ≫ jA := by simpa only [jB, g₀, jA, Category.assoc] using hφ.symm
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
    let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f')_*[AddCommGrpCat.{u + 1}])).obj K
    let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
    let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀
    IsIso (derivedStalkComparison jB t τ ht M₂ N₂
      (exchangeCubeTargetComparison sqB.toCommSq hb G) (q : ℤ)) := by
  dsimp only
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  let F' := ((g')^*[AddCommGrpCat.{u + 1}]).obj G
  have hm := isIso_strictHenselization_baseChange_closedStalk f' (ν ≫ τ)
    eB b f₁ sqB ρB F' q
  let E := Functor.mapDerivedCategoryPlusSingleFunctor ((g')^*[AddCommGrpCat.{u + 1}]) 0
  have hm' : IsIso ((pointSmallEtale
      (ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqB.toCommSq).app
            ((D+((g')^*[AddCommGrpCat.{u + 1}])).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj G))))) := by
    exact (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqB.toCommSq)
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ) ⋙
          (pointSmallEtale
            (ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber))
      (E.app G)).mpr hm
  suffices ∀ (s : Spec (.of k') ⟶ T)
      (ht : (ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) ≫
        (eB.hom ≫ strictLocalizationToBase (ν ≫ τ)) = s),
      IsIso (derivedStalkComparison
        (eB.hom ≫ strictLocalizationToBase (ν ≫ τ))
        (ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) s ht
        _ _ (exchangeCubeTargetComparison sqB.toCommSq hb G) (q : ℤ)) by
    exact this τ (by simpa only [Category.assoc] using hρB)
  intro s ht
  subst s
  simp only [derivedStalkComparison, exchangeCubeTargetComparison, Functor.map_comp]
  infer_instance


end AlgebraicGeometry
