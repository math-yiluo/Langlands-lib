/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyGysin
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineRelative

/-!
# A decomposition criterion from the localization triangle

Let `q : X ⟶ S` be a morphism, `i : Z ⟶ X` a closed immersion with `i ≫ q` an isomorphism (a
section of `q`, up to isomorphism) and `j : U ⟶ X` the open immersion of its complement, with
`p = j ≫ q`. For `K ≅ Lq^* M` and a class `γ : Λ_X ⟶ Ri_! Ri^! K` with supports on `Z` whose
adjoint `Λ_Z ⟶ Ri^! K` is an isomorphism, the map

`(η, c♭) : M ⊕ N ⟶ Rq_* K`

built from the unit `M ⟶ Rq_* Lq^* M ≅ Rq_* K` and from the adjoint of the class
`c : Lq^* N ≅ Λ_X ⟶ Ri_! Ri^! K ⟶ K` with forgotten supports is an isomorphism as soon as the
unit `M ⟶ Rp_* Lp^* M` is one
(`AlgebraicGeometry.Etale.isIso_biprodDesc_of_isIso_supportedClassMap`).

Indeed `Rq_*` of the supported localization triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* Lj^* K ⟶` of `K`
is a distinguished triangle whose first term receives the isomorphism `N ⟶ Rq_* Ri_! Ri^! K`
(the class of a section generates) and whose third term receives the isomorphism
`M ⟶ Rp_* Lp^* M ≅ Rq_* Rj_* Lj^* K`; the map of the split triangle `N ⟶ N ⊕ M ⟶ M ⟶` is then
an isomorphism on the middle terms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Let `F₁ ⊣ G₁`, `F₂ ⊣ G₂` and `F ⊣ G` be adjunctions with `F ≅ F₁ ⋙ F₂`. If the unit of
`F ⊣ G` is an isomorphism at `X`, then so is the composite unit
`X ⟶ G₁ F₁ X ⟶ G₁ G₂ F₂ F₁ X`. -/
lemma _root_.CategoryTheory.Adjunction.isIso_unit_app_comp_map_unit_app_of_iso
    {C D E : Type*} [Category* C] [Category* D] [Category* E] {F₁ : C ⥤ D} {G₁ : D ⥤ C}
    {F₂ : D ⥤ E} {G₂ : E ⥤ D} {F : C ⥤ E} {G : E ⥤ C} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)
    (adj : F ⊣ G) (e : F ≅ F₁ ⋙ F₂) (X : C) [IsIso (adj.unit.app X)] :
    IsIso (adj₁.unit.app X ≫ G₁.map (adj₂.unit.app (F₁.obj X))) := by
  have h := unit_conjugateEquiv (adj₁.comp adj₂) adj e.hom X
  rw [Adjunction.comp_unit_app] at h
  have : IsIso ((adj₁.unit.app X ≫ G₁.map (adj₂.unit.app (F₁.obj X))) ≫
      (conjugateEquiv (adj₁.comp adj₂) adj e.hom).app ((F₁ ⋙ F₂).obj X)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((conjugateEquiv (adj₁.comp adj₂) adj e.hom).app ((F₁ ⋙ F₂).obj X))

/-- **A decomposition criterion.** Let `q : X ⟶ S`, let `i : Z ⟶ X` be a closed immersion with
`i ≫ q` an isomorphism and `j : U ⟶ X` an open immersion onto the complement of `Z`, with
`p = j ≫ q`. Let `ε : Lq^* M ≅ K`, `e : Lq^* N ≅ Λ_X`, and let `γ : Λ_X ⟶ Ri_! Ri^! K` be a
class with supports whose adjoint `Λ_Z ⟶ Ri^! K` is an isomorphism. If the unit
`M ⟶ Rp_* Lp^* M` is an isomorphism, then so is

`(η_M ≫ Rq_* ε, η_N ≫ Rq_*(e ≫ γ ≫ counit)) : M ⊕ N ⟶ Rq_* K`. -/
theorem isIso_biprodDesc_of_isIso_supportedClassMap {X S Z U : Scheme.{u}} (q : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIso (i ≫ q)] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (p : U ⟶ S) (hp : j ≫ q = p)
    {M N : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ε : (L((q)^*[ModuleCat.{u + 1} Λ])).obj M ≅ K)
    (e : (L((q)^*[ModuleCat.{u + 1} Λ])).obj N ≅ constantComplex Λ X)
    (hM : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M))
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj K))
    (hγ : IsIso (supportedClassMap Λ i γ)) :
    IsIso (biprod.desc
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app N ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map
          (e.hom ≫ γ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app K))) := by
  have hb := isIso_unit_comp_map_of_isIso_supportedClassMap_of_isIso q i e γ hγ
  have hT : Triangle.mk ((R((q)_*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekAdjunction Λ i).counit.app K))
      ((R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K))
      (localizationTriangleLowerStar Λ q i j hij K).mor₃ ∈ distTriang _ :=
    localizationTriangleLowerStar_mem_distTriang Λ q i j hij K
  have h₁₂ := comp_distTriang_mor_zero₁₂ _ hT
  have h₂₃ := comp_distTriang_mor_zero₂₃ _ hT
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃] at h₁₂ h₂₃
  have h₃ : IsIso (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom) ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K)) := by
    have := Adjunction.isIso_unit_app_comp_map_unit_app_of_iso
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
      (leftDerivedUpperStarComp _ j q p hp.symm) M
    rw [Category.assoc, ← Functor.map_comp, ← Adjunction.unit_naturality, Functor.map_comp,
      ← Category.assoc]
    infer_instance
  have key := isIso₂_of_isIso₁₃ (Triangle.homMk (binaryBiproductTriangle N M)
    (Triangle.mk ((R((q)_*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekAdjunction Λ i).counit.app K))
      ((R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K))
      (localizationTriangleLowerStar Λ q i j hij K).mor₃)
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app N ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫ γ))
    ((biprod.braiding N M).hom ≫ biprod.desc
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app N ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map
          (e.hom ≫ γ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app K)))
    (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom) ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K))
    ?_ ?_ ?_) (binaryBiproductTriangle_distinguished N M) hT hb h₃
  · exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ key
  · simp [biprod.braiding]
  · refine biprod.hom_ext' _ _ ?_ ?_
    · simpa [biprod.braiding] using (((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) q).unit.app N ≫ (R((q)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫ γ)) ≫=
        h₁₂).symm
    · simp [biprod.braiding]
  · simpa using (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom) ≫= h₂₃).symm

end Etale

end AlgebraicGeometry
