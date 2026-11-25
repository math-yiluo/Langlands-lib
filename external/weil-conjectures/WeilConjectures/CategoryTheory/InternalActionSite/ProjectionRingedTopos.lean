/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.ProperBaseChange.ContinuousCocontinuousRingedRestriction
public import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AcyclicTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# The projection of the internal action site as a morphism of ringed topoi

Source: Stacks, Cohomology on Sites, Tag 0D6E (auxiliary; not a blueprint node).

The projection `Object K ⥤ C` from the twisted action site to the base site is continuous and
cocontinuous. Pulling back along it gives modules with trivial action, and its right adjoint
is the fixed-point direct image. We deduce that restriction of scalars on the twisted site
sends K-injective complexes to complexes acyclic for every right adjoint of the pullback along
the projection (Stacks 0D6E applied to the composite of the two ringed-topos morphisms).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] (K : Cᵒᵖ ⥤ GrpCat.{u})

-- Copy of the private `label_mem_iff` of `InternalActionSiteBasic`.
private theorem label_mem_iff' {X Y : Object K} (S : Sieve X) (f : Y ⟶ X) :
    S f ↔ S (Arrow.mk f.base 1) := by
  constructor
  · intro hf
    have h := S.downward_closed hf (Arrow.mk (𝟙 Y.base) f.label⁻¹)
    have he : (Arrow.mk (𝟙 Y.base) f.label⁻¹ : Y ⟶ Y) ≫ f =
        Arrow.mk f.base 1 := by
      apply arrow_ext K (Category.id_comp _)
      change f.label⁻¹ * K.map (𝟙 Y.base).op f.label = 1
      simp
    rwa [he] at h
  · intro hf
    have h := S.downward_closed hf (Arrow.mk (𝟙 Y.base) f.label)
    have he : (Arrow.mk (𝟙 Y.base) f.label : Y ⟶ Y) ≫ Arrow.mk f.base 1 = f := by
      apply arrow_ext K (Category.id_comp _)
      change f.label * K.map (𝟙 Y.base).op 1 = f.label
      simp
    rwa [he] at h

/-- Sheaves of sets on the base pull back to sheaves on the twisted site. -/
theorem projection_op_comp_isSheaf (J : Precoverage C) [HasFiniteLimits C]
    (hJ : J.IsSiteForCoverings) (P : Cᵒᵖ ⥤ Type u)
    (hP : Presieve.IsSheaf J.toGrothendieck P) :
    Presieve.IsSheaf (topology K J) ((projection K).op ⋙ P) := by
  intro X S hs x hx
  let y : (labelOneSieve K S).arrows.FamilyOfElements P :=
    fun Y f hf ↦ x (Arrow.mk f 1) hf
  have hy : y.Compatible := by
    apply (Presieve.compatible_iff_sieveCompatible y).2
    intro Y Z f g hf
    have h := hx.to_sieveCompatible (Arrow.mk f 1) (Arrow.mk g 1) hf
    change x (Arrow.mk (g ≫ f) (1 * K.map g.op 1)) _ = P.map g.op (y f hf) at h
    refine Eq.trans ?_ h
    dsimp only [y]
    congr 1
    apply arrow_ext K
    · rfl
    · change (1 : K.obj (op Z)) = 1 * K.map g.op 1
      simp
  obtain ⟨t, ht, hu⟩ := hP _ ((topology_mem_iff K J hJ X S).1 hs) y hy
  refine ⟨t, ?_, ?_⟩
  · intro Y f hf
    have h := hx.to_sieveCompatible (Arrow.mk f.base 1)
      (Arrow.mk (𝟙 Y.base) f.label) ((label_mem_iff' K S f).1 hf)
    have he' : x ((Arrow.mk (𝟙 Y.base) f.label : Y ⟶ Y) ≫
        (Arrow.mk f.base 1 : Y ⟶ X))
        (S.downward_closed ((label_mem_iff' K S f).1 hf) _) = x f hf := by
      congr 1
      apply arrow_ext K (Category.id_comp _)
      change f.label * K.map (𝟙 Y.base).op 1 = f.label
      simp
    have h' : x f hf = P.map (𝟙 Y.base).op
        (y f.base ((label_mem_iff' K S f).1 hf)) := he'.symm.trans h
    simp only [op_id, P.map_id, types_id_apply] at h'
    exact (ht f.base ((label_mem_iff' K S f).1 hf)).trans h'.symm
  · intro z hz
    apply hu z
    intro Y f hf
    exact hz (Arrow.mk f 1) hf

/-- The projection is continuous. -/
theorem projection_isContinuous (J : Precoverage C) [HasFiniteLimits C]
    (hJ : J.IsSiteForCoverings) :
    (projection K).IsContinuous (topology K J) J.toGrothendieck :=
  ⟨fun G ↦ projection_op_comp_isSheaf K J hJ G.obj
    ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)⟩

/-- The projection is cocontinuous: a twisted sieve covers when its label-one part does. -/
theorem projection_isCocontinuous (J : Precoverage C) [HasFiniteLimits C]
    (hJ : J.IsSiteForCoverings) :
    (projection K).IsCocontinuous (topology K J) J.toGrothendieck where
  cover_lift {U} {S} hS := by
    rw [topology_mem_iff K J hJ]
    exact hS

variable [HasFiniteLimits C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)

/-- Pullback of base modules along the projection: the same sections with the labels acting
trivially. -/
noncomputable abbrev trivialPullback (S : Sheaf J.toGrothendieck CommRingCat.{u}) :
    SheafOfModules.{u} (baseRing J.toGrothendieck S) ⥤
      SheafOfModules.{u} (twistedRing K J hJ S) :=
  have := projection_isContinuous K J hJ
  SheafOfModules.pushforward.{u} (F := projection K) (J := topology K J)
    (K := J.toGrothendieck) (𝟙 (twistedRing K J hJ S))

/-- Stacks 0D6E for the twisted site: restriction of scalars along any map of twisted
coefficient rings sends K-injective complexes to complexes acyclic for every right adjoint of
the pullback along the projection (the fixed-point direct image). -/
theorem restrictScalars_kInjectiveImageAcyclic (S S' : Sheaf J.toGrothendieck CommRingCat.{u})
    (c : twistedRing K J hJ S ⟶ twistedRing K J hJ S')
    (G : SheafOfModules.{u} (twistedRing K J hJ S) ⥤
      SheafOfModules.{u} (baseRing J.toGrothendieck S)) [G.Additive]
    (adj : trivialPullback K J hJ S ⊣ G) :
    Functor.KInjectiveImageAcyclic (SheafOfModules.restrictScalars.{u} c) G := by
  have := projection_isContinuous K J hJ
  have := projection_isCocontinuous K J hJ
  obtain ⟨g, -, -, ⟨adjg⟩⟩ := continuous_cocontinuous_ringed_restriction (topology K J)
    J.toGrothendieck (projection K) (baseRing J.toGrothendieck S)
  obtain ⟨f, hf⟩ := restrictionRingedToposModuleDirectImage_exists c
  let := HasDerivedCategory.standard (SheafOfModules.{u} (twistedRing K J hJ S'))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (twistedRing K J hJ S))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (baseRing J.toGrothendieck S))
  obtain ⟨Rf, Rg, Rgf, ηf, ηg, ηgf, -, -, -, -, -, κ, ⟨-, hκ⟩, -⟩ :=
    ringedToposDerivedPushforwardComposition (topology K J) (topology K J) J.toGrothendieck
      (coefficientSheaf K J hJ S') (coefficientSheaf K J hJ S) S f g
  let gm : SheafOfModules.{u} (twistedRing K J hJ S) ⥤
      SheafOfModules.{u} (baseRing J.toGrothendieck S) := g.modules
  have : gm.Additive := g.additive
  have hg : Functor.KInjectiveImageAcyclic (SheafOfModules.restrictScalars.{u} c) gm := by
    intro I _ T _ j _
    have h : (f.modules.mapHomologicalComplex (.up ℤ)).obj I =
        ((SheafOfModules.restrictScalars.{u} c).mapHomologicalComplex (.up ℤ)).obj I := by
      have key (F : SheafOfModules.{u} (twistedRing K J hJ S') ⥤
          SheafOfModules.{u} (twistedRing K J hJ S)) [F.PreservesZeroMorphisms]
          (e : F = SheafOfModules.restrictScalars.{u} c) :
          (F.mapHomologicalComplex (.up ℤ)).obj I =
            ((SheafOfModules.restrictScalars.{u} c).mapHomologicalComplex (.up ℤ)).obj I := by
        subst e
        rfl
      exact key _ hf
    have : QuasiIso (eqToHom h ≫ j) := by
      have := quasiIso_of_isIso (eqToHom h)
      exact quasiIso_comp _ _
    have hq := (hκ I inferInstance T inferInstance (eqToHom h ≫ j)).1
    rw [Functor.map_comp] at hq
    have : IsIso ((g.modules.mapHomologicalComplex (.up ℤ)).map (eqToHom h)) :=
      ((g.modules.mapHomologicalComplex (.up ℤ)).mapIso (eqToIso h)).isIso_hom
    have := quasiIso_of_isIso ((g.modules.mapHomologicalComplex (.up ℤ)).map (eqToHom h))
    exact (quasiIso_iff_comp_left _ _).1 hq
  have : (Equivalence.refl (C := SheafOfModules.{u} (twistedRing K J hJ S'))).functor.Additive :=
    inferInstanceAs (𝟭 _).Additive
  have : (Equivalence.refl (C := SheafOfModules.{u} (twistedRing K J hJ S))).functor.Additive :=
    inferInstanceAs (𝟭 _).Additive
  have : (Equivalence.refl (C := SheafOfModules.{u}
      (baseRing J.toGrothendieck S))).functor.Additive :=
    inferInstanceAs (𝟭 _).Additive
  exact Functor.KInjectiveImageAcyclic.of_equivalence (Equivalence.refl) (Equivalence.refl)
    (Equivalence.refl) (Iso.refl _)
    (Functor.isoWhiskerRight (adj.rightAdjointUniq adjg) _) hg

end CategoryTheory.InternalActionSite
