/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionQCoh
import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomology
import WeilConjectures.AlgebraicGeometry.AffineAlgebraExactDerivedCounitIso
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionIsos
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Cohomology of the affine algebra derived unit

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

private theorem restriction_exact {Z : TopCat.{v}}
    (O A : Z.Sheaf RingCat.{v}) (φ : O ⟶ A) :
    Limits.PreservesFiniteLimits (SheafOfModules.restrictScalars.{v} φ) ∧
      Limits.PreservesFiniteColimits (SheafOfModules.restrictScalars.{v} φ) := by
  let T := SheafOfModules.restrictScalars.{v} φ
  have : Limits.PreservesFiniteLimits (T ⋙ SheafOfModules.toSheaf O) := by
    change Limits.PreservesFiniteLimits (SheafOfModules.toSheaf A)
    infer_instance
  have hlim : Limits.PreservesFiniteLimits T :=
    Limits.preservesFiniteLimits_of_reflects_of_preserves T (SheafOfModules.toSheaf O)
  have : Limits.PreservesFiniteColimits (SheafOfModules.toSheaf O) := inferInstance
  have : Limits.PreservesFiniteColimits (T ⋙ SheafOfModules.toSheaf O) := by
    change Limits.PreservesFiniteColimits (SheafOfModules.toSheaf A)
    infer_instance
  have hcolim : Limits.PreservesFiniteColimits T :=
    Limits.preservesFiniteColimits_of_reflects_of_preserves T (SheafOfModules.toSheaf O)
  exact ⟨hlim, hcolim⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Under the cohomology comparison, the derived affine algebra unit is the
underived unit applied to the cohomology module.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
(blueprint: lem-sc-affine-algebra-derived-unit-homology-factorization).

Proof: First take the tensor-derived adjunction of
RingedSpace.derivedModulePullback_adjunction. The flat stalk localizations of g
make its underived tensor pullback exact. Applying an exact functor to kernels
and images gives a natural identification H^n(Lg-star M) with g-star H^n(M).
The latter is quasi-coherent by the affine module correspondence, so Lg-star M
has quasi-coherent cohomology. Exact scalar restriction to O_Y compares Rg-star
with Rf-star: both use the same K-injective resolution and underlying pushed
complex. The affine unbounded cohomology formula, justified by affine vanishing
and the unbounded cohomological bound, identifies H^n(Rg-star Lg-star M) with
 g_* g^* H^n(M). This comparison is natural and compatible with the derived unit:
on a representative and its resolution the unit is induced by the underived
adjunction, and the comparison sends it to the ordinary unit on cohomology.
One may check this on affine opens, where the map sends a module section to
its tensor with 1. These maps agree on restrictions and hence on sheaves.
Uniqueness of left adjoints transports the comparison from tensor pullback to P
and from its derived left adjoint to L, with the adjunction-compatible natural
isomorphisms. Absorb their cohomology components in the target isomorphism e.
This gives the stated equality for a and adj even when these are not the chosen
canonical adjunctions. The argument uses all integer degrees and does not assume
boundedness. Identity morphisms, empty schemes and zero cohomology give the
identity between the respective objects, including the zero objects. -/
theorem affine_algebra_derived_unit_homology_factorization
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    [Limits.PreservesFiniteLimits P]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f))
    (M : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))))
    (hM : directImageAlgebraDerivedQCohProperty f M) (n : ℤ) :
    ∃ e : (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj
          ((RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)).obj
            (L.obj M)) ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj
          (P.obj ((DerivedCategory.homologyFunctor
            (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj M)),
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).map
          (adj.unit.app M) ≫ e.hom =
        a.unit.app ((DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj M) := by
  classical
  let R := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let RD := RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)
  let HA := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n
  let HX := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n
  let : P.Additive := a.left_adjoint_additive
  let : P.IsLeftAdjoint := a.isLeftAdjoint
  let adjD := a.mapDerivedCategoryRightDerivedAdjunction
  let eL : L ≅ P.mapDerivedCategory := adj.leftAdjointUniq adjD
  let eH : HA ⋙ P ≅ L ⋙ HX :=
    P.mapDerivedCategoryHomologyFunctorIso n ≪≫
      Functor.isoWhiskerRight eL.symm HX
  have hLM := affine_algebra_derived_pullback_preserves_qcoh f L adj M hM
  have hR : ∀ K, schemeDerivedQCohProperty X K →
      directImageAlgebraDerivedQCohProperty f (RD.obj K) := by
    let : HasDerivedCategory
        (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) :=
      HasDerivedCategory.standard _
    let T := SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
    obtain ⟨hlim, hcolim⟩ := restriction_exact (moduleRings Y.toRingedSpace)
      (moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
    let := hlim
    let := hcolim
    -- Compare sections to avoid unfolding both functor records in a definitional equality.
    let underived : R ⋙ T ≅ RingedSpace.moduleDirectImage f.toLRSHom.toShHom :=
      NatIso.ofComponents (fun _ ↦
        (SheafOfModules.fullyFaithfulForget _).preimageIso
          (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; ext x; rfl)))
        (by intros; ext U x; rfl)
    let comparison : RD ⋙ T.rightDerivedFunctor ≅ schemeDerivedDirectImage f :=
      Functor.isoWhiskerLeft RD T.rightDerivedFunctorIsoMapDerivedCategory ≪≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso R T).symm ≪≫
        Functor.rightDerivedFunctorNatIso underived
    intro K hK i
    obtain ⟨⟨e⟩, hq⟩ := schemeHigherDirectImage_of_affine f K hK i
    let HY := DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) i
    let c := (T.rightDerivedFunctorHomologyFunctorIso i).app (RD.obj K) ≪≫
      HY.mapIso (comparison.app K) ≪≫ e
    apply ((Scheme.Modules.affine_module_correspondence f).1 _).mpr
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      c.symm hq
  obtain ⟨_, hunit, _⟩ := affine_algebra_module_adjunction_isos f P a
  have hεD : IsIso (adjD.counit.app (L.obj M)) :=
    affine_algebra_exact_derived_counit_isIso f P a (L.obj M) hLM
  have hε : IsIso (adj.counit.app (L.obj M)) := by
    rw [← adj.leftAdjointUniq_hom_app_counit adjD (L.obj M)]
    infer_instance
  have hLu : IsIso (L.map (adj.unit.app M)) := by
    have : IsIso (L.map (adj.unit.app M) ≫ adj.counit.app (L.obj M)) := by
      rw [adj.left_triangle_components M]
      exact ⟨⟨𝟙 _, by simp, by simp⟩⟩
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj M))
  have hPu : IsIso (P.map (HA.map (adj.unit.app M))) := by
    have he := eH.hom.naturality (adj.unit.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
    have : IsIso (P.map (HA.map (adj.unit.app M)) ≫
        eH.hom.app (RD.obj (L.obj M))) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (eH.hom.app (RD.obj (L.obj M)))
  have hu₀ : IsIso (a.unit.app (HA.obj M)) := hunit _ (hM n)
  have hu₁ : IsIso (a.unit.app (HA.obj (RD.obj (L.obj M)))) :=
    hunit _ (hR _ hLM n)
  have hu : IsIso (HA.map (adj.unit.app M)) := by
    have : IsIso (HA.map (adj.unit.app M) ≫
        a.unit.app (HA.obj (RD.obj (L.obj M)))) := by
      have he := a.unit_naturality (HA.map (adj.unit.app M))
      change a.unit.app (HA.obj M) ≫ R.map (P.map (HA.map (adj.unit.app M))) =
        HA.map (adj.unit.app M) ≫ a.unit.app (HA.obj (RD.obj (L.obj M))) at he
      rw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (a.unit.app (HA.obj (RD.obj (L.obj M))))
  refine ⟨(asIso (HA.map (adj.unit.app M))).symm ≪≫
    asIso (a.unit.app (HA.obj M)), ?_⟩
  change HA.map (adj.unit.app M) ≫
    (inv (HA.map (adj.unit.app M)) ≫ a.unit.app (HA.obj M)) = _
  exact IsIso.hom_inv_id_assoc _ _

end AlgebraicGeometry
