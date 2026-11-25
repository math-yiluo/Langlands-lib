/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.AffineRestrictedHomologySupport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Spectrum.Prime.Module
/-! # Elementwise torsion for an affine model of a supported target

Source: Stacks Project, Tag 08EJ, affine support paragraph, and Tag 06Z0.
(blueprint: new-affine-open-supported-model-torsion).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
private theorem torsion_of_localized_subsingleton {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R)
    (h : Subsingleton (LocalizedModule.Away f M)) (m : M) :
    ∃ n : ℕ, f ^ n • m = 0 := by
  obtain ⟨r, hr, hm⟩ := LocalizedModule.subsingleton_iff.mp h m
  rcases hr with ⟨n, rfl⟩
  exact ⟨n, hm⟩

/-- Vanishing away from the zero locus implies power annihilation on affine cohomology.
Source: Stacks Project, Tag 08EJ, affine support paragraph, and Tag 06Z0.
(blueprint: new-affine-open-supported-model-torsion).

Proof: Fix i and put N = H^i(M). Compare F with affine derived tilde followed by
canonical affine-site transport: the two comparisons after Q lift to a natural
isomorphism by localization. Exactness of tilde identifies the transported sheaf
of N with H^i(F(M)). Apply homology to hM and undo affine-site transport; exact
open restriction and its stalk isomorphism identify this sheaf with the affine
restriction of H^i(E'[k]). The homology shift isomorphism identifies its stalks
with stalks of H^(i+k)(E'). Compatibility of f with restriction and the affine
chart identifies D(f|U) with the points of U outside the global V(f). Hence the
sheaf of N has zero stalks there. Tilde stalks are prime localizations of N,
so Module.notMem_support_iff gives disjointness of D(f|U) and Module.support A N.
LocalizedModule.subsingleton_iff_disjoint makes the localization at powers of
f|U zero. For m, its localization equals zero; the localization equality criterion
provides a power (f|U)^n annihilating m. The exponent may depend on m and i.
For f=0, n=1 works; for a unit f, N is zero; for empty U, A and N are zero.
No finite generation, boundedness, or perfectness is needed. -/
theorem affine_open_supported_model_torsion
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E' : schemeDerivedQCohCategory X)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ)
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (X.sheaf.obj.obj (op U)))]
    (F : DerivedCategory (ModuleCat.{u} (X.sheaf.obj.obj (op U))) ⥤
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
    (hF : Nonempty (DerivedCategory.Q ⋙ F ≅
      (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q))
    (M : DerivedCategory (ModuleCat.{u} (X.sheaf.obj.obj (op U))))
    (hM : Nonempty (F.obj M ≅
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (E'.obj⟦k⟧))) :
    ∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (X.sheaf.obj.obj (op U))) i).obj M),
      ∃ n : ℕ, (f.val (op U)) ^ n • m = 0 := by
  let A := X.presheaf.obj (op U)
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    inferInstanceAs (HasDerivedCategory.{u + 1}
      (ModuleCat.{u} (X.sheaf.obj.obj (op U))))
  let S := SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let rF := Modules.restrictFunctor hU.isoSpec.hom
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let e : S ≌ (U : Scheme.{u}).Modules := CategoryTheory.Equivalence.mk rF rG
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp [A]) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  let E : S ≌ D := e.trans (Modules.overEquiv U).symm
  have : HasBinaryBiproducts S := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasBinaryBiproducts D := HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts E.functor :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : E.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let T := tilde.functor A
  have : T.IsLeftAdjoint := (tilde.adjunction (R := A)).isLeftAdjoint
  have : PreservesFiniteLimits T := tilde_preserves_finite_limits A
  have : T.Additive := inferInstanceAs (tilde.functor A).Additive
  have : PreservesFiniteLimits (T ⋙ E.functor) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (T ⋙ E.functor) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (affinePerfectSheafification X U hU) :=
    inferInstanceAs (PreservesFiniteLimits (T ⋙ E.functor))
  have : PreservesFiniteColimits (affinePerfectSheafification X U hU) :=
    inferInstanceAs (PreservesFiniteColimits (T ⋙ E.functor))
  have : (affinePerfectSheafification X U hU).Additive :=
    inferInstanceAs (T ⋙ E.functor).Additive
  obtain ⟨α⟩ := hF
  let β : F ≅ (affinePerfectSheafification X U hU).mapDerivedCategory.{u + 1, w} :=
    Localization.liftNatIso (DerivedCategory.Q (C := ModuleCat.{u} A))
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))
      (DerivedCategory.Q ⋙ F)
      ((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)
      F (affinePerfectSheafification X U hU).mapDerivedCategory.{u + 1, w} α
  obtain ⟨γ⟩ := hM
  intro i m
  let H := DerivedCategory.homologyFunctor D i
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M
  let δ : (affinePerfectSheafification X U hU).obj N ≅
      H.obj ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
          (E'.obj⟦k⟧)) :=
    (Functor.mapDerivedCategoryHomologyFunctorIso.{u + 1, u + 1, u, u, u + 1, w}
      (affinePerfectSheafification X U hU) i).app M ≪≫
      H.mapIso (β.app M).symm ≪≫ H.mapIso γ
  have hd := affine_restricted_homology_support X f E' hSupport U hU k i N ⟨δ⟩
  have hz : Subsingleton (LocalizedModule.Away (R := (A : Type u)) (f.val (op U)) N) :=
    LocalizedModule.subsingleton_iff_disjoint.mpr hd
  exact torsion_of_localized_subsingleton (R := (A : Type u)) (f.val (op U)) hz m
end AlgebraicGeometry.Scheme
