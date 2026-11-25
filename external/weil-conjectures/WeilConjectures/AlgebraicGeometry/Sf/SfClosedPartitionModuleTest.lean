/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientModulePullbackComposition
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.AlgebraicGeometry.SixFunctors.NoetherianComplementaryStratifications

/-!
# Closed-side partitions and pro-etale module restrictions

## References

* Stacks Project, Tags 02V0, 01OW, 01OZ, 04ZA and 03D8
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

private theorem constant_zero_over_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (V : Y.ProEt) :
    IsZero (proEtaleConstantModuleSheafOver Y A V
      (0 : ModuleCat.{u + 1} (ULift.{u + 1} A))) := by
  let R : Sheaf ((ProEt.topology Y).over V)
      RingCat.{u + 1} := ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} A)))).over V
  let α : ((Functor.const (Over V)ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)) ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⟶ R.obj :=
    Functor.whiskerLeft (Over.forget V).op
    (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have : Presheaf.IsLocallyInjective _ α := (proEtaleConstantRingUnit_over_locallyBijective Y A V).1
  have : Presheaf.IsLocallySurjective _ α :=
    (proEtaleConstantRingUnit_over_locallyBijective Y A V).2
  let F := PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} (R := R) α
  have : F.IsLeftAdjoint :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1} (R := R) α).isLeftAdjoint
  have hz : IsZero (proEtaleConstantModulePresheaf (Over V) A
      (0 : ModuleCat.{u + 1} (ULift.{u + 1} A))) := by
    rw [IsZero.iff_id_eq_zero]
    ext W x
    change x = 0
    have : Subsingleton (0 : ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    exact @Subsingleton.elim (0 : ModuleCat.{u + 1} (ULift.{u + 1} A)) this x 0
  exact F.map_isZero hz

private theorem locallyConstant_of_iso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hG : IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} Y A G) :
    IsLocallyConstantProEtaleModuleSheaf Y A F := by
  obtain ⟨I, V, f, hf, h⟩ := hG
  refine ⟨I, V, f, hf, ?_⟩
  intro a
  obtain ⟨M, _, ⟨eM⟩⟩ := h a
  exact ⟨M, ⟨(SheafOfModules.overFunctor _ (V a)).mapIso e ≪≫ eM⟩⟩

private theorem locallyConstant_of_isZero {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {F : proEtaleRingModules Y (proEtaleConstantRing Y A)} (hF : IsZero F) :
    IsLocallyConstantProEtaleModuleSheaf Y A F := by
  refine ⟨PUnit.{u + 2}, fun _ ↦ ProEt.mk (𝟙 Y), fun _ ↦ 𝟙 _, ?_, ?_⟩
  · simpa only [Presieve.ofArrows_pUnit] using
      (Precoverage.mem_coverings_of_isIso (J := ProEt.precoverage Y) (𝟙 (ProEt.mk (𝟙 Y))))
  · intro a
    refine ⟨0, ⟨?_⟩⟩
    apply IsZero.iso ?_ (constant_zero_over_isZero Y A _)
    rw [IsZero.iff_id_eq_zero]
    ext W x
    exact congrArg (fun k : F ⟶ F ↦ k.val.app (Opposite.op W.unop.left) x)
      ((IsZero.iff_id_eq_zero F).mp hF)

private theorem finite_stalk_of_isZero {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {F : proEtaleRingModules Y (proEtaleConstantRing Y A)} (hF : IsZero F)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F) := by
  have hz := (geometricRingModuleStalkFunctor y (proEtaleConstantRing Y A)).map_isZero hF
  have : Subsingleton (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  infer_instance

end AlgebraicGeometry.Scheme
