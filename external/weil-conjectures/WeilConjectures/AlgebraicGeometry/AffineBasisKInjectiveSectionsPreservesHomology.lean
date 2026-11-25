/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme

import WeilConjectures.AlgebraicGeometry.DerivedLowerTruncationCycleFormula
import WeilConjectures.CategoryTheory.LeftExactUpperTruncationComparison
import WeilConjectures.AlgebraicGeometry.AffineBasisDerivedSectionsLowerTailVanishing
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # K-injective section homology from affine-basis acyclicity

Source: Stacks Project, Tag 08C2, singleton cover; Tag 071B, compatible resolution tower.
(blueprint: lem-sc-affine-basis-kinjective-sections-preserves-homology).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem preservesLeftHomology_of_lowerComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]
    (F : CochainComplex C ℤ) [F.IsKInjective] (n : ℤ)
    (hLower : IsIso ((DerivedCategory.homologyFunctor D n).map
      (S.rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj F))))) :
    S.PreservesLeftHomologyOf (F.sc n) := by
  let J := (S.mapHomologicalComplex (.up ℤ)).obj F
  let H := DerivedCategory.homologyFunctor D n
  let h := (F.sc n).homologyData.left
  let e := ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app J).symm ≪≫
    ((DerivedCategory.homologyFunctorFactorsh D n).app
      ((HomotopyCategory.quotient D (.up ℤ)).obj J)).symm
  let U := S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj F)
  let q := S.rightDerivedFunctor.map
    ((DerivedCategory.quotientCompQhIso C).hom.app F ≫
      (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj F))
  have : IsIso (H.map q) := by
    dsimp only [q]
    rw [S.rightDerivedFunctor.map_comp, H.map_comp]
    infer_instance
  obtain ⟨b, hb⟩ := derived_lower_truncation_cycle_formula S F n
  let a : cokernel (S.map h.f') ≅ S.obj h.H :=
    (S.mappedCyclesHomologyData F n).homologyIso.symm ≪≫ e ≪≫
      asIso (H.map U) ≪≫ asIso (H.map q) ≪≫ b
  have hc : cokernel.π (S.map h.f') ≫
      (S.mappedCyclesHomologyData F n).homologyIso.inv =
      (J.sc n).liftCycles (S.map h.i) (by
        change S.map h.i ≫ S.map (F.sc n).g = 0
        rw [← S.map_comp, h.wi, S.map_zero]) ≫ (J.sc n).homologyπ := by
    change (S.mappedCyclesHomologyData F n).π ≫ _ = _
    rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
    apply congrArg (fun z ↦ z ≫ (J.sc n).homologyπ)
    apply (cancel_mono (J.sc n).iCycles).mp
    erw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles,
      ShortComplex.liftCycles_i]
    rfl
  have ha : cokernel.π (S.map h.f') ≫ a.hom = S.map h.π := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, hc]
    simpa only [Category.assoc] using hb
  have hp := cokernel.cokernelIso (S.map h.f') (S.map h.π) a ha
  have hpres : h.IsPreservedBy S :=
    { g := inferInstance
      f' := by
        apply preservesColimit_of_preserves_colimit_cocone h.hπ
        exact (isColimitMapCoconeCoforkEquiv' S h.wπ).symm hp }
  let := hpres
  exact Functor.PreservesLeftHomologyOf.mk' S h

set_option backward.isDefEq.respectTransparency false in
/-- Sections preserve homology of a K-injective complex with acyclic homology
on an affine basis of V.
Source: Stacks Project, Tag 08C2, unbounded comparison via Tag 071B;
Tag 08D4, its tower argument adapted using the basis hypothesis of Tag 071B.
(blueprint: lem-sc-affine-basis-kinjective-sections-preserves-homology).

Proof: The lower-tail vanishing theorem applied in degrees n and n+1, and
the homology exact sequence of the derived truncation triangle, make degree-n
derived sections of QF -> truncGE n QF invertible. The derived lower-truncation
cycle formula identifies the actual image of the homology quotient: it is the
cycle lift followed by the raw-to-derived unit, this truncation projection and
the bottom comparison. The unit is invertible because F is K-injective.
Left exactness gives mappedCyclesHomologyData: its homology object is the
cokernel of the mapped boundary into the mapped cycle kernel. Its comparison
with section homology identifies its cokernel projection with the same cycle
lift. Compose these specified isomorphisms; the cycle formula says the composite
sends that cokernel projection to S of the original homology quotient.
Transport its cokernel universal property along this isomorphism. Together
with preservation of the cycle kernel this preserves the chosen left homology
data, hence all left homology data. The unbounded tower calculation remains
in affineBasisDerivedSections_lowerTail_isZero; the original complex need
not have injective terms, and no term or cokernel acyclicity is introduced.
Empty V and every integer degree obey the same calculation. -/
theorem affineBasisKInjectiveSections_preservesLeftHomology
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F : CochainComplex X.Modules ℤ) [F.IsKInjective]
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1))) (n : ℤ) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    S.PreservesLeftHomologyOf (F.sc n) := by
  dsimp only
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  let t := DerivedCategory.TStructure.t (C := C)
  let T := S.rightDerivedFunctor.mapTriangle.obj ((t.triangleLTGE n).obj
    (DerivedCategory.Q.obj F))
  have hT : T ∈ distTriang _ :=
    S.rightDerivedFunctor.map_distinguished _
      (t.triangleLTGE_distinguished n (DerivedCategory.Q.obj F))
  have hz (i : ℤ) (hi : n ≤ i) :
      IsZero ((DerivedCategory.homologyFunctor D i).obj T.obj₁) :=
    affineBasisDerivedSections_lowerTail_isZero X V hV F hhomology n i hi
  have hLower : IsIso ((DerivedCategory.homologyFunctor D n).map T.mor₂) :=
    DerivedCategory.isIso_homologyMap_mor₂ T hT n (n + 1) rfl
      (hz n le_rfl) (hz (n + 1) (by omega))
  exact preservesLeftHomology_of_lowerComparison S F n hLower

end AlgebraicGeometry
