/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerCanonicalReduction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBoundedFreeCone
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

set_option linter.privateModule false

/-! # Finite reduction of the projection from a normalized tower limit

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, finite-reduction paragraph.
(blueprint: lem-sp-tower-projection-finite-reduction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

private theorem completed_derived_products :
    Nonempty (HasLimitsOfShape (Discrete ℕ)
      (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))) := by
  let A := WeilConjectures.scalarReductionSource.{u, u} l E T
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T
  let : CountableAB4Star A := by
    constructor
    intro I _
    have : (lim : (Discrete I ⥤ A) ⥤ A).PreservesEpimorphisms := by
      constructor
      intro B C f hf
      let eB := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))
      let eC := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := C))
      have h (i : I) : Epi (f.app ⟨i⟩) := inferInstance
      have : Epi (Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩)) :=
        (Scheme.ProEt.countableProducts_exact.{u, u, 0} T R).2.2 I _ _ _ h
      have hh : lim.map f = eB.hom ≫ Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ eC.inv := by
        apply limit.hom_ext
        rintro ⟨i⟩
        dsimp only [eB, eC]
        simp only [Category.assoc, HasLimit.isoOfNatIso_inv_π,
          Discrete.natIsoFunctor_inv_app]
        change lim.map f ≫ limit.π C ⟨i⟩ =
          (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))).hom ≫
            Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ Pi.π _ i
        rw [Pi.map_π, HasLimit.isoOfNatIso_hom_π_assoc]
        simp
      rw [hh]
      infer_instance
    exact hasExactLimitsOfShape_of_preservesEpi (C := A) (Discrete I)
  obtain ⟨hP, _⟩ := derivedCategory_countableProducts_core.{0} A
  let := hP
  exact ⟨inferInstance⟩

end AlgebraicGeometry.ProEtale
