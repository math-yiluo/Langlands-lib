/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
import WeilConjectures.AlgebraicGeometry.AdicResidueCechQuotientCone
import WeilConjectures.AlgebraicGeometry.AdicResidueCompletionModel
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The normalized quotient cone of a complete object

Source: Stacks Project, Tags 099M, 0940 and 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/-- A complete object has the quotient homotopy-limit cone, with its actual adjunction units.
Source: Stacks Project, Algebraization Tag 099M; Cohomology on Sites Tags 0940 and 0941;
proetale.tex, Tag 09C6, passage from the reductions to the complete object.
(auxiliary; not a blueprint node).

Proof: choose a flat-term K-flat representative of M and take its termwise quotient tower,
with scalar actions retained. Exact restriction of scalars realizes this as a tower over
B. Its unit is m mapped to m tensor 1, including sheafification. The universal derived
scalar extension is left adjoint to exact restriction, by resolving that ordinary scalar
adjunction. The inverse image of its unit is therefore the identity after reduction.
The composition comparisons are the unique normalized balancing maps, so adjunction
naturality identifies the successor map with adicResidueHomStep after conjugation.
Apply total right derived inverse limit to the strict quotient tower. Exact countable
products on the pro-etale slice give its Roos triangle. The quotient-completion reflector
identifies this unit with the local completeness unit. Since M is complete, the unit is
invertible; transport the cone and Roos triangle along it so the cone point is M itself.
The leg equality is the unit equality before transport. There is no choice of a compatible
family of maps, and no perfectness, boundedness, or Mittag-Leffler condition is used. -/
theorem adicResidue_complete_reduction_cone
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (_hM : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) M) :
    ∃ (F : ℕᵒᵖ ⥤ AdicResidueLocalDerived.{u, v} X J U) (c : Cone F)
      (eM : c.pt ≅ M)
      (e : ∀ n : ℕ, F.obj (op n) ≅
        (CategoryTheory.ConstantCompletion.dres.{max v (u + 1)}
          (adicResidueLocalProjection.{u, v} X J U n)).obj
          ((adicResidueLocalReduction.{u, v} X J U n).obj M))
      (adj : ∀ n : ℕ, adicResidueLocalReduction.{u, v} X J U n ⊣
        CategoryTheory.ConstantCompletion.dres.{max v (u + 1)}
          (adicResidueLocalProjection.{u, v} X J U n)),
      Pretriangulated.IsHomotopyLimit c ∧
      (∀ n : ℕ, c.π.app (op n) ≫ (e n).hom = eM.hom ≫ (adj n).unit.app M) ∧
      (∀ (T : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ)
        (f : (adicResidueLocalReduction.{u, v} X J U (n + 1)).obj T ⟶
          (adicResidueLocalReduction.{u, v} X J U (n + 1)).obj M),
        (adj (n + 1)).homEquiv T _ f ≫ (e (n + 1)).inv ≫
            F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
          (adj n).homEquiv T _ (adicResidueHomStep.{u, v} X J U T M n f)) := by
  obtain ⟨K, ε, hK, hi⟩ := adicResidueCompletionModel_exists.{u, v} X J U
  obtain ⟨π, hlim, hπ⟩ := adicResidue_cech_quotient_cone.{u, v} X J U M K ε hK
  let R := (CategoryTheory.ConstantCompletion.completed
    (coefficientProEtaleModelTopology.{u, v} X) A J).over U
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod R)
  let η := ringedCechCompletionUnit R K ε M
  have : IsIso η := hi M _hM
  let c : Cone (adicResidueAdjointTower.{u, v} X J U M) := ⟨_, π⟩
  let eM : c.pt ≅ M := (asIso η).symm
  refine ⟨adicResidueAdjointTower.{u, v} X J U M, c, eM,
    fun _ ↦ Iso.refl _, adicResidueScalarAdjunction.{u, v} X J U, hlim, ?_, ?_⟩
  · intro n
    apply (cancel_epi η).1
    simpa only [c, eM, η, R, Category.assoc, Iso.symm_hom, asIso_inv,
      IsIso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id] using hπ n
  · intro T n f
    simp only [Iso.refl_inv, Iso.refl_hom, adicResidueAdjointTower,
      Functor.ofOpSequence_map_homOfLE_succ]
    change (adicResidueScalarAdjunction.{u, v} X J U (n + 1)).homEquiv T _ f ≫
      (𝟙 _ ≫ (adicResidueAdjointStep.{u, v} X J U M n ≫ 𝟙 _)) = _
    rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]
    exact adicResidueAdjointStep_transpose.{u, v} X J U T M n f

end AlgebraicGeometry.Scheme
