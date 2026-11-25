/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
import WeilConjectures.Algebra.Homology.HomotopyCategory.BraidedCochainNormalization

/-! # Braided cochain restriction with normalized tensor and unit

Source: Stacks Project, Tags 06YS, 0G7D, 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-cochain-normalization).
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  RingedDerivedNative.monoidal
  RingedDerivedNative.symmetric HasDerivedCategory.standard SheafOfModules.pushforward

attribute [local instance 20000] instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
  RingedDerivedNative.moduleClosed SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

private theorem restrictionCoproducts
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (hcolim : ∀ (K : Type (max u (t + 1))),
      PreservesColimitsOfShape (Discrete K) (clopenTensorRestriction.{t, u} j R)) :
    ∀ n, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n}))
        (clopenTensorRestriction.{t, u} j R) := by
  intro n
  have := hcolim (ULift.{max u (t + 1)}
    (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n}))
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

/-- Ordinary braided restriction lifts to a braided cochain restriction with the given
summand-normalized inverse tensorator and the ordinary unit in degree zero.

Source: Stacks Project, Tags 06YS, 0G7D, 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-cochain-normalization).

Proof: Transport the given coproduct preservation to the total-degree index types using
ULift. The canonical mapCochainComplexMonoidal construction gives the strong cochain
structure. Apply coproduct extensionality to the two braiding composites: the signed
summand formulas give the same Koszul sign, and the ordinary braided equation identifies
the remaining tensorators. Coproduct extensionality and hsum then identify the inverse
cochain tensorator with b on every degree. The canonical unit of the cochain construction
is the single-complex comparison followed by the single of the ordinary inverse unit.
These computations also hold for the zero ring and empty site. -/
theorem clopen_braided_cochain_normalization
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided)
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
        clopenTensorComplexRestriction.{t, u} j R ≅
      ((clopenTensorComplexRestriction.{t, u} j R).prod
        (clopenTensorComplexRestriction.{t, u} j R)) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology Y)
            ((clopenTensorRings.{t, u} j).obj R))
    (hsum : ∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      (clopenTensorRestriction.{t, u} j R).map
          (clopenTotalTensorSummand.{t, u} R P Q p q n hpq) ≫
          (b.hom.app (P, Q)).f n =
        (clopenTensorComparison.{t, u} j R h (P.X p) (Q.X q)).hom ≫
          clopenTotalTensorSummand.{t, u} ((clopenTensorRings.{t, u} j).obj R)
            ((clopenTensorComplexRestriction.{t, u} j R).obj P)
            ((clopenTensorComplexRestriction.{t, u} j R).obj Q) p q n hpq)
    (hcolim : ∀ (K : Type (max u (t + 1))),
      PreservesColimitsOfShape (Discrete K) (clopenTensorRestriction.{t, u} j R)) :
    ∃ c : (clopenTensorComplexRestriction.{t, u} j R).Braided,
      (∀ P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ,
        c.toMonoidal.toOplaxMonoidal.δ P Q = b.hom.app (P, Q)) ∧
      c.toMonoidal.toOplaxMonoidal.η =
        ((HomologicalComplex.singleMapHomologicalComplex
          (clopenTensorRestriction.{t, u} j R) (.up ℤ) (0 : ℤ)).app
            (𝟙_ (clopenTensorModules.{t, u} R))).hom ≫
          (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map
            (clopenTensorUnitComparison.{t, u} j R h).hom := by
  let F := clopenTensorRestriction.{t, u} j R
  let : F.Braided := h
  have := restrictionCoproducts.{t, u} j R hcolim
  obtain ⟨c, hδ, hη⟩ :=
    CategoryTheory.Functor.OplaxMonoidal.braided_cochain_normalization F
  refine ⟨c, ?_, hη⟩
  intro P Q
  exact hδ P Q (b.hom.app (P, Q)) (fun p q n hpq ↦ hsum P Q p q n hpq)

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
