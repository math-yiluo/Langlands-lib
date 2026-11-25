/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization

/-! # Unit normalization of native braided restriction

Source: Stacks Project, Tags 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-unit-square).
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  RingedDerivedNative.monoidal RingedDerivedNative.symmetric
  HasDerivedCategory.standard SheafOfModules.pushforward

attribute [local instance 20000] instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
  RingedDerivedNative.moduleClosed SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

namespace CategoryTheory

open Category Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverse_unit_square_aux
    {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory D] [MonoidalCategory E]
    (Q : A ⥤ D) (L : B ⥤ E) (F : A ⥤ B) (G : D ⥤ E)
    [Q.LaxMonoidal] [L.LaxMonoidal] [F.Monoidal] [G.Monoidal]
    (e : Q ⋙ G ≅ F ⋙ L) [NatTrans.IsMonoidal e.hom] [IsIso (ε L)]
    {M : B} (a : F.obj (𝟙_ A) ⟶ M) (b : M ⟶ 𝟙_ B) (hF : η F = a ≫ b) :
    η G = G.map (ε Q) ≫ e.hom.app (𝟙_ A) ≫ L.map a ≫ L.map b ≫ inv (ε L) := by
  rw [← L.map_comp_assoc, ← hF]
  have hh := NatTrans.IsMonoidal.unit (τ := e.hom)
  simp only [comp_ε, Category.assoc] at hh
  apply (cancel_epi (ε G)).1
  rw [Functor.Monoidal.ε_η, reassoc_of% hh]
  rw [← L.map_comp_assoc, Functor.Monoidal.ε_η, L.map_id, id_comp, IsIso.hom_inv_id]

end CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

/-- Expand the specified unit isomorphism without unfolding it in the cancellation proof. -/
private theorem unitComparison_hom_aux
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided) :
    (unitComparison.{t, u} j R h).hom =
      (derivedRestriction.{t, u} j R).map
        (RingedDerivedNative.unitIso.{t + 1, t, u, max (u + 1) (t + 2)}
          (topology X) R).hom ≫
      (factors.{t, u} j R).hom.app
        (𝟙_ (CochainComplex (clopenTensorModules.{t, u} R) ℤ)) ≫
      DerivedCategory.Q.{max (u + 1) (t + 2)}.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (clopenTensorRestriction.{t, u} j R) (.up ℤ) (0 : ℤ)).app
            (𝟙_ (clopenTensorModules.{t, u} R))).hom ≫
      DerivedCategory.Q.{max (u + 1) (t + 2)}.map
        ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map
          (clopenTensorUnitComparison.{t, u} j R h).hom) ≫
      (RingedDerivedNative.unitIso.{t + 1, t, u, max (u + 1) (t + 2)}
        (topology Y) ((clopenTensorRings.{t, u} j).obj R)).inv := by
  rfl

/-- The inverse unit of derived restriction is the canonical degree-zero comparison.
Source: Stacks Project, Tags 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-unit-square).

Proof: the unit equation for the monoidal factorization identifies the composite of
localization and restriction unit maps. Cancel the invertible derived restriction unit
and the target localization unit. Substitute the supplied single-complex description
of the cochain inverse unit. Applying localization to its two factors, and associating
composites, gives precisely the five factors defining unitComparison. Equality of the
hom maps gives equality of the unit isomorphisms. No K-flatness, flatness, boundedness,
nonzero coefficient, or nonempty scheme hypothesis is needed for the unit equation. -/
theorem clopen_braided_unit_square
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided)
    (c : (clopenTensorComplexRestriction.{t, u} j R).Braided)
    (hcη : c.toMonoidal.toOplaxMonoidal.η =
      ((HomologicalComplex.singleMapHomologicalComplex
        (clopenTensorRestriction.{t, u} j R) (.up ℤ) (0 : ℤ)).app
          (𝟙_ (clopenTensorModules.{t, u} R))).hom ≫
        (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map
          (clopenTensorUnitComparison.{t, u} j R h).hom)
    (d : (derivedRestriction.{t, u} j R).Braided) :
    letI := c
    letI := d
    letI := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology X) R
    letI := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology Y) ((clopenTensorRings.{t, u} j).obj R)
    NatTrans.IsMonoidal (factors.{t, u} j R).hom →
      braidedUnit.{t, u} j R d = unitComparison.{t, u} j R h := by
  intro he
  let := c
  let := d
  let := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
    (topology X) R
  let := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
    (topology Y) ((clopenTensorRings.{t, u} j).obj R)
  apply Iso.ext
  have hεY := RingedDerivedNative.isIso_ε.{t + 1, t, u, max (u + 1) (t + 2)}
    (topology Y) ((clopenTensorRings.{t, u} j).obj R)
  have hu := CategoryTheory.inverse_unit_square_aux
    (Q := DerivedCategory.Q.{max (u + 1) (t + 2)})
    (L := DerivedCategory.Q.{max (u + 1) (t + 2)})
    (F := clopenTensorComplexRestriction.{t, u} j R)
    (G := derivedRestriction.{t, u} j R)
    (e := factors.{t, u} j R)
    ((HomologicalComplex.singleMapHomologicalComplex
      (clopenTensorRestriction.{t, u} j R) (.up ℤ) (0 : ℤ)).app
        (𝟙_ (clopenTensorModules.{t, u} R))).hom
    ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map
      (clopenTensorUnitComparison.{t, u} j R h).hom) hcη
  rw [unitComparison_hom_aux]
  dsimp only [braidedUnit, Iso.symm_hom, RingedDerivedNative.unitIso_inv,
    Functor.Monoidal.εIso_inv, RingedDerivedNative.unitIso,
    asIso_hom, asIso_inv, Iso.app_hom]
  exact hu

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
