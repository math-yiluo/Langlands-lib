/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSplitLineCoordinates

/-! # Recovering the lower exchange coordinate from a split unit -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- A split unit and its split image force invertibility of the lower matrix entry.

Source: the unit/Chern matrix argument, diagonal coefficients (3)
(blueprint: lem-diagonal-exchange-line-coordinate).

Proof: the unit has zero projection to the second summand. Its first coordinate
is split injective and hence invertible by the line hypothesis. Thus the chosen
first component equals the unit precomposed with that inverse. Applying the
additive functor and composing with exchange makes it split injective, since the
unit composite with exchange is split injective. Its target second coordinate
vanishes as well. Apply the rank-one coordinate argument at the target. -/
theorem exchangeLineCoordinate_isIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) {A B K : C} {A' B' K' : D}
    (a : A ⟶ K) (b : B ⟶ K) [IsIso (biprod.desc a b)]
    (a' : A' ⟶ K') (b' : B' ⟶ K') [IsIso (biprod.desc a' b')]
    (t : K ⟶ B) (t' : K' ⟶ B')
    (hat : a ≫ t = 0) (hbt : b ≫ t = 𝟙 B)
    (hat' : a' ≫ t' = 0) (hbt' : b' ≫ t' = 𝟙 B')
    (u : A ⟶ K) [IsSplitMono u] (hu : u ≫ t = 0)
    (e : F.obj K ⟶ K') [IsSplitMono (F.map u ≫ e)]
    (hz : F.map a ≫ e ≫ t' = 0) (i : F.obj A ≅ A')
    (hline : ∀ q : End A, IsSplitMono q.asHom → IsIso q.asHom)
    (hline' : ∀ q : End A', IsSplitMono (q).asHom → IsIso (q).asHom) :
    IsIso (F.map a ≫ e ≫ inv (biprod.desc a' b') ≫ biprod.fst) := by
  let d := u ≫ inv (biprod.desc a b) ≫ biprod.fst
  have : IsIso d := splitLineCoordinate_isIso a b t hat hbt u hu (Iso.refl A) hline
  have hfactor : u = d ≫ a := by
    simpa only [hu, zero_comp, add_zero, d] using coordinates a b t hat hbt u
  have hunit : a = inv d ≫ u := by
    rw [hfactor]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hs : IsSplitMono (F.map a ≫ e) := by
    rw [hunit, F.map_comp, Category.assoc]
    infer_instance
  simpa only [Category.assoc] using
    splitLineCoordinate_isIso a' b' t' hat' hbt' (F.map a ≫ e)
      (by simpa only [Category.assoc] using hz) i hline'

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
