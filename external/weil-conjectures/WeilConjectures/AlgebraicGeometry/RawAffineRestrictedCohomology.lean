/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Restricted single-complex cohomology and its canonical maps

Source: Stacks Project, Tags 03Q8 and 0EZM.
(blueprint: def-sbc-raw-affine-restricted-cohomology).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Canonical cohomology pullback on an actual complex, using the derived adjunction unit.
Source: Stacks Project, Tag 0EZM.
(blueprint: def-sbc-raw-affine-restricted-cohomology). -/
noncomputable def rawAffineComplexPullback (p : ℤ) {X Y : Scheme.{v}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    (cohomology AddCommGrpCat.{v + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{v + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{v + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{v + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} X).map
          ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryFactors.hom.app K))

/-- Cohomology of a sheaf restricted to the etale scheme `U ×_S Y`, in degree zero
as a complex. No raw derived-Hom group occurs in this definition.
(blueprint: def-sbc-raw-affine-restricted-cohomology). -/
noncomputable def rawAffineRestrictedCohomology {S Y : Scheme.{v}} (h : Y ⟶ S)
    (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : S.Etale) :
    AddCommGrpCat.{v + 1} :=
  (cohomology AddCommGrpCat.{v + 1} (Limits.pullback U.hom h) (p : ℤ)).obj
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)).obj F)))

/-- The map between the restricted schemes induced by a triangle over `S`.
(blueprint: def-sbc-raw-affine-restricted-cohomology). -/
noncomputable def rawAffineRestrictedMap {S Y Y' : Scheme.{v}} (a : Y' ⟶ Y)
    (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (U : S.Etale) :
    Limits.pullback U.hom h' ⟶ Limits.pullback U.hom h :=
  Limits.pullback.map U.hom h' U.hom h (𝟙 _) a (𝟙 _) (by simp) (by simpa using w.symm)

/-- Restriction of a coefficient map to the pullback triangle, with both inverse-image
composition comparisons written explicitly.
(blueprint: def-sbc-raw-affine-restricted-cohomology). -/
noncomputable def rawAffineRestrictedCoefficient {S Y Y' : Scheme.{v}} (a : Y' ⟶ Y)
    (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale) :
    (upperStar AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)).obj
      ((upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)).obj F) ⟶
    (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h')).obj F' := by
  let q := rawAffineRestrictedMap a h h' w U
  let r := Limits.pullback.snd U.hom h
  let r' := Limits.pullback.snd U.hom h'
  have hw : r' ≫ a = q ≫ r := by simp [q, r, r', rawAffineRestrictedMap]
  exact (upperStarComp AddCommGrpCat.{v + 1} q r).inv.app F ≫
    (upperStarComp AddCommGrpCat.{v + 1} r' a (q ≫ r) hw.symm).hom.app F ≫
      (upperStar AddCommGrpCat.{v + 1} r').map φ

/-- Canonical restricted-cohomology map: derived pullback followed by the restricted
coefficient map. This definition uses neither continuity nor raw derived Hom.
(blueprint: def-sbc-raw-affine-restricted-cohomology). -/
noncomputable def rawAffineRestrictedCohomologyMap {S Y Y' : Scheme.{v}} (a : Y' ⟶ Y)
    (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale) :
    rawAffineRestrictedCohomology h p F U ⟶ rawAffineRestrictedCohomology h' p F' U := by
  let q := rawAffineRestrictedMap a h h' w U
  let R := (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)).obj F
  exact rawAffineComplexPullback (p : ℤ) q ((CochainComplex.singleFunctor _ 0).obj R) ≫
    (cohomology AddCommGrpCat.{v + 1} (Limits.pullback U.hom h') (p : ℤ)).map
      (DerivedCategory.Q.map
        (((upperStar AddCommGrpCat.{v + 1} q).mapCochainComplexSingleFunctor 0).hom.app R ≫
          (CochainComplex.singleFunctor _ 0).map
            (rawAffineRestrictedCoefficient a h h' w F F' φ U)))

end AlgebraicGeometry.Etale
