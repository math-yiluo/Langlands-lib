/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparisonAlpha
import WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparisonBeta

/-!
# Finite ordered Čech comparison for flasque resolutions

Source: Stacks Project, Cohomology, Tags 09SZ, 01ET, 01EQ, 01FJ and 01FM.
(auxiliary; not a blueprint node)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The finite ordered Čech comparison, including componentwise naturality.
Source: Stacks Project, Cohomology, Tags 09SZ, 01ET, 01EQ, 01FJ and 01FM.
(auxiliary; not a blueprint node)

Proof: The flasque row augmentation follows from the source library's full Čech
exactness theorem, the ordered/usual restriction homotopy equivalence, and degree-zero
sheaf gluing. Negative coefficient rows vanish. Only the finitely many Čech columns
0,...,r-1 can be nonzero, so finite-strip row augmentation gives alpha.
Construct beta with its prescribed resolution-degree-zero components. The cochain
identity for e kills its vertical differential, and restriction naturality supplies
its horizontal cochain identity. Each vertical column is a finite product of section
complexes. Restriction of scalars and these products preserve the stipulated
quasi-isomorphisms; finite-column comparison gives quasi-isomorphism of totals.
The total of the single coefficient complex is isomorphic to its Čech complex,
and naturality identifies the resulting composite with beta. Naturality of global
restriction proves degree-zero agreement. For the final square, push the second
augmentation forward, transport its single-complex source through the canonical
functor isomorphism, and apply beta naturality and the existing alpha naturality.
All component formulas also hold for empty tuples and the empty cover.
-/
theorem finiteOrderedFlasqueCechComparison
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : (HomologicalComplex.single (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (.up ℤ) 0).obj F ⟶ G)
    [QuasiIso e] [G.IsStrictlyGE 0]
    (hfl : ∀ q : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (G.X (q : ℤ))))
    (r : ℕ) (V : Fin r → X.Opens) (hcover : iSup V = ⊤)
    (hsections : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      QuasiIso (((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj
          (op (alternatingCechIntersection V t))).mapHomologicalComplex (.up ℤ)).map e)) :
    QuasiIso (alternatingCechAugmentationMap V G) ∧
    ∃ β : (alternatingCechModuleFunctor V).obj F ⟶ (alternatingCechTotalFunctor V).obj G,
      (∀ n : ℤ, β.f n = ((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
        ((alternatingCechDoubleFunctor V).obj G).ιTotal (.up ℤ) n 0 n (Int.add_zero n)) ∧
      QuasiIso β ∧
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (e.f 0) ≫
          (alternatingCechAugmentationMap V G).f 0 = alternatingCechZero V F ≫ β.f 0 ∧
      ∀ (Y : Scheme.{u}) (h : Y ⟶ X) (F' : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
        (G' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (e' : (HomologicalComplex.single (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (.up ℤ) 0).obj F' ⟶ G') [QuasiIso e'] [G'.IsStrictlyGE 0]
        (u : F ⟶ ((Scheme.Modules.pushforward h).obj F'))
        (v : G ⟶ (((Scheme.Modules.pushforward h).mapHomologicalComplex (.up ℤ)).obj G')),
        e.f 0 ≫ v.f 0 = u ≫ (Scheme.Modules.pushforward h).map (e'.f 0) →
        ∃ β' : (alternatingCechModuleFunctor V).obj ((Scheme.Modules.pushforward h).obj F') ⟶
            (alternatingCechTotalFunctor V).obj
              (((Scheme.Modules.pushforward h).mapHomologicalComplex (.up ℤ)).obj G'),
          (∀ n : ℤ, β'.f n =
            ((alternatingCechModuleFunctor V).map
              ((Scheme.Modules.pushforward h).map (e'.f 0))).f n ≫
            ((alternatingCechDoubleFunctor V).obj
              (((Scheme.Modules.pushforward h).mapHomologicalComplex (.up ℤ)).obj G')).ιTotal
              (.up ℤ) n 0 n (Int.add_zero n)) ∧
          β ≫ (alternatingCechTotalFunctor V).map v =
            (alternatingCechModuleFunctor V).map u ≫ β' ∧
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (.up ℤ)).map v ≫ alternatingCechAugmentationMap V
              (((Scheme.Modules.pushforward h).mapHomologicalComplex (.up ℤ)).obj G') =
              alternatingCechAugmentationMap V G ≫ (alternatingCechTotalFunctor V).map v := by
  refine ⟨finiteOrderedFlasqueCechComparison_alpha X G hfl r V hcover,
    orderedCechCoefficientMap V e, fun _ ↦ rfl,
    orderedCechCoefficientMap_quasiIso X F G e r V hsections,
    orderedCechCoefficientMap_zero V e, ?_⟩
  intro Y h F' G' e' _ _ u v huv
  let H := Scheme.Modules.pushforward h
  let eH := ((H.mapHomologicalComplex (.up ℤ)).map e')
  let a := (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).inv.app F'
  let e'' := a ≫ eH
  have he : e''.f 0 = H.map (e'.f 0) := by
    change ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).inv.app F').f 0 ≫
      H.map (e'.f 0) = H.map (e'.f 0)
    rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    change (𝟙 _) ≫ H.map (𝟙 _) ≫ H.map (e'.f 0) = H.map (e'.f 0)
    erw [Category.id_comp, H.map_id]
    exact Category.id_comp _
  refine ⟨orderedCechCoefficientMap V e'', ?_, ?_, ?_⟩
  · intro n
    change ((alternatingCechModuleFunctor V).map (e''.f 0)).f n ≫ _ = _
    rw [he]
  · apply orderedCechCoefficientMap_naturality V e e'' u v
    simpa only [he] using huv
  · exact alternatingCechAugmentation_naturality V G _ v

end AlgebraicGeometry
