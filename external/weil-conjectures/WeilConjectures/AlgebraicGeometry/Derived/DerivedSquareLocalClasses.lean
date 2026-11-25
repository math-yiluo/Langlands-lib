/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClassModels
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareUnitMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

import WeilConjectures.AlgebraicGeometry.Square.SquareResolutionLocalClass
import WeilConjectures.AlgebraicGeometry.Square.SquareLocalHypercohomology
import WeilConjectures.AlgebraicGeometry.Square.SquareLocalClassNaturality

/-! # Local classes of the ordinary-unit map in a square

Source: Stacks Project, Cohomology, Tags 01E4, 01FB, 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-derived-square-local-classes).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
set_option synthInstance.maxSize 128 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_class_pasting {C : Type*} [Category C]
    {A B D E F G L M N O P : C}
    (s : A ⟶ D) (c : A ⟶ L) (t : L ⟶ B) (x : B ⟶ D) (y : D ⟶ B)
    (a : B ⟶ E) (p : L ⟶ M) (b : M ⟶ E) (e : E ⟶ F)
    (l : M ⟶ N) (r : N ⟶ F) (i : N ⟶ O) (t' : O ⟶ F)
    (j : F ⟶ G) (m : A ⟶ P) (c' : P ⟶ O) (s' : P ⟶ G)
    (hs : s = c ≫ t ≫ x) (ht : s' = c' ≫ t' ≫ j)
    (hx : x ≫ y = 𝟙 B) (hn : p ≫ b = t ≫ a)
    (he : b ≫ e = l ≫ r) (hi : r = i ≫ t')
    (hr : c ≫ p ≫ l ≫ i = m ≫ c') :
    s ≫ (y ≫ a ≫ e ≫ j) = m ≫ s' := by
  calc
    _ = (c ≫ t ≫ x) ≫ (y ≫ a ≫ e ≫ j) := by
      exact congrArg (fun z ↦ z ≫ (y ≫ a ≫ e ≫ j)) hs
    _ = c ≫ t ≫ (x ≫ y) ≫ a ≫ e ≫ j := by
      simp only [Category.assoc]
    _ = c ≫ t ≫ a ≫ e ≫ j := by rw [hx]; simp only [Category.id_comp]
    _ = c ≫ (t ≫ a) ≫ e ≫ j := by simp only [Category.assoc]
    _ = c ≫ (p ≫ b) ≫ e ≫ j := congrArg (fun z ↦ c ≫ z ≫ e ≫ j) hn.symm
    _ = c ≫ p ≫ (b ≫ e) ≫ j := by simp only [Category.assoc]
    _ = c ≫ p ≫ (l ≫ r) ≫ j := congrArg (fun z ↦ c ≫ p ≫ z ≫ j) he
    _ = c ≫ p ≫ (l ≫ (i ≫ t')) ≫ j := congrArg (fun z ↦ c ≫ p ≫ (l ≫ z) ≫ j) hi
    _ = (c ≫ p ≫ l ≫ i) ≫ t' ≫ j := by simp only [Category.assoc]
    _ = (m ≫ c') ≫ t' ≫ j := congrArg (fun z ↦ z ≫ t' ≫ j) hr
    _ = m ≫ (c' ≫ t' ≫ j) := by simp only [Category.assoc]
    _ = m ≫ s' := congrArg (fun z ↦ m ≫ z) ht.symm

namespace AlgebraicGeometry
open Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The local cocycle equation for an arbitrary coefficient h-map in a commutative
square. The edge is specified solely by its local sheafification equation. This
requires no derived-pullback input, top-degree bound, or tensor-pullback unit.
Source: Stacks Project, Cohomology, Tags 01E4 and 01FB, with the canonical local
Leray and sheafification comparisons of Tags 0D5X and 0BKJ
(blueprint: lem-weil-pbc-derived-square-local-classes).

Proof: Resolve F and G by I and J. Resolve v_*J by an injective complex L and
lift the coefficient map to beta:I -> L. Its augmentation is phi followed by
v_* of the augmentation of J and the replacement ell:v_*J -> L. The normalized
right-adjoint comparison of the square identifies Rf(phi[0]) followed by that
comparison with the roof f_*I -> f_*L <- g_*k_*J. Its arrows are f_*beta and
f_*ell, including the sectionwise comparison of the square. Restriction preserves
injective resolutions and the augmentation equations. On U, sections of ell are
a quasi-isomorphism by the pushforward-injectives section theorem. Thus the map
on cohomology of this roof is precisely moduleCohomologyFMap of the restricted
phi, by its independence-of-choices theorem. The local class map sends a cocycle
to the section of the cohomology sheaf represented by that cocycle. Its naturality
for both arrows of the roof gives the same equation after passage to cohomology
sheaves. The edge's defining equation removes the intermediate local cohomology
of Rg_*Rk_*G. Finally the canonical total/classical comparisons and the two
augmentation-preserving restricted-resolution comparisons give exactly the
maps displayed below. No class map is inverted, only comparison isomorphisms
and the cohomology of sections of ell. The argument includes q=0, empty opens,
zero coefficients, and nonflat morphisms. -/
theorem derivedSquareUnit_localClasses {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G) (q : ℕ)
    (e : (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).obj
        ((schemeDerivedDirectImage g).obj ((schemeDerivedDirectImage k).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))) ⟶
      (pushforward g).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (q : ℤ)).obj
          ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))))
    (he : ∀ V : S.Opensᵒᵖ,
      (RingedSpace.topEdgeLocalClass S.toRingedSpace (q : ℤ)
        ((schemeDerivedDirectImage g).obj ((schemeDerivedDirectImage k).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G)))).app V ≫
        ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map e).hom.app V =
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app V ≫
      (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).app V)
    (V : S.Opens) (I : InjectiveResolution F) (J : InjectiveResolution G)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (R' : RestrictedResolutionSections J (v ⁻¹ᵁ (f ⁻¹ᵁ V))) :
    (resolutionSectionClass R.resolution
        (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        V R.sections q ≫ Hom.app (I.isoRightDerivedObj (pushforward f) q).inv V) ≫
      Hom.app (M := ((pushforward f).rightDerived q).obj F)
        (N := (pushforward g).obj (((pushforward k).rightDerived q).obj G))
        ((schemeSingleCohomologyComparison f F q).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).map
            (derivedSquareUnitMap f k g v h F G φ) ≫ e ≫
        (pushforward g).map (schemeSingleCohomologyComparison k G q).hom) V =
      moduleCohomologyFMap (v.resLE (f ⁻¹ᵁ V) (v ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)
        (restrictedDirectImageMap v φ (f ⁻¹ᵁ V)) q ≫
      resolutionSectionClass R'.resolution
        (((pushforward k).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)
        (g ⁻¹ᵁ V) (R'.sections ≪≫ eqToIso (C := CochainComplex AddCommGrpCat.{u} ℕ)
          (congrArg (β := CochainComplex AddCommGrpCat.{u} ℕ) (fun U : Z.Opens ↦
          ((RingedSpace.openModuleSections Z.toRingedSpace U).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj J.cocomplex) ((Scheme.Hom.comp_preimage v f V).symm.trans
            ((congrArg (fun t : Z ⟶ S ↦ t ⁻¹ᵁ V) h).trans
              (Scheme.Hom.comp_preimage k g V))))) q ≫
      Hom.app (J.isoRightDerivedObj (pushforward k) q).inv (g ⁻¹ᵁ V) := by
  simp only [Hom.comp_app, pushforward_map_app]
  let K : schemeDerivedCategory T := (schemeDerivedDirectImage k).obj
    ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G)
  let A : schemeDerivedCategory S := (schemeDerivedDirectImage f).obj
    ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
  let a := derivedSquareUnitMap f k g v h F G φ
  let hU : v ⁻¹ᵁ (f ⁻¹ᵁ V) = k ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]
  have hs := squareResolution_localClass f F q V I (f ⁻¹ᵁ V) rfl R
  have ht := squareResolution_localClass k G q (g ⁻¹ᵁ V) J
    (v ⁻¹ᵁ (f ⁻¹ᵁ V)) hU R'
  have hn := congrArg (fun t ↦ t.app (op V))
    (RingedSpace.squareLocalClass_naturality (q : ℤ) a)
  change ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map a).app
      (op V) ≫
      (RingedSpace.topEdgeLocalClass S.toRingedSpace (q : ℤ)
        ((schemeDerivedDirectImage g).obj K)).app (op V) =
    (RingedSpace.topEdgeLocalClass S.toRingedSpace (q : ℤ) A).app (op V) ≫
      Hom.app ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).map a) V at hn
  have hi : (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom (q : ℤ) K).app
      (op V) = (squareInverseOpenComparison g (q : ℤ) K).hom.app (op V) ≫
        (RingedSpace.topEdgeLocalClass T.toRingedSpace (q : ℤ) K).app (op (g ⁻¹ᵁ V)) := by
    exact congrArg (fun t ↦ t.app (op V)) (squareInverseOpenComparison_class g (q : ℤ) K)
  have hr := square_localHypercohomology f k g v h F G φ q V I J R R'
  change resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V R.sections q ≫ Hom.app (I.isoRightDerivedObj (pushforward f) q).inv V = _ at hs
  have hc := congrArg (fun t ↦ Hom.app t V)
    (schemeSingleCohomologyComparison f F q).hom_inv_id
  change Hom.app (schemeSingleCohomologyComparison f F q).hom V ≫
      Hom.app (schemeSingleCohomologyComparison f F q).inv V = 𝟙 _ at hc
  exact local_class_pasting (C := AddCommGrpCat.{u})
    (resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V R.sections q ≫ Hom.app (I.isoRightDerivedObj (pushforward f) q).inv V)
    (squareLocalResolutionComparison f F q V I (f ⁻¹ᵁ V) rfl R).hom
    ((RingedSpace.topEdgeLocalClass S.toRingedSpace (q : ℤ) A).app (op V))
    (Hom.app (schemeSingleCohomologyComparison f F q).hom V)
    (Hom.app (schemeSingleCohomologyComparison f F q).inv V)
    (Hom.app ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).map
        (derivedSquareUnitMap f k g v h F G φ)) V)
    (((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map a).app
      (op V))
    ((RingedSpace.topEdgeLocalClass S.toRingedSpace (q : ℤ)
      ((schemeDerivedDirectImage g).obj K)).app (op V))
    (Hom.app e V)
    ((RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ) K).hom.app (op V))
    ((RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom (q : ℤ) K).app (op V))
    ((squareInverseOpenComparison g (q : ℤ) K).hom.app (op V))
    ((RingedSpace.topEdgeLocalClass T.toRingedSpace (q : ℤ) K).app (op (g ⁻¹ᵁ V)))
    (Hom.app (schemeSingleCohomologyComparison k G q).hom (g ⁻¹ᵁ V))
    (moduleCohomologyFMap (v.resLE (f ⁻¹ᵁ V) (v ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)
      (restrictedDirectImageMap v φ (f ⁻¹ᵁ V)) q)
    (squareLocalResolutionComparison k G q (g ⁻¹ᵁ V) J
      (v ⁻¹ᵁ (f ⁻¹ᵁ V)) hU R').hom
    _ hs ht hc hn (he (op V)) hi hr

end AlgebraicGeometry
