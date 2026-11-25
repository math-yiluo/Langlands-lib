/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Finite-coefficient geometric-fibre formula

Source: Stacks Project, Tag 0DDF; SGA 4, Expose XII, Corollaire 5.2(iii);
blueprint `sec-proper-base-change/sk-thm-properbasechange/`
`cor-weil-pbc-geometric-fiber-finite.md`
(blueprint: corollary-cohomology-geometric-fibres--2).

The cohomological formula includes the two endpoint identifications explicitly:
global sections of the source are the geometric stalk, and global sections of the
target are the cohomology of the geometric fibre. The map between these presentations
is the degree-q base-change map, not an unspecified isomorphism between groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Finite-coefficient proper base change at a geometric point, Stacks Tag 0DDF(2).
(blueprint: corollary-cohomology-geometric-fibres--2)

Proof: form the pullback square with projections i_y and a_y. A finite additive
group is torsion (`isAddTorsion_of_finite`), so every complex of Λ-module sheaves
has torsion cohomology (`moduleTorsionHomology_of_isTorsion`). Apply the module
version of bounded-below proper base change directly. No coefficient-forgetting
comparison is needed. -/
theorem isIso_geometricFiber_finite
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback f y).toCommSq).app K) := by
  exact isIso_baseChange_of_isProper_of_torsionHomology Λ
    (IsPullback.of_hasPullback f y) K
    (DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X
      isAddTorsion_of_finite K)

/-- The identity-point germ is invertible for module sheaves: apply the set-valued
constancy theorem to the underlying sheaf, commute its filtered stalk colimit with
forgetting scalars, and reflect the resulting isomorphism. -/
private theorem isIso_module_identityGerm
    (Λ : Type (u + 1)) [CommRing Λ]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (Over.homMk (𝟙 _) (Category.comp_id _)) F.obj) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))
  let I := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let xI : Φ.fiber.obj I := Over.homMk (𝟙 _) (Category.comp_id _)
  let U := CategoryTheory.forget (ModuleCat.{u + 1} Λ)
  let G := (sheafCompose (Spec (.of Ω)).smallEtaleTopology U).obj F
  have : IsIso (Φ.toPresheafFiber I xI (F.obj ⋙ U)) :=
    (isIso_iff_bijective _).2 (Scheme.spec_algClosed_etale_sheaf_constant Ω G).2
  have : IsIso (U.map (Φ.toPresheafFiber I xI F.obj)) := by
    rw [← Φ.toPresheafFiber_presheafFiberCompIso_hom_app U I xI F.obj]
    infer_instance
  exact isIso_of_reflects_iso _ U

/-- The canonical module-valued global germ, using the identity etale neighbourhood. -/
private noncomputable def module_identityGermIso
    (Λ : Type (u + 1)) [CommRing Λ]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≅
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber := by
  let Φ := Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))
  let τ := Functor.whiskerLeft
    (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Φ.toPresheafFiberNatTrans (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (Over.homMk (𝟙 _) (Category.comp_id _)))
  have : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact isIso_module_identityGerm Λ Ω
  exact Sheaf.ΓNatIsoSheafSections _ _
    (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) _) ≪≫ asIso τ

/-- The geometric-stalk formula, with its endpoint comparisons and its base-change map.
Source: Stacks Tag 0DDF(1); SGA 4 XII, Corollaire 5.2(iii).
(blueprint: corollary-cohomology-geometric-fibres--2)

Proof: apply isIso_geometricFiber_finite to F in degree zero. Exactness of y^{-1}
identifies the source homology sheaf with y^{-1} R^q f_* F
(def-weil-pbc-inverse-image, def-weil-pbc-direct-image). Its sections are the stalk
at y (def-weil-pbc-geometric-stalks, lem-weil-pbc-geometric-point-pullback-stalk).
Global sections on Spec Omega are exact, so they commute with cohomology.
The generic Leray isomorphism
`rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`, together with
`rightDerivedFunctorPlusCompatibility`, identifies the target sections with H^q(X_y, i_y^{-1} F)
(def-weil-pbc-etale-cohomology). These comparisons transport the global sections of
the degree-q exchange map to the displayed stalk-to-fibre map. Functors and transport
by isomorphisms preserve isomorphisms. Finiteness of F is not needed in this argument. -/
theorem geometricFiber_finite_stalk_formula
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsFiniteSheaf F]
    (q : ℕ) :
    ∃ (sourceIso :
        (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          ((baseChangeSourceFunctor Λ y f q).obj F) ≅
        ((Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          (higherDirectImage Λ f q F))
      (targetIso :
        (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          ((baseChangeTargetFunctor Λ (pullback.fst f y) (pullback.snd f y) q).obj F) ≅
        (cohomology (ModuleCat.{u + 1} Λ) (pullback f y) q).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F))),
      IsIso (sourceIso.inv ≫
        (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
          (baseChangeHomologyMap Λ (IsPullback.of_hasPullback f y) q F) ≫ targetIso.hom) := by
  let A := ModuleCat.{u + 1} Λ
  let P := Spec (.of Ω)
  let ΓP := Sheaf.Γ P.smallEtaleTopology A
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  let E := (lowerStar A f).rightDerivedFunctorPlus.obj K
  let L := (upperStar A (pullback.fst f y)).mapDerivedCategoryPlus.obj K
  let M := (lowerStar A (pullback.snd f y)).rightDerivedFunctorPlus.obj L
  have hSections := (Scheme.geometricPoint_pullback_stalk Ω).2.2.2.1 Λ
  have : ((sheafSections P.smallEtaleTopology A).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 P)))).IsEquivalence := hSections.1
  have : ΓP.IsEquivalence := Functor.isEquivalence_of_iso
    (Sheaf.ΓNatIsoSheafSections _ _
      (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) P)).symm
  let sourceIso := ΓP.mapIso
      (((upperStar A y).mapDerivedCategoryPlusHomologyFunctorIso q).symm.app E) ≪≫
    (module_identityGermIso Λ Ω).app
      ((upperStar A y).obj (higherDirectImage Λ f q F)) ≪≫
    (upperStarCompSheafFiberIso A y (𝟙 P)).app (higherDirectImage Λ f q F) ≪≫
    eqToIso (by rw [Category.id_comp])
  let targetIso :=
    (ΓP.rightDerivedFunctorHomologyFunctorIso q).app M.obj ≪≫
      (_root_.DerivedCategory.homologyFunctor A q).mapIso
        (ΓP.rightDerivedFunctor.mapIso
            ((lowerStar A (pullback.snd f y)).rightDerivedFunctorPlusCompatibility.app L) ≪≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A
            (pullback.snd f y)).app L.obj ≪≫
          (rightDerivedGlobalSections A (pullback f y)).mapIso
            ((upperStar A (pullback.fst f y)).mapDerivedCategoryPlusCompatibility.app K ≪≫
              ((upperStar A (pullback.fst f y)).mapDerivedCategorySingleFunctor 0).app F))
  have hBC := isIso_geometricFiber_finite Λ f Ω y K
  have : IsIso (baseChangeHomologyMap Λ (IsPullback.of_hasPullback f y) q F) := by
    change IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ q).map
      ((baseChange A (IsPullback.of_hasPullback f y).toCommSq).app K))
    rw [baseChange_eq_derivedBaseChangeMapPlus]
    infer_instance
  exact ⟨sourceIso, targetIso, inferInstance⟩

end AlgebraicGeometry.Etale
