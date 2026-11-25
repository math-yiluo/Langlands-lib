/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.BottomFiniteRootUnitIsIso
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootMap
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement

/-! # Detection and scalar compatibility of integral root limits

Source: diagonal tower coefficient changes (1), the limit universal property.
(blueprint: lem-diagonal-root-limit-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The bottom root comparison is an isomorphism, since its every level is.
Source: coefficient changes (1) (blueprint: lem-diagonal-root-limit-compatibility).
Proof: the free units form a natural isomorphism of inverse systems. Transport the
limiting root cone along it and compare with the scalar-forgotten integral limit. -/
theorem diagonalBottomIntegralRoots_isIso
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (r : IntegralRoots l (bottomField l) X) :
    IsIso r.hom := by
  let T := spIntegralTwistSystem X l (bottomField l)
  let U := Mod.forget
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} l (bottomField l).1) X)
  let F := Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)
  let t : F ⟶ T ⋙ U := NatTrans.ofOpSequence
    (fun n ↦ (Mod.freeForgetAdjunction
      (condensedRingObj (spEllPointRingObj l (bottomField l) n) X)).unit.app
        (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) (by
      intro n
      dsimp only [Functor.comp_map, T, U, F, spIntegralTwistSystem,
        Scheme.proEtaleRootsOfUnityTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      have ht := (spIntegralLevelTransition_existsUnique X l (bottomField l) n).exists.choose_spec
      change (spIntegralLevelTransition X l (bottomField l) n).hom = _ at ht
      change _ = _ ≫ (spIntegralLevelTransition X l (bottomField l) n).hom
      rw [ht, freeUnit_tensorMap])
  have : ∀ j, IsIso (t.app j) := fun j ↦ bottomFiniteRootUnit_isIso l X j.unop
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let c := (Cone.postcompose t).obj (limit.cone F)
  let hc : IsLimit c := (IsLimit.postcomposeHomEquiv (asIso t) (limit.cone F)).symm
    (limit.isLimit F)
  let hd := isLimitOfPreserves U (limit.isLimit T)
  let f : c ⟶ U.mapCone (limit.cone T) :=
    { hom := r.hom
      w := fun j ↦ r.projections j.unop }
  have : IsIso f := IsLimit.hom_isIso hc hd f
  exact (Cone.forget _).map_isIso f

/-- Integral extension carries the bottom root map to the prescribed E root map.
Source: coefficient changes (1) (blueprint: lem-diagonal-root-limit-compatibility).
Proof: compare every finite projection, use the specified integral transition and
naturality of the free-module unit, then cancel the limiting cone projections. -/
theorem diagonalIntegralRoots_transition
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l)
    (r : IntegralRoots l (bottomField l) X) (s : IntegralRoots l E X) :
    r.hom ≫ integralLineMap l E X = s.hom := by
  apply (isLimitOfPreserves
    (Mod.forget (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) X))
    (limit.isLimit (spIntegralTwistSystem X l E))).hom_ext
  intro j
  change (r.hom ≫ integralLineMap l E X) ≫
    (limit.π (spIntegralTwistSystem X l E) j).hom =
      s.hom ≫ (limit.π (spIntegralTwistSystem X l E) j).hom
  have hm := (spIntegralTwistMap_existsUnique X l
    (show (bottomField l).1 ≤ E.1 from bot_le)).exists.choose_spec j.unop
  change integralLineMap l E X ≫
    (limit.π (spIntegralTwistSystem X l E) j).hom = _ at hm
  rw [Category.assoc, hm, ← Category.assoc, r.projections j.unop, s.projections j.unop]
  let h : (bottomField l).1 ≤ E.1 := bot_le
  have := spEllReduction_epi X l (bottomField l) j.unop
  have : IsMonHom (spIntegersMap X l h) := (spIntegersMap_spec X l h).1
  have : IsMonHom (spEllReduction X l (bottomField l) j.unop) :=
    spEllReduction_isMonHom X l _ _
  have : IsMonHom (spEllReduction X l E j.unop) := spEllReduction_isMonHom X l _ _
  have : IsMonHom (spEllMap X l h j.unop) :=
    spMonHom_of_epi (spEllReduction X l (bottomField l) j.unop)
      (spIntegersMap X l h ≫ spEllReduction X l E j.unop) _ (spEllMap_spec X l h j.unop)
  rw [Category.assoc, freeUnit_tensorMap, Category.id_comp]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
