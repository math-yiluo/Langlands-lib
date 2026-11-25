/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedRootProjectionLinear
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.BottomFiniteRootUnitIsIso

/-! # Linearity and invertibility of the normalized root-limit map

Source: diagonal coefficient changes, integral root-limit identification.
(blueprint: lem-diagonal-completed-coefficient-root-line-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint
  Scheme.purTwistZlCompletionOfUniverses
  InternalAbelianSheafModule.sectionModuleEquivalenceCore

private theorem freeUnit_tensorMap
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a]
    {M N : C} (f : M ⟶ N) :
    (Mod.freeForgetAdjunction R).unit.app M ≫ (a ⊗ₘ f) =
      f ≫ (Mod.freeForgetAdjunction S).unit.app N := by
  change ((λ_ M).inv ≫ η[R] ▷ M ≫ 𝟙 _) ≫ (a ⊗ₘ f) =
    f ≫ (λ_ N).inv ≫ η[S] ▷ N ≫ 𝟙 _
  simp only [Category.comp_id]
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, IsMonHom.one_hom,
    ← MonoidalCategory.whisker_exchange]
  rw [← Category.assoc, ← MonoidalCategory.leftUnitor_inv_naturality]
  rw [Category.assoc]

/-- After identifying the coefficient rings by their reductions, the root-limit
map is an isomorphism of sectionwise modules.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower,
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), and the integral
root-limit normalization in lem-diagonal-integral-root-map.
(blueprint: lem-diagonal-completed-coefficient-root-line-comparison).

Proof: the normalized maps to the positive finite integral twist levels are
linear. Their underlying maps are the root projections followed by free-module
units, so the projection equations of roots make them a compatible cone.
Restriction of internal scalars and the section-module equivalence preserve
limits, giving a linear lift to the integral line. The forgetful limit's
projections identify its underlying map with roots.hom. At each finite level
the bottom-field coefficient is the usual residue ring, so the free-module
unit on the torsion root sheaf is invertible. Tensor naturality of these units
gives an isomorphism of towers. Passing to limits and the forgetful limit
comparison identifies its isomorphism with roots.hom. The sectionwise forgetful
functor reflects isomorphisms, proving the assertion. This includes the empty
scheme. The remaining finite scalar and torsion tensor calculations are the
separate declarations completedRootProjection_linear and bottomFiniteRootUnit_isIso. -/
theorem completedCoefficientRootLineComparison_exists (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (l : Γ(X, ⊤)))
    (e : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) ≅
        Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    (he : ∀ n : ℕ,
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.inv ≫
            (purZlReduction l X (n + 1)).hom =
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              ((sheafCompose (Scheme.ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                  (Scheme.purTwistZlProjection X l n)) ≫
            (sfbConstantRingAbIso X
              (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom)
    (roots : IntegralRoots l (bottomField l) X) :
    ∃ s : (SheafOfModules.restrictScalars e.hom).obj (Scheme.purTwistZlModule X l) ≅
        (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).functor.obj
            (zlLine l X),
      (SheafOfModules.toSheaf _).map s.hom = roots.hom := by
  let T := spIntegralTwistSystem X l (bottomField l)
  let U := Mod.forget
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} l (bottomField l).1) X)
  let C := Mod.comap
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralMap l (bottomField l)) X)
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)
  let H := C ⋙ E.functor
  let V := SheafOfModules.toSheaf
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)))
  choose f hf using completedRootProjection_linear l X hX e he
  let c : Cone (T ⋙ H) :=
    { pt := (SheafOfModules.restrictScalars e.hom).obj (Scheme.purTwistZlModule X l)
      π :=
        { app := fun n ↦ f n.unop
          naturality := by
            intro i j g
            have hn : f i.unop ≫ H.map (T.map g) = f j.unop := by
              apply V.map_injective
              change V.map (f i.unop) ≫ (T.map g).hom = V.map (f j.unop)
              rw [hf i.unop, hf j.unop, ← roots.projections i.unop,
                ← roots.projections j.unop]
              simpa only [Category.assoc, Mod.comp_hom'] using
                congrArg (fun k : limit T ⟶ T.obj j ↦ roots.hom ≫ k.hom) (limit.w T g)
            exact (Category.id_comp (f j.unop)).trans hn.symm } }
  let hc := isLimitOfPreserves H (limit.isLimit T)
  let m := hc.lift c
  have hm : V.map m = roots.hom := by
    apply (isLimitOfPreserves U (limit.isLimit T)).hom_ext
    intro n
    change V.map m ≫ (limit.π T n).hom = roots.hom ≫ (limit.π T n).hom
    calc
      _ = V.map (m ≫ H.map (limit.π T n)) := rfl
      _ = V.map (f n.unop) := congrArg V.map (hc.fac c n)
      _ = _ := (hf n.unop).trans (roots.projections n.unop).symm
  have hr : IsIso roots.hom := by
    let R := Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)
    let a : R ⟶ T ⋙ U := NatTrans.ofOpSequence
      (fun n ↦ (Mod.freeForgetAdjunction
        (condensedRingObj (spEllPointRingObj l (bottomField l) n) X)).unit.app
          (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) (by
        intro n
        dsimp only [T, U, R, Functor.comp_map, spIntegralTwistSystem,
          Scheme.proEtaleRootsOfUnityTower]
        rw [Functor.ofOpSequence_map_homOfLE_succ,
          Functor.ofOpSequence_map_homOfLE_succ]
        have ht := (spIntegralLevelTransition_existsUnique X l (bottomField l) n).exists.choose_spec
        change (spIntegralLevelTransition X l (bottomField l) n).hom = _ at ht
        change _ = _ ≫ (spIntegralLevelTransition X l (bottomField l) n).hom
        rw [ht]
        exact (freeUnit_tensorMap _ _).symm)
    have : ∀ n, IsIso (a.app n) := fun n ↦ bottomFiniteRootUnit_isIso l X n.unop
    have : IsIso a := NatIso.isIso_of_isIso_app a
    have heq : roots.hom = limMap a ≫ (preservesLimitIso U T).inv := by
      apply (isLimitOfPreserves U (limit.isLimit T)).hom_ext
      intro n
      change roots.hom ≫ (limit.π T n).hom =
        (limMap a ≫ (preservesLimitIso U T).inv) ≫ U.map (limit.π T n)
      rw [Category.assoc, preservesLimitIso_inv_π, limMap_π]
      exact roots.projections n.unop
    rw [heq]
    infer_instance
  have : IsIso (V.map m) := hm.symm ▸ hr
  have : IsIso m := isIso_of_reflects_iso m V
  exact ⟨asIso m, hm⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
