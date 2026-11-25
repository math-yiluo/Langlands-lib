/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.Picard.Affine.PicardAffineStructureProjectiveRepresentation
import WeilConjectures.AlgebraicGeometry.Picard.Affine.PicardAffineStructureProjectiveHomology

/-! # The unnormalized affine structure-image model

## References

* Stacks Project, Tag 0BF2, perfect base-change paragraph
* Tags 0B91, 08EB, 06Z0
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The trivialized coefficient image has a bounded projective affine model whose
base changes have no negative homology and have free rank-one zeroth homology.
No cancellation of terms or vanishing of a differential is asserted here. -/
theorem picard_affine_structure_projective_model
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    ∃ P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (W.presheaf.obj (.op U)) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (W.presheaf.obj (.op U)) (P.X n)) ∧
      (∀ (B : Type v) [CommRing B] (φ : W.presheaf.obj (.op U) →+* B),
        let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
        (∀ i : ℤ, i < 0 → IsZero (PB.homology i)) ∧
          Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) ∧
      Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨P, hb, hf, hp, hrep⟩ :=
    picard_affine_structure_projective_representation f M W k U hU htrivial
  exact ⟨P, hb, hf, hp,
    picard_affine_structure_projective_homology f hO M W k U hU htrivial P hb hp hrep,
    hrep⟩

end AlgebraicGeometry.Scheme
