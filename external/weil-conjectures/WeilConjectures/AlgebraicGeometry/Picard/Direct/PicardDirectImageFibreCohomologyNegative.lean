/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti

import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Negative fibre cohomology of a flat line-bundle direct image

## References

* Stacks Project, Tag 0B91(2), and Tag 0BF2, the displayed fibre comparison
-/

@[expose] public section

set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem finiteLocallyFree_isFlatOver {X S : Scheme.{v}}
    (f : X ⟶ S) [Flat f] (G : X.Modules) [G.IsFiniteLocallyFree] :
    G.IsFlatOver f := by
  intro V U e
  let := (f.appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(S, V.1) Γ(X, U.1) :=
    HasRingHomProperty.appLE @Flat f ‹_› V U e
  have := (Modules.finitePresentation_projective_sections G U.2).2
  let : Module Γ(S, V.1) Γ(G, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
  have : IsScalarTower Γ(S, V.1) Γ(X, U.1) Γ(G, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(S, V.1) Γ(X, U.1) Γ(G, U.1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Negative residue cohomology of a proper flat line-bundle direct image vanishes. -/
theorem picard_directImage_fibre_cohomology_negative
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) (w : W) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∀ j : ℤ, j < 0 → IsZero (derivedFiberCohomology W E j w) := by
  classical
  dsimp only
  let : ∀ U : W.Opens, HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  let : ∀ {Y Z : Scheme.{v}} (a : Y ⟶ Z), (Modules.tensorPullback a).Additive := by
    intro Y Z a
    let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction a)
    let : (Modules.tensorPullback a).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  let fW := pullback.snd f k
  let G := (Modules.tensorPullback (pullback.fst f k)).obj L
  let eG : G ≅ (Modules.pullback (pullback.fst f k)).obj L :=
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).leftAdjointUniq
       (Modules.pullbackPushforwardAdjunction (pullback.fst f k))).app L
  have : G.IsInvertible := Modules.IsInvertible.of_iso eG.symm
  have : SheafOfModules.IsInvertible.{v, v, v} G :=
    Modules.IsInvertible.sheafOfModules_isInvertible G
  have hflat : G.IsFlatOver fW := finiteLocallyFree_isFlatOver fW G
  let g := W.fromSpecResidueField w
  let p := pullback.fst fW g
  let q := pullback.snd fW g
  obtain ⟨c, hc, hiso⟩ := exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    fW g p q (IsPullback.of_hasPullback fW g) G hflat
  let φ := schemeDerivedBaseChangeMap fW q g p pullback.condition
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj G) ≫
    (schemeDerivedDirectImage q).map c
  have : IsIso φ := hiso
  let P := RingedSpace.moduleDirectImage q.toLRSHom.toShHom
  have hge := P.isGE_rightDerivedFunctor_obj_singleFunctor
    ((Modules.tensorPullback p).obj G)
  intro j hj
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)) j
  have hz : IsZero (H.obj ((schemeDerivedDirectImage q).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback fW g).toRingedSpace)) 0).obj
          ((Modules.tensorPullback p).obj G)))) :=
    DerivedCategory.isZero_of_isGE _ 0 j hj
  have hz' := hz.of_iso (H.mapIso (asIso φ))
  let Γ := SheafOfModules.evaluation
    (moduleRings (Spec (W.residueField w)).toRingedSpace) (Opposite.op ⊤)
  have hzΓ : IsZero (Γ.obj (H.obj ((derivedPullback g).obj
      ((schemeDerivedDirectImage fW).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj G))))) := by
    rw [IsZero.iff_id_eq_zero, ← Γ.map_id, hz'.eq_of_src (𝟙 _) 0]
    exact Γ.map_zero _ _
  have hs := ModuleCat.isZero_iff_subsingleton.mp hzΓ
  let : Subsingleton (derivedFiberCohomology W
      ((schemeDerivedDirectImage fW).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj G)) j w) :=
    hs
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry.Scheme
