/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange

/-! # A global derived model for relatively flat higher direct images

Source: Stacks Project, Tag 0B91(2), and the injective-resolution definition of
higher direct images (blueprint: lemma-coherent-base-change-invertible-sheaves--2).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Higher direct images of a finitely presented relatively flat module have one global
connective derived model, with cohomology computing every cartesian base change.

Source: Stacks Project, Tag 0B91(2); Tag 079V for computation by injective resolutions.
(blueprint: lemma-coherent-base-change-invertible-sheaves--2).

Proof: take E = Rf_*(F[0]). Resolve F by an injective resolution in nonnegative degrees.
The resulting bounded-below complex of injectives is K-injective after embedding
into integer complexes.
Applying f_* computes the unbounded derived direct image and its degree-q cohomology is
exactly the right derived functor defining higherDirectImage f q. Its negative cohomology
vanishes because this resolution is nonnegative. Relative flatness and finite presentation
allow Tag 0B91(2) to identify Lg^*E with Rf'_*(g'^*F[0]) for every cartesian square.
For a chosen square rather than the standard categorical pullback, transport this
isomorphism along sq.isoPullback and the pullback composition isomorphisms. Take degree-q
cohomology and use the same injective-resolution comparison on X' to obtain the last
clause. These are global derived isomorphisms, so their cohomology identifications are
compatible on overlaps, rather than choices of unrelated local free trivializations. -/
theorem exists_derived_model_higherDirectImage
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation] (hF : F.IsFlatOver f) :
    ∃ E : schemeDerivedCategory T,
      (∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E)) ∧
      (∀ q : ℕ, Nonempty ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E ≅
          (higherDirectImage f q).obj F)) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g → ∀ q : ℕ,
        Nonempty ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) q).obj
            ((AlgebraicGeometry.derivedPullback g).obj E) ≅
              (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by
  let E : schemeDerivedCategory T := (schemeDerivedDirectImage f).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
  have hGE : E.IsGE 0 := by
    dsimp [E, schemeDerivedDirectImage]
    exact Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F
  refine ⟨E, ?_, ?_, ?_⟩
  · intro n hn
    exact DerivedCategory.isZero_of_isGE E 0 n hn
  · intro q
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    exact ⟨D.homologyRightDerivedFunctorObjSingleFunctorIso F q⟩
  · intro T' X' g g' f' _ hsq q
    let P := tensorPullback g'
    obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction g'
    let : P.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    have : P.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ P
      (by
        rw [CategoryTheory.rightExactFunctor_iff]
        infer_instance)
    obtain ⟨c, _, hc⟩ := exists_isIso_canonicalModuleBaseChange_of_isFlatOver
      f g g' f' hsq F hF
    let φ := schemeDerivedBaseChangeMap f f' g g' hsq.w
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ≫
      (schemeDerivedDirectImage f').map c
    let : IsIso φ := hc
    let t := adj.leftAdjointUniq (pullbackPushforwardAdjunction g')
    let S' := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0
    let d := asIso φ ≪≫ (schemeDerivedDirectImage f').mapIso (S'.mapIso (t.app F))
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) (q : ℤ)
    let D := RingedSpace.moduleDirectImage f'.toLRSHom.toShHom
    exact ⟨H.mapIso d ≪≫ D.homologyRightDerivedFunctorObjSingleFunctorIso
      ((pullback g').obj F) q⟩

end AlgebraicGeometry.Scheme.Modules
