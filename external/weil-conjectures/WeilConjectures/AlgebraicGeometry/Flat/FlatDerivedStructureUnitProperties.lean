/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.Flat.FlatInvertibleCanonicalDerivedBaseChange
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalStructureMapBaseChange
import WeilConjectures.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit

/-! # Derived fibres of the canonical structure map

Source: Stacks Project, Tags 0E62 (first paragraph), 0A1D, and 0096.
(blueprint: flat-derived-structure-unit-properties).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_structureMap_over_field {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsIso f.appTop] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let t := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let F := SheafOfModules.toSheaf (Spec (.of K)).ringCatSheaf ⋙
    sheafToPresheaf _ AddCommGrpCat
  have : IsIso (F.map t) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    induction U using Opposite.rec with
    | op U =>
      rw [ConcreteCategory.isIso_iff_bijective]
      rcases U.eq_bot_or_top with hU | hU
      · subst U
        change Function.Bijective (f.app ⊥)
        have : Subsingleton Γ(Spec (.of K), ⊥) :=
          CommRingCat.subsingleton_of_isTerminal (Spec (.of K)).sheaf.isTerminalOfEmpty
        have : Subsingleton Γ(X, f ⁻¹ᵁ ⊥) :=
          CommRingCat.subsingleton_of_isTerminal
            (X.sheaf.isTerminalOfEqEmpty (by simp))
        exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩
      · subst U
        change Function.Bijective f.appTop
        exact ConcreteCategory.bijective_of_isIso f.appTop
  exact isIso_of_reflects_iso t F

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit structure map, obtained by applying the single functor to the
ordinary structure map and composing with the canonical right-derived unit,
has nonnegative derived fibres and induces an isomorphism in degree zero when
the canonical map on fibre global functions is invertible.
Source: Stacks Project, Tag 0E62 (first paragraph), Tag 0A1D, and Tag 0096.
(blueprint: flat-derived-structure-unit-properties).

Proof: For a point s, use the cartesian residue-field square with projections
p : X_s → X and f_s : X_s → Spec κ(s). Flatness of f says the stalks of O_X
are flat over the corresponding base stalks, so O_X is relatively flat over S.
Apply exists_isIso_canonicalModuleBaseChange_of_isFlatOver to O_X. Its target
is R(f_s)_*((p^*O_X)[0]); tensorPullbackObjUnitToUnit identifies p^*O_X with
O_{X_s}. This gives an isomorphism b : Li_s^*Rf_*O_X[0] ≅ R(f_s)_*O_{X_s}[0].
An injective resolution of O_{X_s} in nonnegative degrees computes the latter
object, so its negative cohomology vanishes, and b transports this vanishing.
For the map assertion, O_S[0] is K-flat; hence the left-derived counit and the
adjoint structure-sheaf map give j : Li_s^*O_S[0] ≅ O_{Spec κ(s)}[0]. The mate
identity for canonical base change, evaluated on the single ordinary structure
map, says that Li_s^*(a) followed by b equals j followed by a_s, where a_s is
the single fibre structure map followed by its canonical right-derived unit.
This follows by transposing both composites under the derived adjunction for
f_s: the ordinary structure map transposes to p^*O_X → O_{X_s}, and the two
counit/adjunction-unit pairs cancel by the triangle identities. The chosen
left-derived counit is the same in the comparison and in the mate, so no
arbitrary map a can replace this explicit canonical composite.
Taking H0 and using canonicalDirectImageH0Unit identifies H0(a_s) with the
ordinary module structure map O_{Spec κ(s)} → (f_s)_*O_{X_s}. On Spec of a
field there are only the empty and the whole open set. At the empty open every
module sheaf is zero; on the whole open the underlying map is exactly appTop
of f_s, with the canonical Γ(Spec κ(s), O) identification. Thus the assumed
IsIso on appTop makes this module map an isomorphism. Cancel H0(j) and H0(b)
to obtain the claimed IsIso. Empty fibres satisfy the negative assertion; their
map κ(s) → 0 cannot satisfy the last hypothesis, so that implication is vacuous. -/
theorem flat_derived_structure_unit_properties
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] [Flat f] :
    (∀ (s : S) (i : ℤ), i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj
          ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
              (SheafOfModules.unit X.ringCatSheaf)))))) ∧
    (∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop →
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
          ((derivedPullback (S.fromSpecResidueField s)).map
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
                (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
              Scheme.Modules.canonicalSingleDirectImageMap f
                (SheafOfModules.unit X.ringCatSheaf))))) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  constructor
  · intro s i hi
    let g := S.fromSpecResidueField s
    let p := f.fiberι s
    let f' := f.fiberToSpecResidueField s
    let OX : SheafOfModules.{u} X.ringCatSheaf := SheafOfModules.unit X.ringCatSheaf
    let OX' : SheafOfModules.{u} (f.fiber s).ringCatSheaf :=
      SheafOfModules.unit (f.fiber s).ringCatSheaf
    let singleX := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
    let singleX' := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (f.fiber s).toRingedSpace)) 0
    let c := Scheme.Modules.canonicalSinglePullbackMap p OX ≫
      singleX'.map (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
    have : SheafOfModules.IsInvertible.{u, u, u} OX := by
      dsimp only [OX]
      exact SheafOfModules.instIsInvertibleUnit (R := X.ringCatSheaf)
    have : IsIso (Scheme.Modules.canonicalSinglePullbackMap p OX) :=
      Scheme.Modules.isIso_canonicalSinglePullbackMap p OX
    have : IsIso c := by dsimp only [c]; infer_instance
    let b := schemeDerivedBaseChangeMap f f' g p (f.fiber_fac s) (singleX.obj OX) ≫
      (schemeDerivedDirectImage f').map c
    have : IsIso (schemeDerivedBaseChangeMap f f' g p (f.fiber_fac s)
        (singleX.obj OX)) := Scheme.Modules.isIso_derivedBaseChange_of_flat_invertible
          f g p f' (IsPullback.of_hasPullback f g) OX
    have : IsIso b := by dsimp only [b]; infer_instance
    have hge := Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom) OX'
    exact ((DerivedCategory.isGE_iff _ 0).mp hge i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (asIso b))
  · intro s hs
    have : IsIso (f.fiberToSpecResidueField s).appTop := hs
    let g := S.fromSpecResidueField s
    let p := f.fiberι s
    let f' := f.fiberToSpecResidueField s
    let OX : SheafOfModules.{u} X.ringCatSheaf := SheafOfModules.unit X.ringCatSheaf
    let OX' : SheafOfModules.{u} (f.fiber s).ringCatSheaf :=
      SheafOfModules.unit (f.fiber s).ringCatSheaf
    let singleX := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
    let singleX' := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (f.fiber s).toRingedSpace)) 0
    let c := Scheme.Modules.canonicalSinglePullbackMap p OX ≫
      singleX'.map (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
    have : SheafOfModules.IsInvertible.{u, u, u} OX := by
      dsimp only [OX]
      exact SheafOfModules.instIsInvertibleUnit (R := X.ringCatSheaf)
    have : IsIso (Scheme.Modules.canonicalSinglePullbackMap p OX) :=
      Scheme.Modules.isIso_canonicalSinglePullbackMap p OX
    have : IsIso c := by dsimp only [c]; infer_instance
    let b := schemeDerivedBaseChangeMap f f' g p (f.fiber_fac s) (singleX.obj OX) ≫
      (schemeDerivedDirectImage f').map c
    have : IsIso (schemeDerivedBaseChangeMap f f' g p (f.fiber_fac s)
        (singleX.obj OX)) := Scheme.Modules.isIso_derivedBaseChange_of_flat_invertible
          f g p f' (IsPullback.of_hasPullback f g) OX
    have : IsIso b := by dsimp only [b]; infer_instance
    let OS : SheafOfModules.{u} S.ringCatSheaf := SheafOfModules.unit S.ringCatSheaf
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0
    let singleS' := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0
    let j := Scheme.Modules.canonicalSinglePullbackMap g OS ≫
      singleS'.map (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
    have : SheafOfModules.IsInvertible.{u, u, u} OS :=
      SheafOfModules.instIsInvertibleUnit (R := S.ringCatSheaf)
    have : IsIso (Scheme.Modules.canonicalSinglePullbackMap g OS) :=
      Scheme.Modules.isIso_canonicalSinglePullbackMap g OS
    have : IsIso j := by dsimp only [j]; infer_instance
    have : IsIso (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) :=
      isIso_structureMap_over_field f'
    have : HasInjectiveResolutions (f.fiber s).Modules :=
      inferInstanceAs (HasInjectiveResolutions
        (SheafOfModules.{u} (moduleRings (f.fiber s).toRingedSpace)))
    let z := Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom) OX' 0 ≪≫
        (Scheme.Modules.pushforward f').rightDerivedZeroIsoSelf.app OX'
    have hz : H.map (Scheme.Modules.canonicalSingleDirectImageMap f' OX') ≫ z.hom =
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).app
            ((Scheme.Modules.pushforward f').obj OX')).hom :=
      Scheme.Modules.canonicalDirectImageH0Unit f' OX'
    have : IsIso (H.map (Scheme.Modules.canonicalSingleDirectImageMap f' OX')) := by
      apply (isIso_comp_right_iff _ z.hom).mp
      rw [hz]
      infer_instance
    have heq := congrArg H.map (canonical_structure_map_base_change f f' g p (f.fiber_fac s))
    simp only [Functor.map_comp] at heq
    apply (isIso_comp_right_iff _ (H.map b)).mp
    rw [show H.map ((derivedPullback g).map
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          Scheme.Modules.canonicalSingleDirectImageMap f OX)) ≫ H.map b =
        H.map j ≫ H.map (singleS'.map
          (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom)) ≫
            H.map (Scheme.Modules.canonicalSingleDirectImageMap f' OX') by
          simpa only [b, c, j, OX, OX', OS, singleX, singleX', singleS',
            Functor.map_comp, Category.assoc] using heq]
    infer_instance

end AlgebraicGeometry
