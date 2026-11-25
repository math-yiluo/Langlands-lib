/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Derived comparison for an acyclic module on an open subscheme -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The derived-composition comparison for a module acyclic for open pushforward.
Source: blueprint lemma-coherent-base-change-invertible-sheaves, proof paragraphs 2 and 3;
Stacks Project, Derived Categories, Tag 015M.
(blueprint: lem-pc-open-pushforward-derived-comparison)

Proof: resolve M by an injective resolution I on W. Restriction to W is an exact
left adjoint of j_*, so j_* preserves injectives. Since M is j_*-acyclic, applying
j_* to I, with the induced augmentation from j_*M, gives an injective resolution
of j_*M: its positive homology vanishes by acyclicity, and degree zero is j_*M
by left exactness. Computing R^q f_* on this resolution gives H^q(f_*j_*I).
The sectionwise pushforward composition isomorphism identifies this complex with
(f j)_*I, whose homology computes R^q(f j)_*M. Composing these identifications
proves the stated comparison in every degree, including degree zero. No affine
or quasi-coherence hypothesis is needed for this comparison. -/
theorem open_pushforward_rightDerived_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (W : X.Opens) [HasInjectiveResolutions W.toScheme.Modules]
    (M : W.toScheme.Modules)
    (hM : (Scheme.Modules.pushforward W.ι).rightAcyclic M) (q : ℕ) :
    Nonempty
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj
          ((Scheme.Modules.pushforward W.ι).obj M) ≅
        ((Scheme.Modules.pushforward (W.ι ≫ f)).rightDerived q).obj M) := by
  have : HasInjectiveResolutions X.Modules :=
    inferInstanceAs (HasInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  have : (Scheme.Modules.restrictFunctor W.ι).PreservesMonomorphisms := by
    constructor
    intro A B φ hφ
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    exact PresheafOfModules.injective_of_mono
      ((SheafOfModules.forget _).map φ) (Opposite.op (W.ι ''ᵁ U.unop))
  let J := Scheme.Modules.pushforward W.ι
  let G := Scheme.Modules.pushforward f
  let I := injectiveResolution M
  have : PreservesFiniteLimits J :=
    have := (Scheme.Modules.restrictAdjunction W.ι).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  have : PreservesFiniteLimits G :=
    have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  have hsingle (n : ℕ) : J.rightAcyclic
      (((CochainComplex.single₀ W.toScheme.Modules).obj M).X n) := by
    cases n with
    | zero => exact hM
    | succ n =>
      exact J.rightAcyclic.prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
  have := J.quasiIso_map_of_rightAcyclic_nat I.ι hsingle
    (fun n ↦ Functor.rightAcyclic_of_injective (F := J) (I.cocomplex.X n))
  let α := (HomologicalComplex.singleMapHomologicalComplex J
    (ComplexShape.up ℕ) 0).inv.app M ≫
      (J.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have : QuasiIso α := inferInstance
  have hI (n : ℕ) : G.rightAcyclic (J.obj (I.cocomplex.X n)) := by
    have : Injective (J.obj (I.cocomplex.X n)) :=
      (Scheme.Modules.restrictAdjunction W.ι).map_injective _ inferInstance
    exact Functor.rightAcyclic_of_injective _
  let e := (Functor.mapHomologicalComplexCompIso
    (Scheme.Modules.pushforwardComp W.ι f) (ComplexShape.up ℕ)).app I.cocomplex
  exact ⟨G.rightDerivedObjIsoOfResolution α hI q ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso e ≪≫
    (I.isoRightDerivedObj (Scheme.Modules.pushforward (W.ι ≫ f)) q).symm⟩

end AlgebraicGeometry
