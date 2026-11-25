/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluation
import WeilConjectures.Algebra.Homology.HomologyEvaluationRoofComparison
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

/-! Core finite-free roof calculation for local homology evaluation. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- The finite-free roof calculation proves local invertibility once its roof is exposed.
Source: Stacks Project, Tag 0BQY, zero-differential Hom calculation.
(blueprint: new-b2-homology-evaluation-local-iso-core).

The proof is the explicit finite-free zero-differential calculation together with the
quasi-isomorphism comparison square. -/
theorem homologyEvaluation_local_iso_of_roof (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (E L : CochainComplex
      (SheafOfModules (V.toScheme.ringCatSheaf.over W)) ℤ)
    (q : L ⟶ (moduleOpenOverComplexFunctor X V W).obj T)
    (p : L ⟶ E) (hq : QuasiIso q) (hp : QuasiIso p)
    (hzero : ∀ a b : ℤ, E.d a b = 0)
    (hsupp : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k))
    (hfree : ∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf.over W) (ULift.{u} (Fin r)))) :
    IsIso (((Scheme.Modules.restrictFunctor V.ι).map e).over W) := by
  let O := SheafOfModules.overFunctor.{u} X.ringCatSheaf V
  let A := (Scheme.Modules.overEquiv V).functor
  let R := Scheme.Modules.restrictFunctor V.ι
  let B := SheafOfModules.overFunctor.{u} V.toScheme.ringCatSheaf W
  let F := R ⋙ B
  let : PreservesFiniteLimits O := moduleOverFunctor_limits X.toRingedSpace V
  let : PreservesFiniteColimits O := moduleOverFunctor_colimits X.toRingedSpace V
  let : PreservesFiniteLimits (O ⋙ A) := comp_preservesFiniteLimits O A
  let : PreservesFiniteColimits (O ⋙ A) := comp_preservesFiniteColimits O A
  let : PreservesFiniteLimits R :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.overFunctorEquiv V)
  let : PreservesFiniteColimits R :=
    preservesFiniteColimits_of_natIso (Scheme.Modules.overFunctorEquiv V)
  let : PreservesFiniteLimits B := moduleOverFunctor_limits V.toScheme.toRingedSpace W
  let : PreservesFiniteColimits B := moduleOverFunctor_colimits V.toScheme.toRingedSpace W
  let : PreservesFiniteLimits F := comp_preservesFiniteLimits R B
  let : PreservesFiniteColimits F := comp_preservesFiniteColimits R B
  let : F.PreservesZeroMorphisms := moduleOpenOver_preservesZeroMorphisms X V W
  have hK : ∀ k : ℤ, k ≠ 0 →
      IsZero (((moduleOpenOverComplexFunctor X V W).obj J).homology k) := by
    intro k hk
    exact (F.map_isZero (hJ k hk)).of_iso
      ((F.mapHomologicalComplexHomologyIso (.up ℤ) k).app J)
  obtain ⟨f, hf, c, hc, hc'⟩ := finiteFreeZero_homologyEvaluation
    (V.toScheme.sheaf.over W) E ((moduleOpenOverComplexFunctor X V W).obj J)
    n hK hzero hsupp hfree
  obtain ⟨a, b, hab⟩ := homologyEvaluation_roof_comparison X T J n e he V W hI
    E L q p hq hp f c hc hc'
  let : IsIso f := hf
  have : IsIso ((((Scheme.Modules.restrictFunctor V.ι).map e).over W) ≫ b.hom) := by
    rw [hab]
    infer_instance
  exact IsIso.of_isIso_comp_right _ b.hom

end CategoryTheory
