/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.GlobalSectionsGeomConnected
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatGlobalSectionsCriterion

/-!
# Universal structure-sheaf pushforward for proper flat morphisms

## References

* Stacks Project, Derived Categories of Schemes, Tag 0E0L
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper flat morphism of finite presentation whose residue-field fibres are geometrically
reduced and geometrically connected has canonical map `𝒪_S → f_* 𝒪_X` an isomorphism,
universally. Here the canonical map `𝒪_T → p_* 𝒪_{X_T}` (for `p = pullback.snd f g`) is the
unit `𝒪_T → p_* p^* 𝒪_T` at `𝒪_T` of the pullback/pushforward adjunction. -/
theorem isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f]
    (hred : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s))
    (hconn : ∀ s : S, GeometricallyConnected (f.fiberToSpecResidueField s)) :
    IsIso ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        IsIso ((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
            (SheafOfModules.unit T.ringCatSheaf)) := by
  apply isIso_structureSheafMap_of_proper_flat_fiberwise f
  intro s
  let k : Type u := S.residueField s
  let F := f.fiberToSpecResidueField s
  let : (Scheme.Hom.fiber f s).Over (Spec (.of k)) :=
    f.fiberOverSpecResidueField s
  let : GeometricallyReduced ((Scheme.Hom.fiber f s) ↘ Spec (.of k)) := hred s
  have : IsProper ((Scheme.Hom.fiber f s) ↘ Spec (.of k)) := by
    change IsProper (pullback.snd f (S.fromSpecResidueField s))
    exact MorphismProperty.pullback_snd _ _ inferInstance
  have hbij : Function.Bijective (Scheme.globalSectionsRingHom k
      (X := Scheme.Hom.fiber f s)) :=
    (Scheme.globalSectionsRingHom_bijective_iff_geometricallyConnected k
      (Scheme.Hom.fiber f s)).2 (hconn s)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ F.appTop) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2 hbij
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv F.appTop

end AlgebraicGeometry
