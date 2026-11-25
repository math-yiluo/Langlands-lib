/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.CategoryTheory.InternalModule.InternalModule
import WeilConjectures.CategoryTheory.Finite.FiniteContinuousModule
import Mathlib.Algebra.Category.ModuleCat.Ulift
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicFromFinite
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Sites.PreservesLimits
import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
import WeilConjectures.ConstructibleSheaf.KernelCokernel

set_option linter.privateModule false

/-!
# Galois representations attached to lisse sheaves

Source: Stacks Project, Tag 0DV5; the blueprint, `chap-Verdier-and-Poincare-duality`,
`lemma-perfect-complexes-geometric-point` (blueprint:
proposition-lattices-representations-normal-scheme); Deligne, Weil II (1.1.1), (1.1.6).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite ZeroObject
open scoped TensorProduct FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

private theorem galoisFiniteEtale_preservesFiniteLimits (Y : Scheme.{u}) : PreservesFiniteLimits
    (ObjectProperty.ι (fun P : Y.Etale ↦ IsFinite P.hom)) := by
  let : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).HasOfPostcompProperty
      (@IsFinite ⊓ @Etale) := by
    refine ⟨fun {X Y Z} f g hg hfg ↦ ?_⟩
    have := hg.1; have := hg.2; have := hfg.1; have := hfg.2
    exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩
  let H := MorphismProperty.Over.changeProp (Q := ⊤) (Q' := ⊤) Y
    (inf_le_right : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ @Etale) le_rfl
  have : PreservesFiniteLimits H :=
    MorphismProperty.Over.preservesFiniteLimits_changeProp Y
      (inf_le_right : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ @Etale)
  have : PreservesFiniteLimits (FiniteEtale.toFiniteEtaleOver Y ⋙ H) := inferInstance
  exact this

private theorem galoisFLC_preservesFiniteLimits
    {Y : Scheme.{u}}
    (Φ : Y.FiniteEtale ≌ Y.FLC)
    (hΦ : Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{u + 1})) :
    PreservesFiniteLimits (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))) := by
  obtain ⟨α⟩ := hΦ
  let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
  let : PreservesFiniteLimits
      (ObjectProperty.ι (fun P : Y.Etale ↦ IsFinite P.hom)) :=
    galoisFiniteEtale_preservesFiniteLimits Y
  let : PreservesFiniteLimits Y.smallEtaleTopology.uliftYoneda.{u + 1} :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits (Φ.functor ⋙ I) :=
    preservesFiniteLimits_of_natIso α.symm
  let e : Φ.inverse ⋙ (Φ.functor ⋙ I) ≅ I :=
    (Functor.associator Φ.inverse Φ.functor I).symm ≪≫
      Functor.isoWhiskerRight Φ.counitIso I ≪≫ Functor.leftUnitor I
  exact preservesFiniteLimits_of_natIso e

section ModuleObjectBridge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end ModuleObjectBridge

section ScalarComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end ScalarComposition

end AlgebraicGeometry.Scheme
