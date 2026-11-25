/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Proper support of an individual etale section

Source: Stacks Project, Tags 04FT and 0F76
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

/-- A section has proper support when its nonzero-geometric-germ locus is a closed
subset whose reduced induced subscheme is proper over the specified base.
Source: Stacks Project, Tags 04FT and 0F76
(auxiliary; not a blueprint node). -/
def SectionHasProperSupport
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (p : V.left ⟶ S) [LocallyOfFiniteType p] (s : F.obj.obj (op V)) : Prop :=
  ∃ Z : TopologicalSpace.Closeds V.left,
    (Z : Set V.left) = {x | ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (v : Spec (.of Ω) ⟶ V.left), v default = x ∧
        (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
          (Over.homMk v rfl) F.obj s ≠ 0} ∧
    Scheme.IsClosedSubsetProperOver p Z

end AlgebraicGeometry.Etale
