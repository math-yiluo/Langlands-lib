/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentPseudoCoherent
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Quasi-coherence of derived Hom from a finite pushforward algebra

Source: Stacks Project, Duality for Schemes, Tag 0AX2, with Tags 0AUC, 0AUP and 0A6H
(blueprint: lem-sc-finite-pushforward-derived-hom-qcoherent).
-/

@[expose] public section

universe u w wB

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- For a finite morphism of Noetherian schemes, `B = f_* 𝒪_X` is pseudo-coherent.
Derived internal Hom from `B` sends bounded-below quasi-coherent complexes to
bounded-below quasi-coherent complexes of `B`-modules. Forgetting the algebra action
still gives a bounded-below quasi-coherent complex on `Y`. The equality identifying `B`
includes its algebra structure, namely the structure map `f.c`, not just its module.

Source: Stacks Project, Duality for Schemes, Tag 0AX2, with Tags 0AUC, 0AUP and 0A6H
(blueprint: lem-sc-finite-pushforward-derived-hom-qcoherent).

Proof:
1. The equality identifying B includes its algebra structure. After substitution, its
   underlying module is definitionally the pushforward of the unit module. Apply
   `isCoherent_unit_of_finite_to_locallyNoetherian` and
   `isCoherent_pushforward_of_isFinite` (lem-weil-pbc-finite-pushforward-coherent).
2. On the Noetherian target, the coherence criterion
   `isCoherent_iff_isQuasicoherent_and_isFiniteType` (pqf-lem-coherent-ft-locnoeth)
   gives quasi-coherence. Apply `isPseudoCoherent_singleFunctor_obj_of_isCoherent`
   (lem-sc-coherent-pseudo-coherent) to obtain pseudo-coherence of B[0].
3. Apply `pseudoCoherentRHomQuasiCoherent` (lem-sc-pseudo-coherent-rhom-qcoherent)
   with K's quasi-coherence property and lower bound. Mathlib's `Q_obj_single_obj`
   identifies the two presentations of B[0]. The lemma gives all three remaining
   conclusions, including the underlying object's quasi-coherence and lower bound. -/
theorem finite_pushforward_derivedHom_qcoherent {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    (B : Y.CommAlgebraSheaf)
    (hBf : B = Under.mk (⟨f.c⟩ : Y.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
        B.right))]
    (K : schemeDerivedQCohCategory Y) (hK : ∃ n : ℤ, K.obj.IsGE n) :
    ∃ hB : B.toModule.IsQuasicoherent,
      Scheme.IsPseudoCoherent Y
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj B.toModule) ∧
      sheafAlgebraDerivedQCohProperty Y B hB
        ((derivedRHomAlgebraModule Y B hB).obj K.obj) ∧
      schemeDerivedQCohProperty Y
        ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).map
            B.hom)).mapDerivedCategory.obj
              ((derivedRHomAlgebraModule Y B hB).obj K.obj)) ∧
      ∃ n : ℤ,
        ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).map
            B.hom)).mapDerivedCategory.obj
              ((derivedRHomAlgebraModule Y B hB).obj K.obj)).IsGE n := by
  have hmod : B.toModule =
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) := by
    subst B
    rfl
  have hcoh : RingedSpace.IsCoherent Y.toRingedSpace B.toModule := by
    rw [hmod]
    exact (Scheme.Modules.isCoherent_pushforward_of_isFinite f _
      (Scheme.Modules.isCoherent_unit_of_finite_to_locallyNoetherian f)).1
  have hB := ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    Y B.toModule).mp hcoh).1
  have hpc := Scheme.isPseudoCoherent_singleFunctor_obj_of_isCoherent Y B.toModule hcoh
  refine ⟨hB, hpc, ?_⟩
  exact pseudoCoherentRHomQuasiCoherent Y B hB (by simpa using hpc) K.obj K.property hK

end AlgebraicGeometry
