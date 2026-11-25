/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedStructureTensorProjection
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # The ordinary complex projection formula for a closed structure sheaf

Source: Stacks Project, Modules, Tags 01AX and 08KS; More on Algebra, Tag 068G.
(blueprint: lem-pc-closed-structure-tensor-complex-projection). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Tensor with the pushed-forward structure sheaf is termwise pullback and pushforward.
Source: Stacks Project, Modules, Tags 01AX and 08KS; More on Algebra, Tag 068G.
(blueprint: lem-pc-closed-structure-tensor-complex-projection).

Proof: the ordinary projection map M tensor i_*O_Z -> i_*(i^*M) is induced by the
pullback adjunction and the tensor unit on Z. At a point i(z) both stalks are
M_{i(z)} tensor_{O_{Y,i(z)}} O_{Z,z}, and the map is the identity on pure tensors.
Off the closed image, the open complement shows both stalks are zero. Stalks
therefore detect that the map is an isomorphism for every M. Naturality makes
these isomorphisms commute with every differential of P. Tensor with a single
complex in degree zero has just one nonzero summand in each total degree; the
single/total-tensor comparison identifies its differential with d_P tensor 1,
with sign +1. Compose this comparison with the degreewise projection isomorphism.
No K-flatness, augmentation or derived category is needed. Empty sources give
zero complexes on both sides; the identity immersion gives the ordinary unit law. -/
theorem nonempty_closedStructure_tensor_complex_projection
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℤ) :
    letI : MonoidalCategory (SheafOfModules.{u} Y.ringCatSheaf) :=
      SheafOfModules.monoidalCategory Y.sheaf
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (CochainComplex.mapBifunctor P
      ((HomologicalComplex.single (SheafOfModules.{u} Y.ringCatSheaf) (.up ℤ) 0).obj B)
      (curriedTensor _) ≅
      ((Scheme.Modules.pushforward i).mapHomologicalComplex (.up ℤ)).obj T) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  have : (Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.pushforward i).Additive :=
    inferInstance
  obtain ⟨e⟩ := nonempty_closedStructure_tensor_projection i
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  exact ⟨CochainComplex.mapBifunctorSingle₂Iso
    (curriedTensor (SheafOfModules.{u} Y.ringCatSheaf)) B P ≪≫
    (NatIso.mapHomologicalComplex e (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.pushforward i))
      (.up ℤ)).symm.app P⟩

end AlgebraicGeometry
