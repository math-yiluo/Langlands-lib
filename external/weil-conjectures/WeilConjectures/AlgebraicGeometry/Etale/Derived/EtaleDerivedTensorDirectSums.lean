/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement

/-!
# Derived tensor products of étale sheaves preserve direct sums

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-derived-tensor-direct-sums.md` (blueprint: proposition-open-direct-image-preserves-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Tensoring on either side with an arbitrary unbounded derived étale sheaf preserves
set-indexed direct sums, including the empty sum.

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-derived-tensor-direct-sums.md` (blueprint: proposition-open-direct-image-preserves-finite).

Proof plan:
1. The category of coefficient sheaves is Grothendieck abelian, by
`lem-pur-ringed-site-grothendieck-abelian`, working on a small skeleton of the étale site.
2. By `lem-kun-grothendieck-derived-coproducts`, termwise direct sums compute coproducts
of arbitrary unbounded complexes after localization, also for the empty family.
3. Choose a complex representing A and a K-flat resolution P, using
`lem-kun-flat-resolution-existence`. The construction
`proposition-open-direct-image-preserves-finite` computes A tensor B by the localization of the
direct-sum total tensor P tensor C_B. Use the same P for every summand and their sum; independence
is `proposition-open-direct-image-preserves-finite`.
4. The tensor-Hom adjunction `lem-pc-sheaf-modules-tensor-closed` shows that ordinary
sheaf tensor preserves sums. Interchange the degreewise sums indexed by i and by
(p,q) with p+q=n in `def-pc-tensor-complex-sheaves`. Both differentials restrict to
d_P tensor 1 + (-1)^p 1 tensor d_C on each summand, giving an isomorphism of complexes
whose restrictions are the tensor images of the original coprojections.
5. Localize this isomorphism. By step 2 its source is the coproduct of the derived
tensors and its target is the derived tensor with the coproduct. The restriction
calculation identifies it with the canonical coproduct comparison. Every derived
object has a complex representative, so this proves preservation for all families.
6. The natural symmetry `lem-kun-tensor-sym` identifies the right tensor comparison
with the left comparison conjugated by symmetry and the coproduct of its component
isomorphisms. Thus the other variable also preserves sums. For the empty family the
same construction identifies the tensor of the zero object with zero. -/
theorem derivedTensor_preservesDirectSums (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u}) (A : DerivedCategoryModule Λ T) :
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj A)) ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).flip.obj A)) := by
  -- The existing tensor--Hom adjunction avoids unfolding the derived monoidal structure.
  have h (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj A) :=
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) A).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  refine ⟨h, fun I ↦ ?_⟩
  have := h I
  exact preservesColimitsOfShape_of_natIso
    ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) T).app A)

end AlgebraicGeometry.Etale
