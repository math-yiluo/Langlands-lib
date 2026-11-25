/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Tensor bounds for arbitrary representatives over a constant field sheaf

Source: Bhatt--Scholze, Remark 6.3.2; Stacks Project, Tags 03ER and 06YL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {D : Type w} [SmallCategory D] (J : GrothendieckTopology D)
  (k : Type w) [Field k]

private theorem ring_field_tensor_exact
    (N : ConstantCompletion.Mod (ConstantCompletion.constant J k)) :
    let := SheafOfModules.monoidalCategory (ConstantCompletion.constant J k)
    PreservesFiniteLimits (MonoidalCategory.tensorRight N) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight N) := by
  let := SheafOfModules.monoidalCategory (ConstantCompletion.constant J k)
  have h := SheafOfModules.isFlat_constantFieldModule J k N
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (ConstantCompletion.constant J k) N) h

/-- Every representative of a bounded derived object over a constant field sheaf has
bounded tensor with a sheaf placed in degree zero. K-flatness is not needed here.

Source: Bhatt--Scholze, Remark 6.3.2; Stacks Tags 03ER and 06YL
(auxiliary; not a blueprint node).
Proof: every module sheaf over the constant field sheaf is flat by the local
relation criterion. The comparison from site sheaf tensor to monoidal tensor
therefore makes right tensor exact. Localization and its homology comparison give
the bounds on the displayed representative P.
The signed total of P with N[0] is naturally its termwise right tensor by N, which
commutes with homology by exactness. Thus its outside-interval homology is zero. -/
theorem constantFieldResidueTensor_bounds
    (C : ConstantCompletion.D (ConstantCompletion.constant J k))
    (a b : ℤ)
    (h : ∀ q : ℤ, (q < a ∨ b < q) → IsZero
      ((adicResidueCohomology (ConstantCompletion.constant J k) q).obj C))
    (P : ConstantCompletion.Cx (ConstantCompletion.constant J k))
    (e : Nonempty ((ConstantCompletion.Q (ConstantCompletion.constant J k)).obj P ≅ C))
    (N : ConstantCompletion.Mod (ConstantCompletion.constant J k))
    (q : ℤ) (hq : q < a ∨ b < q) :
    IsZero (adicResidueTensorCohomology (ConstantCompletion.constant J k) P N q) := by
  let R := ConstantCompletion.constant J k
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  let := (SheafOfModules.tensorClosed R).2.1.some
  obtain ⟨e⟩ := e
  have hP : IsZero (P.homology q) := (h q hq).of_iso
    (((DerivedCategory.homologyFunctorFactors _ q).app P).symm ≪≫
      (adicResidueCohomology R q).mapIso e)
  have := (ring_field_tensor_exact J k N).1
  have := (ring_field_tensor_exact J k N).2
  let F := MonoidalCategory.tensorRight N
  have hz : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj P).homology q) :=
    (F.map_isZero hP).of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) q).app P)
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso
    (CochainComplex.mapBifunctorSingle₂Iso
      (MonoidalCategory.curriedTensor (ConstantCompletion.Mod R)) N P))

end AlgebraicGeometry.Scheme
