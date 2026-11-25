/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The prescribed source-Hom shift maps

## References

* Stacks Project, Tags 08J9 and 08JC
* Stacks 08JC, total-tensor signs
* Stacks 0A8X, 08JC
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

section Shift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The existing tensor shift in its parameter, assembled as a natural isomorphism. -/
@[irreducible] def siteHomTensorParameterShift (K : D) (n : ℤ) :
    tensorLeft (K⟦n⟧) ≅ tensorLeft K ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun M ↦ (((curriedTensor D).flip.obj M).commShiftIso n).app K)
    (fun f ↦ (NatTrans.shift_app_comm ((curriedTensor D).flip.map f) n K).symm)

/-- The canonical source-Hom shift, as the right-adjoint mate of total-tensor shift.
This is the fixed-coefficient counterpart of the recorded ringed source shift, with
orientation H(K[n],-) → H(K,-)[-n]. Its opposite exact structure includes the correction
(-1)^(n(n+1)/2), prescribed below, rather than treating the raw shifts as coherent. -/
@[irreducible] def siteHomSourceShift (K : D) (n : ℤ) :
    ihom (K⟦n⟧) ≅ ihom K ⋙ shiftFunctor D (-n) :=
  (ihom.adjunction (K⟦n⟧)).rightAdjointUniq
    (((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K)).ofNatIsoLeft
      ((tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm))
/-- The same canonical source shift with the opposite-category integer parameter.
The equality transport records -(-n)=n explicitly. -/
@[irreducible] def siteHomOppositeSourceShift (K : D) (n : ℤ) :
    ihom (K⟦-n⟧) ≅ ihom K ⋙ shiftFunctor D n :=
  siteHomSourceShift K (-n) ≪≫
    Functor.isoWhiskerLeft (ihom K) (eqToIso (congrArg (shiftFunctor D) (neg_neg n)))

end Shift

section SignedShift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The prescribed signed source-Hom map for the triangulated opposite shift. -/
def siteHomSignedSourceComponent (M : D) (n : ℤ) (X : Dᵒᵖ) :
    (MonoidalClosed.internalHom.flip.obj M).obj (X⟦n⟧) ⟶
      ((MonoidalClosed.internalHom.flip.obj M).obj X)⟦n⟧ :=
  (n * (n + 1) / 2).negOnePow • (siteHomOppositeSourceShift X.unop n).hom.app M

end SignedShift

end AlgebraicGeometry.ProEtale
