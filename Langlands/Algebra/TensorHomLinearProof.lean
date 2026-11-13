import Langlands.Algebra.TensorHomLinearStatements
import Langlands.Algebra.NonUnitalTensorHomAdjunctionProof
import Langlands.Algebra.NonUnitalTensorAssociativity
import Langlands.Algebra.NonUnitalBimoduleHomScalarsParts
import Langlands.Algebra.NonUnitalBimoduleTensorScalars

/-! # Coefficient linearity of Renard I.2.2 -/

set_option autoImplicit false

namespace Langlands.Algebra.TensorHomLinear

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul)

universe uK uR uS uX uY uZ

section CompatibleAssociativity

variable (k : Type uK) (R : Type uR) (S : Type uS)
  (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k] [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
  [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
  [Module k Z] [SMulCommClass k S Z] (hY : ActionsCommute R S Y)

/-- The additive associator preserves coefficients carried through its final factor. -/
theorem compatibleAssociator_smul (c : k)
    (t : NonUnitalTensorAssociativity.LeftTensor R S X Y Z hY) :
    letI := NonUnitalBimoduleTensor.rightModule X hY
    letI := NonUnitalBimoduleTensor.leftModule hY Z
    letI := NondegenerateTensorScalars.compatibleModule k S Y Z
    letI := residual_smulCommClass k (Z := Z) hY
    letI := NondegenerateTensorScalars.compatibleModule k S (Tensor R X Y) Z
    letI := NondegenerateTensorScalars.compatibleModule k R X (Tensor S Y Z)
    NonUnitalTensorAssociativity.associator R S X Y Z hY (c • t) =
      c • NonUnitalTensorAssociativity.associator R S X Y Z hY t := by
  let := NonUnitalBimoduleTensor.rightModule X hY
  let := NonUnitalBimoduleTensor.leftModule hY Z
  let := NondegenerateTensorScalars.compatibleModule k S Y Z
  let := residual_smulCommClass k (Z := Z) hY
  let := NondegenerateTensorScalars.compatibleModule k S (Tensor R X Y) Z
  let := NondegenerateTensorScalars.compatibleModule k R X (Tensor S Y Z)
  let E := NonUnitalTensorAssociativity.associator R S X Y Z hY
  have h : E.toAddMonoidHom.comp
        (DistribSMul.toAddMonoidHom (NonUnitalTensorAssociativity.LeftTensor R S X Y Z hY) c) =
      (DistribSMul.toAddMonoidHom (NonUnitalTensorAssociativity.RightTensor R S X Y Z hY) c).comp
        E.toAddMonoidHom :=
    NonUnitalTensorAssociativity.left_hom_ext R S X Y Z hY fun _ _ _ => rfl
  exact DFunLike.congr_fun h t

end CompatibleAssociativity

namespace UnitizedRight

open NonUnitalTensorHomAdjunction.Right

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [Module k X] [NonUnitalModule Rᵐᵒᵖ X]
  [IsScalarTower k Rᵐᵒᵖ X] [SMulCommClass k Rᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule R Y] [IsScalarTower k R Y]
  [SMulCommClass k R Y] [NonUnitalModule Sᵐᵒᵖ Y] [IsScalarTower k Sᵐᵒᵖ Y]
  [SMulCommClass k Sᵐᵒᵖ Y]
  [AddCommGroup Z] [Module k Z] [NonUnitalModule Sᵐᵒᵖ Z]
  [IsScalarTower k Sᵐᵒᵖ Z] [SMulCommClass k Sᵐᵒᵖ Z]
  (hY : ActionsCommute R S Y)

attribute [local instance] CompatibleUnitizationTensor.rightNonUnitalModule
  CompatibleUnitizationTensor.leftNonUnitalModule

/-- The canonical unitized right currying equivalence is coefficient-linear. -/
theorem existsLinearCanonical : ExistsLinearCanonical k R S X Y Z hY := by
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z)
    (unitizedActionsCommute k R S Y hY)
  let := tensorHomModule k R S X Y Z hY
  let := curriedHomModule k R S X Y Z hY
  let E := NonUnitalTensorHomAdjunction.Right.equivalence
    (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k R S Y hY)
  refine ⟨{ E with map_smul' := ?_ }, ?_⟩
  · intro c φ
    apply NonUnitalModuleHom.ext
    intro x
    apply NonUnitalModuleHom.ext
    intro y
    rfl
  · exact NonUnitalTensorHomAdjunction.Right.equivalence_canonical
      (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k R S Y hY)

end UnitizedRight

namespace UnitizedLeft

open NonUnitalTensorHomAdjunction.Left

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [Module k X] [NonUnitalModule R X]
  [IsScalarTower k R X] [SMulCommClass k R X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule S Y] [IsScalarTower k S Y]
  [SMulCommClass k S Y] [NonUnitalModule Rᵐᵒᵖ Y] [IsScalarTower k Rᵐᵒᵖ Y]
  [SMulCommClass k Rᵐᵒᵖ Y]
  [AddCommGroup Z] [Module k Z] [NonUnitalModule S Z]
  [IsScalarTower k S Z] [SMulCommClass k S Z]
  (hY : ActionsCommute S R Y)

attribute [local instance] CompatibleUnitizationTensor.rightNonUnitalModule
  CompatibleUnitizationTensor.leftNonUnitalModule

/-- The canonical unitized left currying equivalence is coefficient-linear. -/
theorem existsLinearCanonical : ExistsLinearCanonical k R S X Y Z hY := by
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z)
    (unitizedActionsCommute k S R Y hY)
  let := tensorHomModule k R S X Y Z hY
  let := curriedHomModule k R S X Y Z hY
  let E := NonUnitalTensorHomAdjunction.Left.equivalence
    (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k S R Y hY)
  refine ⟨{ E with map_smul' := ?_ }, ?_⟩
  · intro c φ
    apply NonUnitalModuleHom.ext
    intro x
    apply NonUnitalModuleHom.ext
    intro y
    rfl
  · exact NonUnitalTensorHomAdjunction.Left.equivalence_canonical
      (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k S R Y hY)

end UnitizedLeft

namespace UnitizedAssoc

open NonUnitalTensorAssociativity

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [Module k X] [NonUnitalModule Rᵐᵒᵖ X]
  [IsScalarTower k Rᵐᵒᵖ X] [SMulCommClass k Rᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule R Y] [IsScalarTower k R Y]
  [SMulCommClass k R Y] [NonUnitalModule Sᵐᵒᵖ Y] [IsScalarTower k Sᵐᵒᵖ Y]
  [SMulCommClass k Sᵐᵒᵖ Y]
  [AddCommGroup Z] [Module k Z] [NonUnitalModule S Z]
  [IsScalarTower k S Z] [SMulCommClass k S Z]
  (hY : ActionsCommute R S Y)

attribute [local instance] CompatibleUnitizationTensor.rightNonUnitalModule
  CompatibleUnitizationTensor.leftNonUnitalModule

/-- The canonical unitized associator is coefficient-linear. -/
theorem existsLinearCanonical : ExistsLinearCanonical k R S X Y Z hY := by
  let := unitizedLeft_smulCommClass k S Z
  let := leftTensorModule k R S X Y Z hY
  let := rightTensorModule k R S X Y Z hY
  let E := NonUnitalTensorAssociativity.associator
    (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k R S Y hY)
  refine ⟨{ E with map_smul' := ?_ }, ?_⟩
  · exact compatibleAssociator_smul k (Unitization k R) (Unitization k S) X Y Z
      (unitizedActionsCommute k R S Y hY)
  · exact NonUnitalTensorAssociativity.associator_canonical
      (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k R S Y hY)

end UnitizedAssoc

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

namespace NondegenerateRight

open NonUnitalTensorHomAdjunction.Right

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
  [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]
  [AddCommGroup Z] [NonUnitalModule Sᵐᵒᵖ Z]
  (hY : ActionsCommute R S Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hSZ : IsNondegenerate Sᵐᵒᵖ Z)

/-- The canonical refined currying equivalence preserves the recovered coefficients. -/
theorem existsLinearRefinedCanonical (hX : IsNondegenerate Rᵐᵒᵖ X)
    (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : NonUnitalBimoduleHomScalars.RightSourceCompatible k hS hSY (R := R)) :
    ExistsLinearRefinedCanonical k R S X Y Z hY hR hS hSZ := by
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := tensorHomModule k R S X Y Z hY hS hSZ
  let := refinedHomModule k R S X Y Z hY hR
  let E := NonUnitalTensorHomAdjunction.Right.refinedEquivalence
    R S X Y Z hY hR hX
  refine ⟨NonUnitalTensorHomAdjunction.Right.equivalence R S X Y Z hY,
    { E with map_smul' := ?_ }, ?_⟩
  · intro c φ
    apply NonUnitalModuleHom.ext
    intro x
    change E (c • φ) x =
      (letI := NondegenerateScalars.module k hR.op
        (nondegeneratePart_isNondegenerate
          (M := NonUnitalModuleHom Sᵐᵒᵖ Y Z) hR.op); c • E φ x)
    rw [NonUnitalBimoduleHomScalars.rightSourcePart_recovered_smul_eq
      k hR hS hY hSZ hSY hc]
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro y
    rfl
  · exact NonUnitalTensorHomAdjunction.Right.refinedEquivalence_canonical
      R S X Y Z hY hR hX

end NondegenerateRight

namespace NondegenerateLeft

open NonUnitalTensorHomAdjunction.Left

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [NonUnitalModule R X]
  [AddCommGroup Y] [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
  [AddCommGroup Z] [NonUnitalModule S Z]
  (hY : ActionsCommute S R Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hSZ : IsNondegenerate S Z)

/-- The canonical refined currying equivalence preserves the recovered coefficients. -/
theorem existsLinearRefinedCanonical (hX : IsNondegenerate R X)
    (hSY : IsNondegenerate S Y)
    (hc : NonUnitalBimoduleHomScalars.SourceCompatible k hS hSY (S := R)) :
    ExistsLinearRefinedCanonical k R S X Y Z hY hR hS hSZ := by
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hY
  let := tensorHomModule k R S X Y Z hY hS hSZ
  let := refinedHomModule k R S X Y Z hY hR
  let E := NonUnitalTensorHomAdjunction.Left.refinedEquivalence
    R S X Y Z hY hR hX
  refine ⟨NonUnitalTensorHomAdjunction.Left.equivalence R S X Y Z hY,
    { E with map_smul' := ?_ }, ?_⟩
  · intro c φ
    apply NonUnitalModuleHom.ext
    intro x
    change E (c • φ) x =
      (letI := NondegenerateScalars.module k hR
        (nondegeneratePart_isNondegenerate
          (M := NonUnitalModuleHom S Y Z) hR); c • E φ x)
    rw [NonUnitalBimoduleHomScalars.sourcePart_recovered_smul_eq
      k hS hR hY hSZ hSY hc]
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro y
    rfl
  · exact NonUnitalTensorHomAdjunction.Left.refinedEquivalence_canonical
      R S X Y Z hY hR hX

end NondegenerateLeft

namespace NondegenerateAssoc

open NonUnitalTensorAssociativity

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
  [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]
  [AddCommGroup Z] [NonUnitalModule S Z]
  (hY : ActionsCommute R S Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hRY : IsNondegenerate R Y) (hSZ : IsNondegenerate S Z)

/-- The canonical associator preserves the recovered coefficients under input compatibility. -/
theorem existsLinearCanonical (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : NonUnitalBimoduleHomScalars.RightSourceCompatible k hS hSY (R := R)) :
    ExistsLinearCanonical k R S X Y Z hY hR hS hRY hSZ := by
  let := NonUnitalBimoduleTensor.leftModule hY Z
  let := NondegenerateScalars.module k hS hSZ
  let := NondegenerateScalars.smulCommClass k hS hSZ
  have hm := NonUnitalBimoduleTensorScalars.recoveredModule_eq
    k hS hY Z hSZ hR hRY hSY hc
  let leftCoefficients := leftTensorModule k R S X Y Z hY hS hSZ
  let rightCoefficients := rightTensorModule k R S X Y Z hY hR hRY
  let E := NonUnitalTensorAssociativity.associator R S X Y Z hY
  refine ⟨{ E with map_smul' := ?_ }, ?_⟩
  · intro c t
    have h : E.toAddMonoidHom.comp
          (DistribSMul.toAddMonoidHom (LeftTensor R S X Y Z hY) c) =
        (DistribSMul.toAddMonoidHom (RightTensor R S X Y Z hY) c).comp
          E.toAddMonoidHom :=
      NonUnitalTensorAssociativity.left_hom_ext R S X Y Z hY fun x y z => by
        change tmul R X (Tensor S Y Z) x (tmul S Y Z y (c • z)) =
          tmul R X (Tensor S Y Z) x
            (letI := NondegenerateScalars.module k hR
              (NondegenerateTensorFunctor.isNondegenerate hR hY hRY Z)
             c • tmul S Y Z y z)
        exact congrArg (fun m : Module k (Tensor S Y Z) =>
          tmul R X (Tensor S Y Z) x (letI := m; c • tmul S Y Z y z)) hm.symm
    exact DFunLike.congr_fun h t
  · exact NonUnitalTensorAssociativity.associator_canonical R S X Y Z hY

end NondegenerateAssoc

end Langlands.Algebra.TensorHomLinear

namespace Langlands.Algebra

universe uK uR uS uX uY uZ

/-- The three coefficient-linear equivalences over compatible unitizations. -/
theorem unitizedTensorHomLinear :
    UnitizedTensorHomLinearTheorem.{uK, uR, uS, uX, uY, uZ} :=
  ⟨@TensorHomLinear.UnitizedRight.existsLinearCanonical,
    @TensorHomLinear.UnitizedLeft.existsLinearCanonical,
    @TensorHomLinear.UnitizedAssoc.existsLinearCanonical⟩

/-- The three coefficient-linear equivalences for the published recovered modules. -/
theorem nondegenerateTensorHomLinear :
    NondegenerateTensorHomLinearTheorem.{uK, uR, uS, uX, uY, uZ} := by
  refine ⟨?_, ?_, ?_⟩
  · intros
    apply TensorHomLinear.NondegenerateRight.existsLinearRefinedCanonical <;> assumption
  · intros
    apply TensorHomLinear.NondegenerateLeft.existsLinearRefinedCanonical <;> assumption
  · intros
    apply TensorHomLinear.NondegenerateAssoc.existsLinearCanonical <;> assumption

/-- Renard I.2.2 with the coefficient structures and compatibility hypotheses of the Library. -/
theorem tensorHomLinear : TensorHomLinearTheorem.{uK, uR, uS, uX, uY, uZ} :=
  ⟨unitizedTensorHomLinear, nondegenerateTensorHomLinear⟩

end Langlands.Algebra
