/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownOpenSingletonEvaluationCore

/-! # Open singleton evaluation

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16,
printed pp. 21 and 34--35; Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The open singleton insertion evaluates to the open coefficient projection.
Source: Zheng, Construction 5.14, Lemma 5.16 and Construction 4.1,
printed pp. 21 and 34--35
(blueprint: lem-pur-etale-brown-open-singleton-evaluation).

Proof: apply the open extension/inverse-image Hom transpose, followed by the
scalar extension/restriction transpose. The mate equation for q rewrites its open
coefficient factor as the inverse of derivedTensor. The singleton below-level
comparison intertwines its Hom transpose with the strict derived transition: on
flat-term K-flat representatives this is derivedBelow_rep and hom_formula; exact
localization then gives the statement on every derived object. The inverseTransition
identity moves that transition through inverse image. Finally the defining conjugate
identity for insertion and the evaluated open adjunction identity reduce the two
sides to the same map. Injectivity of the transposes gives the equality. Thus the
identity coefficient map is included, and no faithfulness of derived evaluation or
invertibility of any proper singleton mate enters the proof. -/
theorem etaleBrownOpenSingletonEvaluation
    (S : StrictEtaleCompactSupport O t c) {m n : ℕ} (h : m ≤ n)
    (q : (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived)
    (hq : (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ q.hom)) = (S.openDerived.derivedTensor h).inv)
    (P : DerivedCategory (strictEtaleLevel X O t n)) :
    let insertion := ((conjugateIsoEquiv
      ((S.PX.derivedAdj n).comp S.derivedOpenAdjunction)
      ((S.levelDerivedOpenAdjunction n).comp (S.PZ.derivedAdj n))).symm
        (S.openDerived.inverseEvaluation n)).symm
    (S.PZ.evaluation m).map (insertion.hom.app P) ≫
      (S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P) =
    (S.openDerivedEvaluation m).hom.app ((S.PX.derivedExtension n).obj P) ≫
      (S.levelDerivedOpen m).map ((S.PX.derivedBelow h).hom.app P) ≫ q.hom.app P := by
  intro insertion
  simpa [insertion, mateEquiv, conjugateEquiv, Category.assoc] using
    (etaleBrownOpenSingletonEvaluationCore O t c S h q hq P)

end AlgebraicGeometry
