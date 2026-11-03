import Langlands.GroupScheme.Dynamic.RealizedLeviNesting
import Langlands.Representation.Aubert.General.RealizedLeviInduction
import Langlands.Representation.Aubert.General.DynamicNestedParabolicTopology
import Langlands.Representation.Aubert.General.NestedParabolicTransitivity

/-! # Normalized induction in stages through a realized source Levi -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RealizedLeviStages

universe u uV

private def inversePullbackIso
    {H K : Type u} [Group H] [Group K] [TopologicalSpace H] [TopologicalSpace K]
    (e : H ≃ₜ* K) :
    SmoothRep.pullbackFunctor.{u, u, uV} e.symm ⋙ SmoothRep.pullbackFunctor e ≅
      𝟭 (SmoothRep.{0, u, uV} ℂ H) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun h => by
        ext a
        change A.representation (e.symm (e h)) a = A.representation h a
        rw [e.symm_apply_apply]))
    (fun _ => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      rfl)

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G L : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine L.X.left]
    [IsSeparated G.X.hom] [IsSeparated L.X.hom]
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (j : L ⟶ G) (hj : (Dynamic.centralizer χ).IsRepresentedBy j)
    (hc : IsClosedSubgroup j)
    (ν : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hReal :
      Dynamic.parabolic ψ =
          Dynamic.extendFromCentralizer χ j hj (Dynamic.parabolic ν) ∧
        Dynamic.centralizer ψ = (Dynamic.centralizer ν).map j ∧
        Dynamic.unipotent ψ =
          Dynamic.extendFromCentralizer χ j hj (Dynamic.unipotent ν))

local instance ambientPointTopology :
    TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

local instance sourcePointTopology :
    TopologicalSpace (RationalPoint F L.X) := rationalPointTopology F L.X

variable [LocallyCompactSpace (RationalPoint F G.X)]
    [NonarchimedeanGroup (RationalPoint F G.X)]
    (hN : IsClosed ((Dynamic.unipotent ψ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (RationalPoint F G.X)))
    (hU : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (RationalPoint F G.X)))
    (hZ : IsClosed ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (RationalPoint F G.X)))

/-- The actual ambient direct induction agrees with induction in stages,
using the literal inner decomposition supplied by source realization. -/
def ambientInductionIso :
    normalizedInductionFunctor.{u, uV} (dynamic_isSemidirectDecomposition ψ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hN ≅
      leviNormalizedInductionFunctor.{u, uV} hZ
        (Dynamic.realized_centralizer_le χ j hj ν ψ hReal.2.1 (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
        (RealizedLeviTransport.insideDecomposition F χ j hj hc ν ψ hReal) hN ⋙
      normalizedInductionFunctor.{u, max u uV}
        (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU := by
  have : Smooth G.X.hom := hG.smooth
  have : SecondCountableTopology F := localField_secondCountableTopology F
  have : SecondCountableTopology (RationalPoint F G.X) :=
    rationalPoint_secondCountableTopology F G
  let hP := dynamic_isSemidirectDecomposition ψ (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  let hQ := dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  let hInner := RealizedLeviTransport.insideDecomposition F χ j hj hc ν ψ hReal
  have hPQ := Dynamic.realized_parabolic_le χ j hj ν ψ hReal.1 (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  have hML := Dynamic.realized_centralizer_le χ j hj ν ψ hReal.2.1 (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  have hUN := Dynamic.unipotent_le_realized χ j hj ν ψ hReal.2.2 (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  have hNested := Dynamic.nestedLeviDecomposition_of_realization χ j hj ν ψ hReal
  have hprod :
      ((Dynamic.unipotent ψ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (RationalPoint F G.X)) =
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) ⊓ (Dynamic.unipotent ψ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
          Subgroup (RationalPoint F G.X)) *
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (RationalPoint F G.X)) :=
    (hNested (Over.mk (𝟙 (Spec (CommRingCat.of F))))).2.2.2.2.2.1
  have hp : Continuous hQ.projection := continuous_dynamic_projection F G χ
  have hNc : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((Dynamic.unipotent ψ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) :=
    BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
      BruhatTits.dynamicUnipotentCompactOpenContainment F G hG ψ
  have hUc : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) :=
    BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
      BruhatTits.dynamicUnipotentCompactOpenContainment F G hG χ
  have hδN := isUnimodularModulus_of_isLimitOfCompactSubgroups _ hN hNc
  have hδU := isUnimodularModulus_of_isLimitOfCompactSubgroups _ hU hUc
  have hHalf := NestedParabolic.halfCharacterProduct
    hP hQ hZ hN hU hPQ hprod hp hInner
  exact NestedInduction.iso.{u, uV}
    hP hQ hZ hML hInner hN hU hPQ hUN hp hδN hδU hHalf

/-- The inner stage is actual normalized induction in the source representative,
transported back to the ambient outer Levi. -/
def innerSourceIso :
    letI := hZ.locallyCompactSpace
    letI : LocallyCompactSpace (RationalPoint F L.X) :=
      RepresentedDynamicTransport.representative_locallyCompactSpace
        F (Dynamic.centralizer χ) j hj hc hZ
    letI : NonarchimedeanGroup (RationalPoint F L.X) :=
      RepresentedDynamicTransport.representative_nonarchimedeanGroup
        F (Dynamic.centralizer χ) j hj hc
    leviNormalizedInductionFunctor.{u, uV} hZ
        (Dynamic.realized_centralizer_le χ j hj ν ψ hReal.2.1 (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
        (RealizedLeviTransport.insideDecomposition F χ j hj hc ν ψ hReal) hN ≅
      SmoothRep.pullbackFunctor
          (subgroupOfContinuousEquiv
            (Dynamic.realized_centralizer_le χ j hj ν ψ hReal.2.1 (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) ⋙
        SmoothRep.pullbackFunctor
          (RealizedLeviTransport.centralizerEquiv F χ j hj hc ν ψ hReal) ⋙
        normalizedInductionFunctor (dynamic_isSemidirectDecomposition ν (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
          (RealizedLeviTransport.unipotentClosed F χ j hj hc ν ψ hReal hN) ⋙
        SmoothRep.pullbackFunctor
          (RepresentedDynamicTransport.pointEquiv F
            (Dynamic.centralizer χ) j hj hc).symm := by
  letI := hZ.locallyCompactSpace
  letI : LocallyCompactSpace (RationalPoint F L.X) :=
    RepresentedDynamicTransport.representative_locallyCompactSpace
      F (Dynamic.centralizer χ) j hj hc hZ
  letI : NonarchimedeanGroup (RationalPoint F L.X) :=
    RepresentedDynamicTransport.representative_nonarchimedeanGroup
      F (Dynamic.centralizer χ) j hj hc
  let e := RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer χ) j hj hc
  let A := SmoothRep.pullbackFunctor.{u, u, uV}
    (subgroupOfContinuousEquiv
      (Dynamic.realized_centralizer_le χ j hj ν ψ hReal.2.1 (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
  let I := leviNormalizedInductionFunctor.{u, uV} hZ
    (Dynamic.realized_centralizer_le χ j hj ν ψ hReal.2.1 (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
    (RealizedLeviTransport.insideDecomposition F χ j hj hc ν ψ hReal) hN
  have hInsert :
      I ≅ (I ⋙ SmoothRep.pullbackFunctor e) ⋙ SmoothRep.pullbackFunctor e.symm := by
    simpa only [Functor.comp_id, Functor.assoc, ContinuousMulEquiv.symm_symm] using
      (Functor.isoWhiskerLeft I (inversePullbackIso.{u, max u uV} e.symm).symm)
  exact hInsert ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft A
        (RealizedLeviTransport.inductionIso F χ j hj hc ν ψ hReal hN))
      (SmoothRep.pullbackFunctor e.symm)

/-- Direct ambient induction agrees naturally with actual source induction
followed by the outer normalized induction. -/
def inductionInStagesIso :
    letI := hZ.locallyCompactSpace
    letI : LocallyCompactSpace (RationalPoint F L.X) :=
      RepresentedDynamicTransport.representative_locallyCompactSpace
        F (Dynamic.centralizer χ) j hj hc hZ
    letI : NonarchimedeanGroup (RationalPoint F L.X) :=
      RepresentedDynamicTransport.representative_nonarchimedeanGroup
        F (Dynamic.centralizer χ) j hj hc
    normalizedInductionFunctor.{u, uV} (dynamic_isSemidirectDecomposition ψ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hN ≅
      SmoothRep.pullbackFunctor
          (subgroupOfContinuousEquiv
            (Dynamic.realized_centralizer_le χ j hj ν ψ hReal.2.1 (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) ⋙
        SmoothRep.pullbackFunctor
          (RealizedLeviTransport.centralizerEquiv F χ j hj hc ν ψ hReal) ⋙
        normalizedInductionFunctor (dynamic_isSemidirectDecomposition ν (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
          (RealizedLeviTransport.unipotentClosed F χ j hj hc ν ψ hReal hN) ⋙
        SmoothRep.pullbackFunctor
          (RepresentedDynamicTransport.pointEquiv F
            (Dynamic.centralizer χ) j hj hc).symm ⋙
        normalizedInductionFunctor.{u, max u uV}
          (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU := by
  letI := hZ.locallyCompactSpace
  letI : LocallyCompactSpace (RationalPoint F L.X) :=
    RepresentedDynamicTransport.representative_locallyCompactSpace
      F (Dynamic.centralizer χ) j hj hc hZ
  letI : NonarchimedeanGroup (RationalPoint F L.X) :=
    RepresentedDynamicTransport.representative_nonarchimedeanGroup
      F (Dynamic.centralizer χ) j hj hc
  exact ambientInductionIso F hG χ j hj hc ν ψ hReal hN hU hZ ≪≫
    Functor.isoWhiskerRight (innerSourceIso F χ j hj hc ν ψ hReal hN hZ)
      (normalizedInductionFunctor (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU)

/-- On functions, stages evaluate at the source point mapped into the outer
Levi and remove its outer half character. -/
@[simp]
theorem inductionInStagesIso_hom_eval
    (A : SmoothRep.{0, u, uV} ℂ ((Dynamic.centralizer ψ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
    (f : (normalizedInductionFunctor
      (dynamic_isSemidirectDecomposition ψ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hN).obj A)
    (g : RationalPoint F G.X) (l : RationalPoint F L.X) :
    letI := hZ.locallyCompactSpace
    letI : LocallyCompactSpace (RationalPoint F L.X) :=
      RepresentedDynamicTransport.representative_locallyCompactSpace
        F (Dynamic.centralizer χ) j hj hc hZ
    letI : NonarchimedeanGroup (RationalPoint F L.X) :=
      RepresentedDynamicTransport.representative_nonarchimedeanGroup
        F (Dynamic.centralizer χ) j hj hc
    ((SmoothRep.hom
      ((inductionInStagesIso F hG χ j hj hc ν ψ hReal hN hU hZ).app A).hom f).1.1 g).1.1 l =
      ((HaarModulus.closedHalfCharacter ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
        (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))).levi_le_normalizer
        (RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer χ) j hj hc l))⁻¹ :
          ℂˣ) •
        f.1.1
          (((RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer χ) j hj hc l :
            (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) : RationalPoint F G.X) * g) := by
  rfl

end Langlands.Aubert.General.RealizedLeviStages
