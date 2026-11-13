import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.SmoothOverRing
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Smooth connected fibres of dynamic subgroups over any base scheme: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace DynamicBaseSmoothConnected

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Base changes of a smooth group scheme are smooth. -/
theorem smooth_baseChange [Smooth G.X.hom] {T : Scheme.{u}} (y : T ⟶ S) :
    Smooth ((GroupScheme.baseChange y).obj G).X.hom := by
  change Smooth (pullback.snd G.X.hom y)
  infer_instance

/-- Base changes of an affine group scheme are affine. -/
theorem isAffineHom_baseChange [IsAffineHom G.X.hom] {T : Scheme.{u}} (y : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange y).obj G).X.hom :=
  MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom y ‹_›

/-- A group scheme over `S` is smooth as soon as its base change along every morphism from an
affine scheme is smooth: smoothness is local on the target. -/
theorem smooth_of_baseChange
    (h : ∀ (R : Type u) [CommRing R] (y : Spec (CommRingCat.of R) ⟶ S),
      Smooth ((GroupScheme.baseChange y).obj H).X.hom) :
    Smooth H.X.hom :=
  IsZariskiLocalAtTarget.of_openCover (P := @Smooth) S.affineOpenCover.openCover fun i =>
    h (S.affineOpenCover.X i) (S.affineOpenCover.f i)

/-- A group scheme over `S` has geometrically connected fibres as soon as its base change along
every field-valued point is connected. -/
theorem geometricallyConnected_of_baseChange
    (h : ∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ S),
      ConnectedSpace ((GroupScheme.baseChange y).obj H).X.left) :
    GeometricallyConnected H.X.hom :=
  ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => h K y⟩

/-- The field-valued fibres of a geometrically connected `G` are connected. -/
theorem connectedSpace_baseChange [GeometricallyConnected G.X.hom] {K : Type u} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) :
    ConnectedSpace ((GroupScheme.baseChange y).obj G).X.left :=
  (geometrically_iff_of_isClosedUnderIsomorphisms.mp
    (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom))) K y

end DynamicBaseSmoothConnected

open DynamicBaseSmoothConnected in
/-- Proof of `DynamicBaseSmoothConnectedStatement`: over each affine scheme mapping to `S`, a
representative base-changes to a representative of the dynamic subgroup of the base-changed
cocharacter, which is smooth by `dynamicSmooth_ring`; over each field point, `dynamicConnected`
gives connectedness. -/
theorem dynamicBaseSmoothConnected : DynamicBaseSmoothConnectedStatement.{u} := by
  intro S G _ _ χ H j
  refine ⟨fun hj => ⟨?_, ?_⟩, fun hj => ⟨?_, fun hG => ?_⟩, fun hj => ⟨?_, fun hG => ?_⟩⟩
  · refine smooth_of_baseChange fun R _ y => ?_
    let := smooth_baseChange (G := G) y
    let := isAffineHom_baseChange (G := G) y
    have hjR := hj.baseChange y
    rw [← Dynamic.unipotent_baseChange] at hjR
    exact (dynamicSmooth_ring R _ (Dynamic.baseChangeCocharacter y χ) _ _).2.2 hjR
  · refine geometricallyConnected_of_baseChange fun K _ y => ?_
    let := smooth_baseChange (G := G) y
    let := isAffineHom_baseChange (G := G) y
    have hjK := hj.baseChange y
    rw [← Dynamic.unipotent_baseChange] at hjK
    exact (dynamicConnected K _ (Dynamic.baseChangeCocharacter y χ) _ _).1 hjK
  · refine smooth_of_baseChange fun R _ y => ?_
    let := smooth_baseChange (G := G) y
    let := isAffineHom_baseChange (G := G) y
    have hjR := hj.baseChange y
    rw [← Dynamic.parabolic_baseChange] at hjR
    exact (dynamicSmooth_ring R _ (Dynamic.baseChangeCocharacter y χ) _ _).1 hjR
  · refine geometricallyConnected_of_baseChange fun K _ y => ?_
    let := smooth_baseChange (G := G) y
    let := isAffineHom_baseChange (G := G) y
    have hjK := hj.baseChange y
    rw [← Dynamic.parabolic_baseChange] at hjK
    exact ((dynamicConnected K _ (Dynamic.baseChangeCocharacter y χ) _ _).2
      (connectedSpace_baseChange y)).1 hjK
  · refine smooth_of_baseChange fun R _ y => ?_
    let := smooth_baseChange (G := G) y
    let := isAffineHom_baseChange (G := G) y
    have hjR := hj.baseChange y
    rw [← Dynamic.centralizer_baseChange] at hjR
    exact (dynamicSmooth_ring R _ (Dynamic.baseChangeCocharacter y χ) _ _).2.1 hjR
  · refine geometricallyConnected_of_baseChange fun K _ y => ?_
    let := smooth_baseChange (G := G) y
    let := isAffineHom_baseChange (G := G) y
    have hjK := hj.baseChange y
    rw [← Dynamic.centralizer_baseChange] at hjK
    exact ((dynamicConnected K _ (Dynamic.baseChangeCocharacter y χ) _ _).2
      (connectedSpace_baseChange y)).2 hjK

end Langlands.GroupScheme
