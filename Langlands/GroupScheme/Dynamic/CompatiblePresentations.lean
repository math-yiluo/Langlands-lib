import Langlands.GroupScheme.Dynamic.PointedPresentation

/-! # Compatible dynamic presentations at a common pointed neighbourhood -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G P Q : GroupScheme S}

/-- Two actual presentations on the same pointed etale neighbourhood whose
ambient cocharacters have equal values at its specified residue point. -/
structure CompatiblePresentationData (i : P ⟶ G) (j : Q ⟶ G) (s : S) where
  U : Scheme.{u}
  projection : U ⟶ S
  etale : Etale projection
  point : Spec (S.residueField s) ⟶ U
  point_projection : point ≫ projection = S.fromSpecResidueField s
  leftCocharacter : (Gm U).toGrp ⟶ (baseChange projection).obj G
  rightCocharacter : (Gm U).toGrp ⟶ (baseChange projection).obj G
  leftPresents : SubgroupFunctor.range ((baseChange projection).map i) =
    parabolic leftCocharacter
  rightPresents : SubgroupFunctor.range ((baseChange projection).map j) =
    parabolic rightCocharacter
  compatible : baseChangeCocharacter point leftCocharacter =
    baseChangeCocharacter point rightCocharacter

/-- Combine two pointed presentations recovering the same ambient cocharacter. -/
def compatiblePresentationsOfPointed (i : P ⟶ G) (j : Q ⟶ G) (s : S)
    (ν : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj G)
    (L : PointedPresentationData i s ν) (R : PointedPresentationData j s ν) :
    CompatiblePresentationData i j s := by
  let U := pullback L.projection R.projection
  let q₁ : U ⟶ L.U := pullback.fst L.projection R.projection
  let q₂ : U ⟶ R.U := pullback.snd L.projection R.projection
  let p := q₁ ≫ L.projection
  have h₂ : q₂ ≫ R.projection = p := pullback.condition.symm
  let b : Spec (S.residueField s) ⟶ U :=
    pullback.lift L.point R.point (L.point_projection.trans R.point_projection.symm)
  have hb₁ : b ≫ q₁ = L.point := pullback.lift_fst _ _ _
  have hb₂ : b ≫ q₂ = R.point := pullback.lift_snd _ _ _
  let a := S.fromSpecResidueField s
  have hb : b ≫ p = a := by
    rw [← Category.assoc, hb₁]
    exact L.point_projection
  let χ := pullbackCocharacter L.projection q₁ p rfl L.cocharacter
  let ψ := pullbackCocharacter R.projection q₂ p h₂ R.cocharacter
  let : Etale L.projection := L.etale
  let : Etale R.projection := R.etale
  let : Etale q₁ := inferInstance
  refine ⟨U, p, inferInstance, b, hb, χ, ψ,
    pullbackCocharacter_presents L.projection q₁ p rfl i L.cocharacter L.presents,
    pullbackCocharacter_presents R.projection q₂ p h₂ j R.cocharacter R.presents, ?_⟩
  apply (cancel_mono (Descent.pullbackComparison p b a hb G).hom).mp
  have hχ : baseChangeCocharacter b χ ≫
      (Descent.pullbackComparison p b a hb G).hom = ν :=
    (pullbackCocharacter_recovers L.projection q₁ p rfl b L.point a
      hb₁ L.point_projection hb L.cocharacter).trans L.recovers
  have hψ : baseChangeCocharacter b ψ ≫
      (Descent.pullbackComparison p b a hb G).hom = ν :=
    (pullbackCocharacter_recovers R.projection q₂ p h₂ b R.point a
      hb₂ R.point_projection hb R.cocharacter).trans R.recovers
  exact hχ.trans hψ.symm

/-- Relative parabolics with the same canonical residue-fibre range admit
compatible presentations over one pointed etale neighbourhood. -/
def compatiblePresentations (i : P ⟶ G) (j : Q ⟶ G) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (s : S)
    (heq : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i) =
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j)) :
    CompatiblePresentationData i j s := by
  let H :=
    ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup
      (hG.isConnectedReductive_residueFiber s)
      ((baseChange (S.fromSpecResidueField s)).map i) (hi.residueFiber s)
  let ν := Classical.choose H
  have hν := Classical.choose_spec H
  exact compatiblePresentationsOfPointed i j s ν
    (pointedPresentation i hG hi s ν hν)
    (pointedPresentation j hG hj s ν (heq.symm.trans hν))

end Langlands.GroupScheme.Dynamic
