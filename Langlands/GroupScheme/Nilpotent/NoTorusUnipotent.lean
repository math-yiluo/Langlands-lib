import Langlands.GroupScheme.Absolute.CharacterCocharacter
import Langlands.GroupScheme.Nilpotent.GeometricCocharacterVanishing
import Langlands.GroupScheme.Nilpotent.CentralQuotient
import Langlands.GroupScheme.Nilpotent.CentralTorusStatement
import Langlands.GroupScheme.Unipotent.FieldReflectionProof

/-! # Unipotence without tori for geometrically nilpotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Over every field, a smooth connected affine geometrically nilpotent group
is unipotent when every homomorphism from a torus is trivial. -/
def NilpotentNoTorusUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsNilpotentGroupScheme G →
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ G, SubgroupFunctor.range f = ⊥) →
    IsUnipotent G

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Geometric cocharacter vanishing and the solvable character criterion
give unipotence over the algebraic closure, which descends to the original field. -/
theorem IsNilpotentGroupScheme.isUnipotent_of_no_torus
    (hG : IsNilpotentGroupScheme G)
    (hno : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ G, SubgroupFunctor.range f = ⊥) :
    IsUnipotent G := by
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let GK := (GroupScheme.baseChange b).obj G
  have : Smooth GK.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace GK.X.left :=
    GroupScheme.connectedSpace_baseChange_of_smooth_affine G b
  apply IsUnipotent.of_baseChange (K := K)
  exact AbsoluteNoCocharacter.isUnipotent_of_gm_hom_eq_zero
    (hG.baseChange b).isSolvableGroupScheme
    (hG.gm_hom_eq_zero_over_algebraicClosure hno)

/-- The nilpotent case of the arbitrary-field no-torus theorem. -/
theorem nilpotentNoTorusUnipotent : NilpotentNoTorusUnipotentStatement.{u} := by
  intro k _ G _ _ _ hG hno
  exact hG.isUnipotent_of_no_torus hno

/-- A central maximal torus has an affine unipotent fppf quotient over the
original field; no geometric preservation of maximal tori is required. -/
theorem nilpotentCentralTorus : NilpotentCentralTorusStatement.{u} := by
  intro k _ G _ _ _ hG
  let D := hG.centralTorusQuotient
  let : Smooth D.quotient.X.hom := D.smooth_quotient
  let : IsAffineHom D.quotient.X.hom := D.affine_quotient
  let : ConnectedSpace D.quotient.X.left := D.connected_quotient
  exact ⟨D.torus, D.inclusion, D.quotient, D.projection, D.maximal_torus,
    D.central, D.affine_quotient,
    D.nilpotent_quotient.isUnipotent_of_no_torus D.no_tori, D.fppf_quotient⟩

end Langlands.GroupScheme
