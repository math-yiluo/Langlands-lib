import Langlands.GroupScheme.Nilpotent.TorusDescent
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupRangeTransport
import Langlands.GroupScheme.Torus.GeometricCocharacterVanishing

/-! # Geometric cocharacter vanishing for nilpotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A smooth connected affine geometrically nilpotent group without base-field
torus maps has no nonzero cocharacters over the algebraic closure. -/
def NilpotentGeometricCocharacterVanishingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsNilpotentGroupScheme G →
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ G, SubgroupFunctor.range f = ⊥) →
    ∀ nu : (Gm (Spec (CommRingCat.of (AlgebraicClosure k)))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G,
      nu = 0

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Centrality of geometric tori reduces geometric cocharacter vanishing to the
full commutative centre, which need not be smooth. -/
theorem IsNilpotentGroupScheme.gm_hom_eq_zero_over_algebraicClosure
    (hG : IsNilpotentGroupScheme G)
    (hno : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ G, SubgroupFunctor.range f = ⊥)
    (nu : (Gm (Spec (CommRingCat.of (AlgebraicClosure k)))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G) :
    nu = 0 := by
  obtain ⟨Z, z, hz, hclosed⟩ :=
    fieldFixedSubgroupRepresentability k G G inferInstance
      (AutomorphicAction.conjugation (𝟙 G))
  have hcenter : (center G).IsRepresentedBy z :=
    ⟨hz.1, hz.2.trans (conjugation_id_fixedSubgroup_eq_center G)⟩
  let : IsClosedImmersion z.hom.hom.left := hclosed
  let : Mono z.hom.hom := hcenter.1
  have hcentral : IsCentral z :=
    (isCentral_iff_range_le_center z).2 (le_of_eq hcenter.2)
  let C := hcentral.commGroupScheme
  have : IsAffineHom C.toGrp.X.hom := by
    change IsAffineHom Z.X.hom
    rw [← Over.w z.hom.hom]
    infer_instance
  have : IsAffine C.toGrp.X.left := isAffine_of_isAffineHom C.toGrp.X.hom
  have : LocallyOfFiniteType C.toGrp.X.hom := by
    change LocallyOfFiniteType Z.X.hom
    rw [← Over.w z.hom.hom]
    infer_instance
  have hC : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))),
      IsTorus T.toGrp → ∀ f : T.toGrp ⟶ C.toGrp, SubgroupFunctor.range f = ⊥ := by
    intro T hT f
    exact (SubgroupFunctor.range_comp_eq_bot_iff f z).1 (hno T hT (f ≫ z))
  let b := algebraBaseMap k (AlgebraicClosure k)
  let GK := (GroupScheme.baseChange b).obj G
  let zK := (GroupScheme.baseChange b).map z
  have hcenterK : (center GK).IsRepresentedBy zK := by
    rw [center_baseChange]
    exact hcenter.baseChange b
  have : Smooth GK.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace GK.X.left :=
    GroupScheme.connectedSpace_baseChange_of_smooth_affine G b
  have hnu : SubgroupFunctor.range nu ≤ center GK :=
    (isCentral_iff_range_le_center nu).1
      ((hG.baseChange b).isCentral_of_isTorus _
        isSplitTorus_gm.isTorus nu)
  have hfactor := CocharacterDatum.gm_hom_eq_zero_over_algebraicClosure
    (Z := C) hC (hcenterK.factorHom nu hnu)
  rw [← hcenterK.factorHom_comp nu hnu, hfactor]
  simp

/-- The nilpotent geometric vanishing implication in the original universe. -/
theorem nilpotentGeometricCocharacterVanishing :
    NilpotentGeometricCocharacterVanishingStatement.{u} := by
  intro k _ G _ _ _ hG hno nu
  exact hG.gm_hom_eq_zero_over_algebraicClosure hno nu

end Langlands.GroupScheme
