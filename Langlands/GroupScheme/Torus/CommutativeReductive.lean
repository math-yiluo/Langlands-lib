import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceProof
import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent

/-! # Commutative reductive group schemes are relative tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A relative maximal torus in a commutative reductive group is the whole
ambient group, with its specified inclusion. -/
def commutativeReductiveMaximalTorusIso
    {S : Scheme.{u}} {G T : CommGroupScheme S} (hG : IsReductive G.toGrp)
    (hT : RelativeTorus.IsTorus T.toGrp) (t : T.toGrp ⟶ G.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t) :
    G.toGrp ≅ T.toGrp := by
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  have htop : (⊤ : SubgroupFunctor G.toGrp) ≤ SubgroupFunctor.range t := by
    rw [← relativeTorusCentralizer_eq_range_of_fibrewiseMaximal hG hT t ht hmax]
    intro U x _ V a y
    exact Commute.all _ _
  have htRep : (SubgroupFunctor.range t).IsRepresentedBy t := ⟨inferInstance, rfl⟩
  have hidRep : (SubgroupFunctor.range t).IsRepresentedBy (𝟙 G.toGrp) := by
    refine ⟨inferInstance, le_antisymm ?_ ?_⟩
    · intro U x _
      exact htop U (Subgroup.mem_top x)
    · intro U x _
      exact SubgroupFunctor.mem_range.mpr ⟨x, by simp⟩
  exact hidRep.isoOfIsRepresentedBy htRep

@[reassoc (attr := simp)]
theorem commutativeReductiveMaximalTorusIso_hom_comp
    {S : Scheme.{u}} {G T : CommGroupScheme S} (hG : IsReductive G.toGrp)
    (hT : RelativeTorus.IsTorus T.toGrp) (t : T.toGrp ⟶ G.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t) :
    (commutativeReductiveMaximalTorusIso hG hT t ht hmax).hom ≫ t = 𝟙 G.toGrp := by
  unfold commutativeReductiveMaximalTorusIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- Every commutative reductive group scheme over an arbitrary base is a
relative torus. -/
theorem relativeTorus_of_commutative_reductive
    {S : Scheme.{u}} (G : CommGroupScheme S) (hG : IsReductive G.toGrp) :
    RelativeTorus.IsTorus G.toGrp := by
  classical
  choose R hR f hf hx I hI i hi hmax using
    exists_etale_affine_split_maximalTorus S G.toGrp hG
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    Scheme.Cover.mkOfCovers (P := @Etale) S (fun s => Spec (CommRingCat.of (R s))) f
      (fun s => ⟨s, hx s⟩) hf
  refine ⟨𝒰, fun s => ?_⟩
  let Gs := (CommGroupScheme.baseChange (f s)).obj G
  let Ts := splitTorus.commGroupScheme (Spec (CommRingCat.of (R s))) (I s)
  have hTs : IsSplitTorus Ts.toGrp := isSplitTorus_splitTorus (I s)
  let e : Gs.toGrp ≅ Ts.toGrp := commutativeReductiveMaximalTorusIso
    (hG.baseChange (f s)) (RelativeTorus.IsTorus.of_isSplitTorus hTs)
    (i s) (hi s) (hmax s)
  exact IsSplitTorus.of_iso e hTs

end Langlands.GroupScheme
