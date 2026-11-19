import Langlands.GroupScheme.Torus.MultiplicativeTypeAffineInfinitesimalCentrality
import Langlands.GroupScheme.CentralIsogeny.BaseChange

/-! # Transport of fibre equality and centrality along composite base changes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralRigidityTransport

variable {S S' S'' : Scheme.{u}}

/-- The comparison `baseChange (c ≫ b) ≅ baseChange b ⋙ baseChange c`. -/
noncomputable def compIso (b : S' ⟶ S) (c : S'' ⟶ S') :
    GroupScheme.baseChange (c ≫ b) ≅ GroupScheme.baseChange b ⋙ GroupScheme.baseChange c :=
  Functor.mapGrpNatIso (Over.pullbackComp c b) ≪≫ Functor.mapGrpCompIso

theorem compIso_naturality (b : S' ⟶ S) (c : S'' ⟶ S') {H G : GroupScheme S} (w : H ⟶ G) :
    (GroupScheme.baseChange (c ≫ b)).map w ≫ (compIso b c).hom.app G =
      (compIso b c).hom.app H ≫ (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map w) :=
  (compIso b c).hom.naturality w

theorem baseChange_comp_map_eq_iff (b : S' ⟶ S) (c : S'' ⟶ S') {H G : GroupScheme S}
    (u v : H ⟶ G) :
    (GroupScheme.baseChange (c ≫ b)).map u = (GroupScheme.baseChange (c ≫ b)).map v ↔
      (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map u) =
        (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map v) := by
  constructor
  · intro h
    rw [← cancel_epi ((compIso b c).hom.app H), ← compIso_naturality, ← compIso_naturality, h]
  · intro h
    rw [← cancel_mono ((compIso b c).hom.app G), compIso_naturality, compIso_naturality, h]

/-- Fibre equality and centrality pass to any further base change factoring through `b`. -/
theorem baseChange_eq_and_central_of_factor (b : S' ⟶ S) (c : S'' ⟶ S') (d : S'' ⟶ S)
    (hd : c ≫ b = d) {H G : GroupScheme S} (u v : H ⟶ G)
    (heq : (GroupScheme.baseChange b).map u = (GroupScheme.baseChange b).map v)
    (hc : IsCentral ((GroupScheme.baseChange b).map u)) :
    (GroupScheme.baseChange d).map u = (GroupScheme.baseChange d).map v ∧
      IsCentral ((GroupScheme.baseChange d).map u) := by
  subst hd
  exact ⟨(baseChange_comp_map_eq_iff b c u v).2 (by rw [heq]),
    (MultiplicativeTypeAffineInfinitesimalCentrality.isCentral_baseChange_comp_iff b c u).2
      (hc.baseChange c)⟩

end Langlands.GroupScheme.CentralRigidityTransport
