import Langlands.GroupScheme.Dynamic.UnitriangularEmbedding
import Langlands.GroupScheme.Dynamic.GeometricMaximality
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.Dynamic.Conjugation
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.UnitriangularUnipotentStatement
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalStatement

/-! # Structural reduction for dynamic geometric unipotent radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section UnitriangularModel

variable {k : Type u} [Field k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : U ⟶ G)
    (hU : (unipotent χ).IsRepresentedBy j) (hj : IsClosedSubgroup j)

/-- A dimension of a standard unitriangular group admitting a closed embedding of the
represented dynamic identity-limit group. -/
def unitriangularDimension : ℕ :=
  (exists_closed_unitriangularEmbedding χ j hU hj).choose

/-- Choose an actual closed embedding of the dynamic identity-limit representative into
the standard upper unitriangular scheme. -/
def unitriangularModel :
    U ⟶ GeneralLinear.blockUnipotentScheme (Fin (unitriangularDimension χ j hU hj))
      (CommRingCat.of k) (fun i => -(i.val : ℤ)) :=
  (exists_closed_unitriangularEmbedding χ j hU hj).choose_spec.choose

theorem isClosedSubgroup_unitriangularModel :
    IsClosedSubgroup (unitriangularModel χ j hU hj) :=
  (exists_closed_unitriangularEmbedding χ j hU hj).choose_spec.choose_spec

include χ j hU hj

/-- The two exact general unipotence inputs imply unipotence of any closed representative
of a dynamic identity-limit subgroup of an affine locally finite-type group. -/
theorem isUnipotent_of_unitriangular_inputs
    (htri : UnitriangularUnipotentStatement.{u})
    (hclosed : UnipotentClosedSubgroupStatement.{u}) : IsUnipotent U := by
  let N := unitriangularDimension χ j hU hj
  let H := GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k)
    (fun i => -(i.val : ℤ))
  have hinc := GeneralLinear.isClosedSubgroup_blockUnipotentHom (Fin N)
    (CommRingCat.of k) (fun i => -(i.val : ℤ))
  let : IsAffineHom (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme (Fin N) (CommRingCat.of k)
  let : Smooth (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    GeneralLinear.smoothStatement (Fin N) (CommRingCat.of k)
  let : IsAffineHom H.X.hom := hinc.isAffineHom
  let : LocallyOfFiniteType H.X.hom := hinc.locallyOfFiniteType
  exact hclosed k H U (unitriangularModel χ j hU hj)
    (isClosedSubgroup_unitriangularModel χ j hU hj) (htri k N)

end UnitriangularModel

section Normality

variable {S : Scheme.{u}} {G P U : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) (p : P ⟶ G) (r : U ⟶ P)
    (hP : (parabolic χ).IsRepresentedBy p)
    (hU : (unipotent χ).IsRepresentedBy (r ≫ p))

include χ p hP hU

/-- The compatible identity-limit representative is normal in the represented dynamic
parabolic, on every test scheme. -/
theorem range_unipotentRepresentative_isNormal : (SubgroupFunctor.range r).IsNormal := by
  intro T g x _ hx
  have hg : g ≫ p.hom.hom ∈ (parabolic χ).carrier T := by
    rw [← hP.2]
    exact ⟨g, rfl⟩
  obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have ha : (a ≫ r.hom.hom) ≫ p.hom.hom ∈ (unipotent χ).carrier T := by
    rw [← hU.2]
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨a, ?_⟩
    simp only [Grp.comp_hom_hom, Category.assoc]
  have hc := unipotent_isNormalizedBy_parabolic χ T
    (g ≫ p.hom.hom) ((a ≫ r.hom.hom) ≫ p.hom.hom) hg ha
  rw [← hU.2] at hc
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hc
  refine SubgroupFunctor.mem_range.mpr ⟨b, ?_⟩
  apply hP.1.right_cancellation
  simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.mul_comp, GrpObj.inv_comp] using hb

end Normality

section GeometricStructure

variable {k : Type u} [Field k]
    {G Z P U : GroupScheme (Spec (CommRingCat.of k))}
    [hGaff : IsAffineHom G.X.hom] [hGsm : Smooth G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (z : Z ⟶ G) (p : P ⟶ G) (r : U ⟶ P)
    (hP : (parabolic χ).IsRepresentedBy p)
    (hU : (unipotent χ).IsRepresentedBy (r ≫ p))
    (hz : (centralizer χ).IsRepresentedBy z)

include χ z p hP hU hz hGaff hGsm

/-- The concrete unipotence inputs and reductivity of the represented centralizer imply
the full geometric radical predicate, including geometric greatestness. -/
theorem isGeometricUnipotentRadical_of_unitriangular_inputs
    (htri : UnitriangularUnipotentStatement.{u})
    (hclosed : UnipotentClosedSubgroupStatement.{u})
    (hZ : IsConnectedReductive Z) : IsGeometricUnipotentRadical r := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hpc := Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP
  have hj := Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hU
  have hzc := Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hz
  have hrc : IsClosedSubgroup r := IsClosedSubgroup.of_comp hpc hj
  have hsm : Smooth U.X.hom := (dynamicSmooth k G χ U (r ≫ p)).2.2 hU
  have hc : ConnectedSpace U.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hU
  have hu : IsUnipotent U :=
    isUnipotent_of_unitriangular_inputs χ (r ≫ p) hU hj htri hclosed
  have hn := range_unipotentRepresentative_isNormal χ p r hP hU
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  let : LocallyOfFiniteType (B.obj G).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hUb : (unipotent (baseChangeCocharacter b χ)).IsRepresentedBy
      (B.map (r ≫ p)) := by
    rw [unipotent_baseChange]
    exact hU.baseChange b
  have hcg : ConnectedSpace (B.obj U).X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent
      (B.obj G) (baseChangeCocharacter b χ) hUb
  have hug : IsUnipotent (B.obj U) :=
    isUnipotent_of_unitriangular_inputs (baseChangeCocharacter b χ)
      (B.map (r ≫ p)) hUb (hj.baseChange b) htri hclosed
  exact isGeometricUnipotentRadical_of_reductive_centralizer χ z p r
    hP hpc hU hz hzc hZ hrc hsm hc hu hn hcg hug

end GeometricStructure

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme

/-- Reduce the exact universal dynamic-radical target to the separately owned concrete
unitriangular unipotence, closed-subgroup unipotence and dynamic centralizer results. -/
theorem dynamicGeometricUnipotentRadical_of_unipotence_centralizer
    (htri : UnitriangularUnipotentStatement.{u})
    (hclosed : UnipotentClosedSubgroupStatement.{u})
    (hcentralizer : DynamicCentralizerReductiveStatement.{u}) :
    DynamicGeometricUnipotentRadicalStatement.{u} := by
  intro k _ G hG χ P U p r hP hU
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact Dynamic.isGeometricUnipotentRadical_of_unitriangular_inputs
    χ (Dynamic.Affine.centralizerHom χ) p r hP hU
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ) htri hclosed
    (hcentralizer k G hG χ _ (Dynamic.Affine.centralizerHom χ)
      (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ))

end Langlands.GroupScheme
