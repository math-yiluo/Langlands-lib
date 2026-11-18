import Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Comparing actual normalizer actions on the full centre -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section BaseChange
variable {S S' : Scheme.{u}} {D C : GroupScheme S} (b : S' ⟶ S) (r : D ⟶ C)

/-- Containment of a full centre in another full centre survives arbitrary pullback. -/
theorem center_le_comap_baseChange (h : center D ≤ (center C).comap r) :
    center ((GroupScheme.baseChange b).obj D) ≤
      (center ((GroupScheme.baseChange b).obj C)).comap ((GroupScheme.baseChange b).map r) := by
  intro U z hz
  change z ≫ ((GroupScheme.baseChange b).map r).hom.hom ∈
    (center ((GroupScheme.baseChange b).obj C)).carrier U
  rw [center_baseChange, SubgroupFunctor.mem_baseChange, baseChangePointsEquiv_comp]
  apply h
  rwa [center_baseChange, SubgroupFunctor.mem_baseChange] at hz

end BaseChange

section Inversion
variable {B : Scheme.{u}} {T A : CommGroupScheme B} {G C D : GroupScheme B}

/-- A supplied full-torus inverter inverts every test point in that torus's range. -/
theorem IsNormalizingPoint.conjugates_inv_of_mem_range
    {j : T.toGrp ⟶ G} {m : Over.mk (𝟙 B) ⟶ G.X}
    (hm : IsNormalizingPoint j m (SpecialLinearTorusAutomorphism.negIso T))
    {U : Over B} {x : U ⟶ G.X} (hx : x ∈ (SubgroupFunctor.range j).carrier U) :
    G.constantPoint m U * x * (G.constantPoint m U)⁻¹ = x⁻¹ := by
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have h := congrArg (fun f : T.toGrp ⟶ G => t ≫ f.hom.hom) hm
  simp only [Grp.comp_hom_hom, ← Category.assoc] at h
  rw [comp_innerIso_hom] at h
  have hi : t ≫ (CommGroupScheme.groupHom
      (SpecialLinearTorusAutomorphism.negIso T).hom).hom.hom = t⁻¹ := by
    change t ≫ (CommGroupScheme.groupHom (-𝟙 T)).hom.hom = _
    rw [← neg_one_zsmul, comp_groupHom_zsmul, zpow_neg_one]
    congr 1
  rw [hi, GrpObj.inv_comp] at h
  exact h

/-- Normalizers with the same action on a torus act identically on the full
centre of its actual centralizer. -/
theorem conjugation_eq_of_same_torus_action
    {i : A.toGrp ⟶ G} {j : C ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j)
    {n m : Over.mk (𝟙 B) ⟶ G.X} {σ : A ≅ A}
    (hn : IsNormalizingPoint i n σ) (hm : IsNormalizingPoint i m σ)
    {U : Over B} {z : U ⟶ C.X} (hz : z ∈ (center C).carrier U) :
    G.constantPoint n U * (z ≫ j.hom.hom) * (G.constantPoint n U)⁻¹ =
      G.constantPoint m U * (z ≫ j.hom.hom) * (G.constantPoint m U)⁻¹ := by
  have hd : IsNormalizingPoint i (m⁻¹ * n) (Iso.refl A) := by
    simpa using hm.inv.mul hn
  have hbase : m⁻¹ * n ∈ (torusCentralizer i).carrier (Over.mk (𝟙 B)) :=
    (mem_torusCentralizer_base_iff i _).mpr (isNormalizingPoint_refl_iff.mp hd)
  have hU := (torusCentralizer i).comp_mem (Over.homMk U.hom (by simp)) hbase
  change G.constantPoint (m⁻¹ * n) U ∈ (torusCentralizer i).carrier U at hU
  rw [← hj.2] at hU
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hU
  have hc := congrArg (fun f => f ≫ j.hom.hom) (commute_of_mem_center hz w).symm.eq
  simp only [MonObj.mul_comp, hw] at hc
  have hconst : G.constantPoint (m⁻¹ * n) U =
      (G.constantPoint m U)⁻¹ * G.constantPoint n U :=
    (G.constantPointHom U).map_mul m⁻¹ n |>.trans
      (congrArg (fun v => v * G.constantPoint n U) ((G.constantPointHom U).map_inv m))
  rw [hconst] at hc
  calc
    G.constantPoint n U * (z ≫ j.hom.hom) * (G.constantPoint n U)⁻¹ =
        G.constantPoint m U *
          (((G.constantPoint m U)⁻¹ * G.constantPoint n U) *
            (z ≫ j.hom.hom) * ((G.constantPoint m U)⁻¹ * G.constantPoint n U)⁻¹) *
          (G.constantPoint m U)⁻¹ := by group
    _ = _ := by rw [hc, mul_inv_cancel_right]

/-- The precise proposition implemented by `full_center_inversion_of_same_torus_action`. -/
def FullCenterInversionComparisonStatement : Prop :=
  ∀ {i : A.toGrp ⟶ G} {j : C ⟶ G} {r : D ⟶ C} (t : T.toGrp ⟶ C)
    (_hj : (torusCentralizer i).IsRepresentedBy j)
    (_hcenter : center D ≤ (center C).comap r)
    (_htorus : center C ≤ SubgroupFunctor.range t)
    {n m : Over.mk (𝟙 B) ⟶ G.X} {σ : A ≅ A}
    (_hn : IsNormalizingPoint i n σ) (_hm : IsNormalizingPoint i m σ)
    (_hminv : IsNormalizingPoint (t ≫ j) m (SpecialLinearTorusAutomorphism.negIso T))
    {U : Over B} {z : U ⟶ D.X} (_hz : z ∈ (center D).carrier U),
    G.constantPoint n U * (z ≫ (r ≫ j).hom.hom) * (G.constantPoint n U)⁻¹ =
      (z ≫ (r ≫ j).hom.hom)⁻¹

/-- Inversion of a maximal containing torus transfers to the full centre of any
subgroup whose centre maps into the full centralizer centre. -/
theorem full_center_inversion_of_same_torus_action
    {i : A.toGrp ⟶ G} {j : C ⟶ G} {r : D ⟶ C} (t : T.toGrp ⟶ C)
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (hcenter : center D ≤ (center C).comap r)
    (htorus : center C ≤ SubgroupFunctor.range t)
    {n m : Over.mk (𝟙 B) ⟶ G.X} {σ : A ≅ A}
    (hn : IsNormalizingPoint i n σ) (hm : IsNormalizingPoint i m σ)
    (hminv : IsNormalizingPoint (t ≫ j) m (SpecialLinearTorusAutomorphism.negIso T))
    {U : Over B} {z : U ⟶ D.X} (hz : z ∈ (center D).carrier U) :
    G.constantPoint n U * (z ≫ (r ≫ j).hom.hom) * (G.constantPoint n U)⁻¹ =
      (z ≫ (r ≫ j).hom.hom)⁻¹ := by
  have hzC : z ≫ r.hom.hom ∈ (center C).carrier U := hcenter U hz
  have hrange : z ≫ (r ≫ j).hom.hom ∈ (SubgroupFunctor.range (t ≫ j)).carrier U := by
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp (htorus U hzC)
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨v, ?_⟩
    simpa only [Grp.comp_hom_hom, ← Category.assoc] using
      congrArg (fun f => f ≫ j.hom.hom) hv
  have hsame := conjugation_eq_of_same_torus_action hj hn hm hzC
  simp only [Grp.comp_hom_hom, ← Category.assoc] at hsame ⊢
  exact hsame.trans (hminv.conjugates_inv_of_mem_range hrange)

end Inversion
end Langlands.GroupScheme
