import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Contraction into a closed normal subgroup containing the cocharacter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G H U : GroupScheme S}
    (d : H ⟶ G) (χ : (Gm S).toGrp ⟶ G)
    (hd : IsClosedSubgroup d) (hn : (SubgroupFunctor.range d).IsNormal)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range d)

include hd hn hχ in
/-- A closed normal subgroup containing a cocharacter contains every point
contracting to the identity under that cocharacter, on every relative test. -/
theorem unipotent_le_range_of_normal :
    unipotent χ ≤ SubgroupFunctor.range d := by
  rintro T g ⟨e, he, he0⟩
  let a : T ⊗ (Gm S).X ⟶ G.X := snd T (Gm S).X ≫ χ.hom.hom
  let b : T ⊗ (Gm S).X ⟶ G.X := fst T (Gm S).X ≫ g
  have ha : a ∈ (SubgroupFunctor.range d).carrier (T ⊗ (Gm S).X) :=
    hχ _ (SubgroupFunctor.mem_range.mpr ⟨snd T (Gm S).X, rfl⟩)
  have hc : orbit χ g * b⁻¹ ∈
      (SubgroupFunctor.range d).carrier (T ⊗ (Gm S).X) := by
    have hh := ((SubgroupFunctor.range d).carrier _).mul_mem ha
      (hn _ b a⁻¹ (Subgroup.mem_top _) (((SubgroupFunctor.range d).carrier _).inv_mem ha))
    change a * b * a⁻¹ * b⁻¹ ∈ _
    simpa only [mul_assoc] using hh
  let r : T ⊗ AffineLine.scheme S ⟶ G.X :=
    e * (fst T (AffineLine.scheme S) ≫ g)⁻¹
  obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.mp hc
  have : IsClosedImmersion d.hom.hom.left := hd
  obtain ⟨r', hr'⟩ := AffineLine.exists_lift_of_unitInclusion d.hom.hom r c (by
    rw [hc]
    dsimp only [r, b]
    rw [MonObj.comp_mul, GrpObj.comp_inv, he, whiskerLeft_fst_assoc])
  have hi : g⁻¹ ∈ (SubgroupFunctor.range d).carrier T := by
    refine SubgroupFunctor.mem_range.mpr ⟨evalZero r', ?_⟩
    rw [← evalZero_comp, hr']
    dsimp only [r]
    rw [evalZero_mul, evalZero_inv, evalZero_fst, he0, one_mul]
  simpa only [inv_inv] using ((SubgroupFunctor.range d).carrier T).inv_mem hi

variable {iU : U ⟶ G} (hU : (unipotent χ).IsRepresentedBy iU)

/-- The actual factor of any represented dynamic unipotent subgroup through
the closed normal subgroup. -/
def normalUnipotentLift : U ⟶ H := by
  let : IsClosedImmersion d.hom.hom.left := hd
  exact hU.lift
    (⟨Over.mono_of_mono_left d.hom.hom, rfl⟩ :
      (SubgroupFunctor.range d).IsRepresentedBy d)
    (fun T => Subgroup.inclusion (unipotent_le_range_of_normal d χ hd hn hχ T))
    (fun _ _ => rfl)

/-- The lifted subgroup has the original ambient inclusion as its composite. -/
theorem normalUnipotentLift_comp :
    normalUnipotentLift d χ hd hn hχ hU ≫ d = iU := by
  let : IsClosedImmersion d.hom.hom.left := hd
  exact hU.lift_comp_eq
    (⟨Over.mono_of_mono_left d.hom.hom, rfl⟩ :
      (SubgroupFunctor.range d).IsRepresentedBy d)
    (fun T => Subgroup.inclusion (unipotent_le_range_of_normal d χ hd hn hχ T))
    (fun _ _ => rfl) (fun _ _ => rfl)

end Langlands.GroupScheme.Dynamic
