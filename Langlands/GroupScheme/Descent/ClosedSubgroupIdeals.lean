import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Closed subgroup descent through defining ideals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- An ideal sheaf on the target whose pullback is the specified ideal sheaf. -/
structure DefiningIdealDescent {X Y : Scheme.{u}} (p : X ⟶ Y)
    (I : X.IdealSheafData) where
  ideal : Y.IdealSheafData
  eq_comap : I = ideal.comap p

/-- Factoring through a closed subgroup is detected by the full ideal sheaf on
every relative test scheme. -/
theorem IsClosedSubgroup.mem_range_iff_ker_le
    {S : Scheme.{u}} {H G : GroupScheme S} {i : H ⟶ G}
    (hi : IsClosedSubgroup i) {T : Over S} (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range i).carrier T ↔
      i.hom.hom.left.ker ≤ x.left.ker := by
  let : IsClosedImmersion i.hom.hom.left := hi
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact Scheme.Hom.le_ker_comp y.left i.hom.hom.left
  · intro h
    let a := IsClosedImmersion.lift i.hom.hom.left x.left h
    have ha : a ≫ i.hom.hom.left = x.left :=
      IsClosedImmersion.lift_fac _ _ _
    refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
    rw [← Over.w i.hom.hom, ← Category.assoc, ha]
    exact Over.w x

/-- Vanishing of a pulled back ideal is equivalent to vanishing along the
composite morphism. -/
theorem ideal_comap_le_ker_iff {X Y Z : Scheme.{u}}
    (J : Y.IdealSheafData) (f : X ⟶ Y) (g : Z ⟶ X) :
    J.comap f ≤ g.ker ↔ J ≤ (g ≫ f).ker := by
  rw [Scheme.Hom.ker_comp]
  exact Scheme.IdealSheafData.le_map_iff_comap_le.symm

open Descent

/-- A closed subgroup whose full defining ideal comes by pullback from the
original ambient scheme has equal images on the double overlap. -/
theorem IsClosedSubgroup.overlap_range_eq_of_idealSheaf_descent
    {B S : Scheme.{u}} (p : S ⟶ B) {G : GroupScheme B}
    {H : GroupScheme S} {i : H ⟶ (GroupScheme.baseChange p).obj G}
    (hi : IsClosedSubgroup i) (J : G.X.left.IdealSheafData)
    (hJ : i.hom.hom.left.ker = J.comap (pullback.fst G.X.hom p)) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i) := by
  rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom,
    SubgroupFunctor.range_baseChangeHom]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_baseChange,
    SubgroupFunctor.mem_baseChange, hi.mem_range_iff_ker_le,
    hi.mem_range_iff_ker_le, hJ, ideal_comap_le_ker_iff,
    ideal_comap_le_ker_iff]
  simp only [baseChangePointsEquiv_left, Over.comp_left, Category.assoc]
  let e := (Over.forget _).mapIso ((Grp.forget _).mapIso (canonicalOverlap p G))
  have he : e.hom ≫ pullback.fst ((GroupScheme.baseChange p).obj G).X.hom (snd p) ≫
      pullback.fst G.X.hom p =
    pullback.fst ((GroupScheme.baseChange p).obj G).X.hom (fst p) ≫
      pullback.fst G.X.hom p := canonicalOverlap_fst p G
  have he' : e.inv ≫ pullback.fst ((GroupScheme.baseChange p).obj G).X.hom (fst p) ≫
      pullback.fst G.X.hom p =
    pullback.fst ((GroupScheme.baseChange p).obj G).X.hom (snd p) ≫
      pullback.fst G.X.hom p := by
    rw [← he, Iso.inv_hom_id_assoc]
  exact (congrArg (fun a => J ≤ a.ker)
    (congrArg (fun a => x.left ≫ a) he')).to_iff

/-- Descended defining-ideal data supplies the all-test overlap condition for
effective closed-subgroup descent. -/
theorem IsClosedSubgroup.overlap_range_eq_of_definingIdealDescent
    {B S : Scheme.{u}} (p : S ⟶ B) {G : GroupScheme B}
    {H : GroupScheme S} {i : H ⟶ (GroupScheme.baseChange p).obj G}
    (hi : IsClosedSubgroup i)
    (d : DefiningIdealDescent (pullback.fst G.X.hom p) i.hom.hom.left.ker) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i) :=
  hi.overlap_range_eq_of_idealSheaf_descent p d.ideal d.eq_comap

end Langlands.GroupScheme
