import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductFactors

/-! # Intrinsic identification of the almost-simple product factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G A H : GroupScheme (Spec (CommRingCat.of k))}

/-- An almost-simple closed normal subgroup contained in another almost-simple
closed subgroup has the same all-test range. -/
theorem IsAlmostSimple.range_eq_of_le_of_normal
    (hA : IsAlmostSimple A) (hH : IsAlmostSimple H)
    (a : A ⟶ G) (j : H ⟶ G)
    (ha : IsClosedSubgroup a) (hj : IsClosedSubgroup j)
    (han : (SubgroupFunctor.range a).IsNormal)
    (hle : SubgroupFunctor.range a ≤ SubgroupFunctor.range j) :
    SubgroupFunctor.range a = SubgroupFunctor.range j := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let hjrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  let f := hjrep.factorHom a hle
  have hf : f ≫ j = a := hjrep.factorHom_comp a hle
  have hf' : f.hom.hom ≫ j.hom.hom = a.hom.hom :=
    congrArg (fun v => v.hom.hom) hf
  have hfc : IsClosedSubgroup f := IsClosedSubgroup.of_comp hj (by rwa [hf])
  let : IsClosedImmersion f.hom.hom.left := hfc
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  have hfn : (SubgroupFunctor.range f).IsNormal := by
    intro T g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1
      (han T (g ≫ j.hom.hom) (y ≫ a.hom.hom) (Subgroup.mem_top _)
        (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩))
    refine SubgroupFunctor.mem_range.2 ⟨z, ?_⟩
    apply (cancel_mono j.hom.hom).1
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hf'] using hz
  rcases hH.normalSubgroup_trivial_or_full A f hfc
      hA.isSemisimple.isConnectedReductive.smooth
      hA.isSemisimple.isConnectedReductive.connectedSpace hfn with hbot | htop
  · exfalso
    apply hA.noncommutative
    intro T x y
    have hall (z : T ⟶ A.X) : z = 1 := by
      apply (cancel_mono f.hom.hom).1
      rw [MonObj.one_comp]
      have hz : z ≫ f.hom.hom ∈ (SubgroupFunctor.range f).carrier T :=
        SubgroupFunctor.mem_range.2 ⟨z, rfl⟩
      simpa only [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hz
    rw [hall x, hall y]
  · apply le_antisymm hle
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have hy : y ∈ (SubgroupFunctor.range f).carrier T := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hy
    refine SubgroupFunctor.mem_range.2 ⟨z, ?_⟩
    rw [← hf', ← Category.assoc, hz]

namespace SimplyConnectedAlmostSimpleProduct

variable (D : SimplyConnectedAlmostSimpleProduct G)

/-- The projections of an actual product presentation separate all points. -/
theorem points_ext {T : Over (Spec (CommRingCat.of k))} {x y : T ⟶ G.X}
    (h : ∀ i, x ≫ (D.projection i).hom.hom = y ≫ (D.projection i).hom.hom) :
    x = y := by
  apply (cancel_mono D.iso.hom.hom.hom).1
  apply (piPointsEquiv D.factor T).injective
  funext i
  simpa only [piPointsEquiv_apply, projection, Grp.comp_hom_hom, Category.assoc]
    using h i

@[simp] theorem inclusion_projection_points_self (i : D.Index)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (D.factor i).X) :
    (x ≫ (D.inclusion i).hom.hom) ≫ (D.projection i).hom.hom = x := by
  rw [Category.assoc, ← Grp.comp_hom_hom, inclusion_projection,
    Grp.id_hom_hom, Category.comp_id]

theorem inclusion_projection_points_ne (i j : D.Index) (h : i ≠ j)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (D.factor i).X) :
    (x ≫ (D.inclusion i).hom.hom) ≫ (D.projection j).hom.hom = 1 := by
  simp only [inclusion, projection, Category.assoc,
    ← Grp.comp_hom_hom, Iso.inv_hom_id_assoc]
  exact piFactorInclusionHom_points_ne D.factor i j h x

/-- Distinct indices have distinct all-test subgroup ranges. -/
theorem range_inclusion_injective :
    Function.Injective (fun i => SubgroupFunctor.range (D.inclusion i)) := by
  intro i j hij
  change SubgroupFunctor.range (D.inclusion i) =
    SubgroupFunctor.range (D.inclusion j) at hij
  by_contra hne
  apply (D.isAlmostSimple i).noncommutative
  intro T x y
  have hall (z : T ⟶ (D.factor i).X) : z = 1 := by
    have hz : z ≫ (D.inclusion i).hom.hom ∈
        (SubgroupFunctor.range (D.inclusion j)).carrier T := by
      rw [← hij]
      exact SubgroupFunctor.mem_range.2 ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.1 hz
    have he := congrArg (fun v => v ≫ (D.projection i).hom.hom) hw
    simpa only [inclusion_projection_points_self,
      inclusion_projection_points_ne D j i (Ne.symm hne)] using he.symm
  rw [hall x, hall y]

/-- Every almost-simple closed normal subgroup is exactly one of the
factors of any actual product presentation. -/
theorem existsUnique_range_eq_inclusion [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hH : IsAlmostSimple H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hjn : (SubgroupFunctor.range j).IsNormal) :
    ∃! i, SubgroupFunctor.range j = SubgroupFunctor.range (D.inclusion i) := by
  classical
  let : Smooth H.X.hom := hH.isSemisimple.isConnectedReductive.smooth
  let : ConnectedSpace H.X.left := hH.isSemisimple.isConnectedReductive.connectedSpace
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  suffices hex : ∃ i, SubgroupFunctor.range j =
      SubgroupFunctor.range (D.inclusion i) by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, hi, fun j hj => D.range_inclusion_injective (hj.symm.trans hi)⟩
  by_contra hnone
  push Not at hnone
  have hcomm (i : D.Index) :
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X)
        (y : T ⟶ (D.factor i).X),
        Commute (x ≫ j.hom.hom) (y ≫ (D.inclusion i).hom.hom) := by
    let : Smooth (D.factor i).X.hom :=
      (D.isAlmostSimple i).isSemisimple.isConnectedReductive.smooth
    let : ConnectedSpace (D.factor i).X.left :=
      (D.isAlmostSimple i).isSemisimple.isConnectedReductive.connectedSpace
    rcases hH.range_le_or_commute_of_normal j (D.inclusion i) hj
        (D.isClosedSubgroup_inclusion i) hjn (D.isNormal_range_inclusion i) with
      hle | hc
    · exact False.elim (hnone i
        (hH.range_eq_of_le_of_normal (D.isAlmostSimple i) j (D.inclusion i)
          hj (D.isClosedSubgroup_inclusion i) hjn hle))
    · exact hc
  apply hH.noncommutative
  intro T x y
  apply (commute_iff_eq _ _).2
  apply (cancel_mono j.hom.hom).1
  apply D.points_ext
  intro i
  have he := congrArg (fun v => v ≫ (D.projection i).hom.hom)
    (hcomm i T x ((y ≫ j.hom.hom) ≫ (D.projection i).hom.hom)).eq
  simpa only [MonObj.mul_comp, inclusion_projection_points_self] using he

/-- The unique factor index of an actual almost-simple closed normal subgroup. -/
def indexOfNormalAlmostSimple [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hH : IsAlmostSimple H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hjn : (SubgroupFunctor.range j).IsNormal) : D.Index :=
  (D.existsUnique_range_eq_inclusion hH j hj hjn).exists.choose

theorem range_eq_indexOfNormalAlmostSimple [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hH : IsAlmostSimple H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hjn : (SubgroupFunctor.range j).IsNormal) :
    SubgroupFunctor.range j =
      SubgroupFunctor.range (D.inclusion (D.indexOfNormalAlmostSimple hH j hj hjn)) :=
  (D.existsUnique_range_eq_inclusion hH j hj hjn).exists.choose_spec

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
