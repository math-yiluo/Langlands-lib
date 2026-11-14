import Langlands.GroupScheme.RelativeLevi.TorusLeviLocal

/-! # Base change of Levi witnesses in a prescribed-torus presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

namespace TorusLeviWitness

variable {S S' : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- Every unique Levi witness containing the prescribed group represents
the centralizer of a defining cocharacter. -/
theorem representsCentralizer (w : TorusLeviWitness t)
    (d : TorusDynamicPresentation i t)
    (hDynamic : DynamicRelativeLeviStatement.{u}) (hG : IsReductive G) :
    (Dynamic.centralizer (d.cocharacter ≫ t ≫ i)).IsRepresentedBy (w.inclusion ≫ i) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : LocallyOfFinitePresentation G.X.hom := inferInstance
  let chi := d.cocharacter ≫ t ≫ i
  obtain ⟨U, iU, _, _, hU⟩ := (dynamicBaseRepresentability S G chi).2.1
  obtain ⟨Z, iZ, _, _, hZ⟩ := (dynamicBaseRepresentability S G chi).2.2
  let l := Dynamic.centralizerToParabolic d.represents hZ
  have hlcomp : l ≫ i = iZ := Dynamic.centralizerToParabolic_comp d.represents hZ
  have hl : IsRelativeLeviSubgroup l :=
    (hDynamic S G P U Z chi i iU iZ hG d.represents hU hZ).2.2 l hlcomp
  let tau := Dynamic.torusFactor (t ≫ i) d.cocharacter hZ
  have htau : tau ≫ l = t := d.represents.hom_ext (by
    rw [Category.assoc, hlcomp]
    exact Dynamic.torusFactor_comp (t ≫ i) d.cocharacter hZ)
  have hcontains : SubgroupFunctor.range t ≤ SubgroupFunctor.range l := by
    intro V x hx
    obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨a ≫ tau.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, htau]
  have hw := w.unique Z l hl hcontains
  have hamb : SubgroupFunctor.range (w.inclusion ≫ i) =
      SubgroupFunctor.range (l ≫ i) := le_antisymm
    ((SubgroupFunctor.range_comp_le_iff_of_mono w.inclusion l i d.represents.1).mpr hw.ge)
    ((SubgroupFunctor.range_comp_le_iff_of_mono l w.inclusion i d.represents.1).mpr hw.le)
  refine ⟨?_, ?_⟩
  · let : Mono w.inclusion.hom.hom := w.isLevi.isClosedSubgroup.mono_overHom
    let : Mono i.hom.hom := d.represents.1
    change Mono (w.inclusion.hom.hom ≫ i.hom.hom)
    infer_instance
  · rw [hamb, hlcomp]
    exact hZ.2

/-- In a dynamic presentation, the actual pulled-back inclusion is a Levi
subgroup after every base change. -/
theorem isLevi_baseChange (w : TorusLeviWitness t)
    (d : TorusDynamicPresentation i t)
    (hDynamic : DynamicRelativeLeviStatement.{u}) (hG : IsReductive G)
    (b : S' ⟶ S) :
    IsRelativeLeviSubgroup ((GroupScheme.baseChange b).map w.inclusion) := by
  let G' := (GroupScheme.baseChange b).obj G
  let P' := (GroupScheme.baseChange b).obj P
  let i' := (GroupScheme.baseChange b).map i
  let t' := (GroupScheme.baseChange b).map t
  let d' := d.baseChange b
  let chi' := d'.cocharacter ≫ t' ≫ i'
  have hG' : IsReductive G' := hG.baseChange b
  let : Smooth G'.X.hom := hG'.smooth
  let : IsAffineHom G'.X.hom := hG'.isAffineHom
  let : LocallyOfFinitePresentation G'.X.hom := inferInstance
  obtain ⟨U', iU', _, _, hU'⟩ := (dynamicBaseRepresentability S' G' chi').2.1
  have hZ' : (Dynamic.centralizer chi').IsRepresentedBy
      ((GroupScheme.baseChange b).map w.inclusion ≫ i') := by
    have h := Dynamic.isRepresentedBy_centralizer_baseChange b
      (d.cocharacter ≫ t ≫ i) (w.representsCentralizer d hDynamic hG)
    have heq : Dynamic.baseChangeCocharacter b (d.cocharacter ≫ t ≫ i) = chi' := by
      change Dynamic.baseChangeCocharacter b (d.cocharacter ≫ t ≫ i) =
        Dynamic.baseChangeCocharacter b d.cocharacter ≫
          (GroupScheme.baseChange b).map t ≫ (GroupScheme.baseChange b).map i
      simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]
    rw [heq, Functor.map_comp] at h
    exact h
  exact (hDynamic S' G' P' U' ((GroupScheme.baseChange b).obj w.group) chi'
    i' iU' ((GroupScheme.baseChange b).map w.inclusion ≫ i')
    hG' d'.represents hU' hZ').2.2 _ rfl

/-- Pull back a chosen witness, retaining the actual base-changed group and
inclusion, under the two explicit structure inputs. -/
def baseChange (w : TorusLeviWitness t) (d : TorusDynamicPresentation i t)
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G)
    (b : S' ⟶ S) :
    TorusLeviWitness (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t) := by
  have hl := w.isLevi_baseChange d hDynamic hG b
  have ht : SubgroupFunctor.range ((GroupScheme.baseChange b).map t) ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map w.inclusion) := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    intro V x hx
    exact w.contains _ hx
  let v := (d.baseChange b).witness hDynamic hRadical (hG.baseChange b)
  refine ⟨(GroupScheme.baseChange b).obj w.group, (GroupScheme.baseChange b).map w.inclusion,
    hl, ht, ?_⟩
  intro L' l' hl' ht'
  exact (v.unique L' l' hl' ht').trans
    (v.unique _ ((GroupScheme.baseChange b).map w.inclusion) hl ht).symm

@[simp] theorem baseChange_group (w : TorusLeviWitness t)
    (d : TorusDynamicPresentation i t)
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G)
    (b : S' ⟶ S) :
    (w.baseChange d hDynamic hRadical hG b).group =
      (GroupScheme.baseChange b).obj w.group := rfl

@[simp] theorem baseChange_inclusion (w : TorusLeviWitness t)
    (d : TorusDynamicPresentation i t)
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G)
    (b : S' ⟶ S) :
    (w.baseChange d hDynamic hRadical hG b).inclusion =
      (GroupScheme.baseChange b).map w.inclusion := rfl

end TorusLeviWitness

end Langlands.GroupScheme.RelativeLevi
