import Langlands.GroupScheme.RelativeLevi.TorusLeviLocal
import Langlands.GroupScheme.RelativeLevi.LeviCoverDescent
import Langlands.GroupScheme.RelativeLevi.BaseChange

/-! # Containment and uniqueness for descended torus-Levi witnesses -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SubgroupFunctor.CoverDescent

/-- A closed subgroup is recovered by imposing its pulled-back range on every
relative test over an étale covering family. -/
theorem subgroup_range_baseChange {S : Scheme.{u}} {H G : GroupScheme S}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (f : H ⟶ G) (hf : IsClosedSubgroup f) :
    subgroup 𝒰 (fun i => range ((GroupScheme.baseChange (𝒰.f i)).map f)) =
      range f := by
  apply le_antisymm
  · intro T x hx
    have hrep : (range f).IsRepresentedBy f := ⟨hf.mono_overHom, rfl⟩
    let : IsClosedImmersion f.hom.hom.left := hf
    apply ((range f).schemeCondition_iff_mem x).mp
    apply ((range f).schemeCondition_iff_exists_of_isRepresentedBy hrep x.left).mpr
    let 𝒰' : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
      𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
        (fun i => ⟨inferInstance, inferInstance⟩)
    apply Langlands.AlgebraicGeometry.FppfClosedLocusDescent.exists_lift_of_covering
      Scheme.fppfTopology f.hom.hom.left x.left
      ((Sieve.generate 𝒰'.presieve₀).pullback T.hom)
      (Scheme.fppfTopology.pullback_stable T.hom
        (Precoverage.generate_mem_toGrothendieck 𝒰'.mem₀))
    intro Y u hu
    obtain ⟨i, a, ha⟩ :=
      Langlands.AlgebraicGeometry.FppfClosedLocusDescent.exists_of_pullback_generate_ofArrows
        T.hom u hu
    let W : Over (𝒰.X i) := Over.mk a
    let b : (Over.map (𝒰.f i)).obj W ⟶ T := Over.homMk u ha.symm
    have hm := hx i W b
    change (baseChangePointsEquiv (𝒰.f i) G W).symm (b ≫ x) ∈
      (range ((GroupScheme.baseChange (𝒰.f i)).map f)).carrier W at hm
    rw [range_baseChangeHom] at hm
    change baseChangePointsEquiv (𝒰.f i) G W
      ((baseChangePointsEquiv (𝒰.f i) G W).symm (b ≫ x)) ∈
        (range f).carrier ((Over.map (𝒰.f i)).obj W) at hm
    have hm' : b ≫ x ∈ (range f).carrier ((Over.map (𝒰.f i)).obj W) := by
      simpa only [MulEquiv.apply_symm_apply] using hm
    obtain ⟨k, hk⟩ := mem_range.mp hm'
    exact ⟨k.left, congrArg (fun q => q.left) hk⟩
  · intro T x hx i V a
    change (baseChangePointsEquiv (𝒰.f i) G V).symm (a ≫ x) ∈
      (range ((GroupScheme.baseChange (𝒰.f i)).map f)).carrier V
    rw [range_baseChangeHom]
    change baseChangePointsEquiv (𝒰.f i) G V
      ((baseChangePointsEquiv (𝒰.f i) G V).symm (a ≫ x)) ∈
        (range f).carrier ((Over.map (𝒰.f i)).obj V)
    simpa only [MulEquiv.apply_symm_apply] using (range f).comp_mem a hx

end SubgroupFunctor.CoverDescent

namespace RelativeLevi.EtaleTorusLeviData

variable {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- The descended all-test condition contains the prescribed commutative group. -/
theorem contains_subgroup (D : EtaleTorusLeviData i t) :
    SubgroupFunctor.range t ≤ SubgroupFunctor.CoverDescent.subgroup D.cover
      (fun a => SubgroupFunctor.range (D.witness a).inclusion) := by
  intro V x hx a W b
  apply (D.witness a).contains W
  rw [SubgroupFunctor.range_baseChangeHom]
  change baseChangePointsEquiv (D.cover.f a) P W
    ((baseChangePointsEquiv (D.cover.f a) P W).symm (b ≫ x)) ∈
      (SubgroupFunctor.range t).carrier ((Over.map (D.cover.f a)).obj W)
  simpa only [MulEquiv.apply_symm_apply] using (SubgroupFunctor.range t).comp_mem b hx

/-- Any global Levi containing the prescribed group has exactly the descended
local ranges. -/
theorem unique_subgroup (D : EtaleTorusLeviData i t) [IsAffineHom P.X.hom]
    (L' : GroupScheme S) (l' : L' ⟶ P) (hl' : IsRelativeLeviSubgroup l')
    (ht' : SubgroupFunctor.range t ≤ SubgroupFunctor.range l') :
    SubgroupFunctor.range l' = SubgroupFunctor.CoverDescent.subgroup D.cover
      (fun a => SubgroupFunctor.range (D.witness a).inclusion) := by
  have heq : ∀ a, SubgroupFunctor.range ((GroupScheme.baseChange (D.cover.f a)).map l') =
      SubgroupFunctor.range (D.witness a).inclusion := by
    intro a
    apply (D.witness a).unique _ _ (hl'.baseChange_etale (D.cover.f a))
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    intro V x hx
    exact ht' _ hx
  rw [← SubgroupFunctor.CoverDescent.subgroup_range_baseChange D.cover l'
    hl'.isClosedSubgroup]
  exact congrArg (SubgroupFunctor.CoverDescent.subgroup D.cover) (funext heq)

/-- Equip an actual descended Levi representative with torus containment and
global uniqueness. -/
def witnessOfLeviRepresentative (D : EtaleTorusLeviData i t)
    [IsAffineHom P.X.hom]
    (R : LeviRepresentative (SubgroupFunctor.CoverDescent.subgroup D.cover
      (fun a => SubgroupFunctor.range (D.witness a).inclusion))) :
    TorusLeviWitness t where
  group := R.group
  inclusion := R.hom
  isLevi := R.isLevi
  contains := by
    rw [R.represents.2]
    exact D.contains_subgroup
  unique := by
    intro L' l' hl' ht'
    exact (D.unique_subgroup L' l' hl' ht').trans R.represents.2.symm

end RelativeLevi.EtaleTorusLeviData

end Langlands.GroupScheme
