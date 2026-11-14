import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Restricting a universal torus family to an open maximal locus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Fibrewise maximality depends only on the actual represented subgroup. -/
theorem IsFibrewiseMaximalTorus.of_range_eq {S : Scheme.{u}}
    {T T' : CommGroupScheme S} {G : GroupScheme S}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i')
    (hm : IsFibrewiseMaximalTorus i) : IsFibrewiseMaximalTorus i' := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion i'.hom.hom.left := hi'
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono i'.hom.hom := Over.mono_of_mono_left _
  let hr : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hr' : (SubgroupFunctor.range i).IsRepresentedBy i' := ⟨inferInstance, h.symm⟩
  let e := hr.isoOfIsRepresentedBy hr'
  have he : e.inv ≫ i = i' := by
    rw [← hr.isoOfIsRepresentedBy_hom_comp hr', Iso.inv_hom_id_assoc]
  intro s
  have hs := IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
    (T' := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T')
    ((baseChange (S.fromSpecResidueField s)).mapIso e.symm) (hm s)
  change IsMaximalTorus
    (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T')
    ((baseChange (S.fromSpecResidueField s)).map e.inv ≫
      (baseChange (S.fromSpecResidueField s)).map i) at hs
  rw [← Functor.map_comp, he] at hs
  exact hs

namespace TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M : Over S}
  {K : CommGroupScheme M.left}

/-- Universality among actual closed fibrewise maximal relative tori. -/
def IsUniversalMaximal (j : K.toGrp ⟶ (baseChange M.hom).obj G) : Prop :=
  ∀ (T : Over S) (T' : CommGroupScheme T.left)
      (t : T'.toGrp ⟶ (baseChange T.hom).obj G),
    RelativeTorus.IsTorus T'.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
      ∃! a : T ⟶ M, evaluate j a = SubgroupFunctor.range t

/-- An open subscheme of the parameter scheme, with its original base map. -/
def openModuli (M : Over S) (U : M.left.Opens) : Over S :=
  Over.mk (U.ι ≫ M.hom)

/-- The inclusion of an open parameter subscheme over the original base. -/
def openInclusion (U : M.left.Opens) : openModuli M U ⟶ M :=
  Over.homMk U.ι rfl

/-- The actual subgroup family restricted to an open parameter subscheme. -/
def openFamily (j : K.toGrp ⟶ (baseChange M.hom).obj G) (U : M.left.Opens) :
    ((CommGroupScheme.baseChange U.ι).obj K).toGrp ⟶
      (baseChange (openModuli M U).hom).obj G :=
  familyHom j (openInclusion U)

/-- Restriction preserves the closed relative-torus conditions. -/
theorem openFamily_isClosed_isTorus
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (U : M.left.Opens)
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K.toGrp) :
    IsClosedSubgroup (openFamily j U) ∧
      RelativeTorus.IsTorus ((CommGroupScheme.baseChange U.ι).obj K).toGrp :=
  ⟨isClosedSubgroup_familyHom j hj (openInclusion U), hK.baseChange U.ι⟩

/-- An open part of smooth parameter space is smooth over the base. -/
theorem smooth_openModuli (U : M.left.Opens) [Smooth M.hom] :
    Smooth (openModuli M U).hom := by
  change Smooth (U.ι ≫ M.hom)
  infer_instance

/-- Restricting a universal torus family to an open subscheme which detects
fibrewise maximality gives a universal maximal-torus family. -/
theorem isUniversalMaximal_openFamily
    (j : K.toGrp ⟶ (baseChange M.hom).obj G)
    (hj : IsClosedSubgroup j) (huni : IsUniversal j) (U : M.left.Opens)
    (hU : ∀ (T : Over S) (a : T ⟶ M),
      IsFibrewiseMaximalTorus
        (T := (CommGroupScheme.baseChange a.left).obj K) (familyHom j a) ↔
          Set.range a.left ⊆ (U : Set M.left)) :
    IsFibrewiseMaximalTorus (openFamily j U) ∧
      IsUniversalMaximal (G := G) (M := openModuli M U)
        (K := (CommGroupScheme.baseChange U.ι).obj K) (openFamily j U) := by
  constructor
  · apply (hU (openModuli M U) (openInclusion U)).mpr
    change Set.range U.ι ⊆ (U : Set M.left)
    rw [Scheme.Opens.range_ι]
  · intro T T' t hT' ht hmax
    obtain ⟨a, ha, hua⟩ := huni T (SubgroupFunctor.range t)
      (isAdmissible_range t ht hT')
    have hma : IsFibrewiseMaximalTorus
        (T := (CommGroupScheme.baseChange a.left).obj K) (familyHom j a) :=
      hmax.of_range_eq ht (isClosedSubgroup_familyHom j hj a) ha.symm
    have hr : Set.range a.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      exact (hU T a).mp hma
    let l := IsOpenImmersion.lift U.ι a.left hr
    have hl : l ≫ U.ι = a.left := IsOpenImmersion.lift_fac _ _ _
    let b : T ⟶ openModuli M U := Over.homMk l (by
      change l ≫ (U.ι ≫ M.hom) = T.hom
      rw [← Category.assoc, hl, Over.w a])
    have hb : b ≫ openInclusion U = a := Over.OverMorphism.ext hl
    refine ⟨b, ?_, ?_⟩
    · change evaluate (familyHom j (openInclusion U)) b = _
      rw [evaluate_comp, hb]
      exact ha
    · intro c hc
      have hc' : evaluate j (c ≫ openInclusion U) = SubgroupFunctor.range t := by
        rw [← evaluate_comp]
        exact hc
      have hca : c ≫ openInclusion U = a := hua _ hc'
      apply Over.OverMorphism.ext
      apply (cancel_mono U.ι).mp
      exact congrArg CommaMorphism.left (hca.trans hb.symm)

end TorusSubgroupModuli
end Langlands.GroupScheme
