import Langlands.GroupScheme.Reductive.NonAffineNormalUnipotentRadicalInclusion
import Langlands.GroupScheme.SmoothFieldComponentFunctorial
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties

/-! # Represented radicals and the identity component of a smooth field group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G U V : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom]

/-- A represented radical of the identity component is a radical in the whole
smooth group, with no affine or quasi-compact ambient premise. -/
theorem IsUnipotentRadical.comp_smoothComponentInclusion
    {i : U ⟶ SmoothFieldComponent.group G} (hi : IsUnipotentRadical i) :
    IsUnipotentRadical (i ≫ SmoothFieldComponent.inclusion G) := by
  let c := SmoothFieldComponent.inclusion G
  have hc : IsClosedSubgroup c :=
    inferInstanceAs (IsClosedImmersion (SmoothFieldComponent.inclusion G).hom.hom.left)
  let : Mono c.hom.hom := Over.mono_of_mono_left _
  refine ⟨hi.isClosedSubgroup.comp hc, hi.smooth, hi.connectedSpace,
    hi.isUnipotent, hi.isNormal_comp_of_smooth c hc
      (SmoothFieldComponent.isNormal_range_inclusion G), ?_⟩
  intro H j hj hs hconn hu hn
  let : ConnectedSpace H.X.left := hconn
  let f := SmoothFieldComponent.factor G j
  have hf : IsClosedSubgroup f := IsClosedSubgroup.of_comp hc (by
    rw [SmoothFieldComponent.factor_inclusion]
    exact hj)
  have hfn : (SubgroupFunctor.range f).IsNormal := by
    intro T g x _ hx
    have hx' : x ≫ c.hom.hom ∈ (SubgroupFunctor.range j).carrier T := by
      obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      refine SubgroupFunctor.mem_range.mpr ⟨v, ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, SmoothFieldComponent.factor_inclusion]
    have hconj := hn T (g ≫ c.hom.hom) (x ≫ c.hom.hom) (Subgroup.mem_top _) hx'
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hconj
    refine SubgroupFunctor.mem_range.mpr ⟨v, ?_⟩
    apply (cancel_mono c.hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, SmoothFieldComponent.factor_inclusion]
    simpa only [MonObj.mul_comp, GrpObj.inv_comp] using hv
  have hle := SubgroupFunctor.range_comp_mono
    (hi.greatest H f hf hs hconn hu hfn) c
  simpa only [f, c, SmoothFieldComponent.factor_inclusion] using hle

/-- Actual comparison of a supplied ambient radical with a supplied radical
of its smooth identity component. -/
def IsUnipotentRadical.smoothComponentSourceIso
    {i : U ⟶ G} (hi : IsUnipotentRadical i)
    {j : V ⟶ SmoothFieldComponent.group G} (hj : IsUnipotentRadical j) : U ≅ V :=
  hi.isClosedSubgroup.sourceIsoOfRangeEq
    (hj.comp_smoothComponentInclusion).isClosedSubgroup
    (hi.range_eq hj.comp_smoothComponentInclusion)

/-- The comparison commutes with the actual inclusions into the full group. -/
@[reassoc]
theorem IsUnipotentRadical.smoothComponentSourceIso_hom_comp
    {i : U ⟶ G} (hi : IsUnipotentRadical i)
    {j : V ⟶ SmoothFieldComponent.group G} (hj : IsUnipotentRadical j) :
    (hi.smoothComponentSourceIso hj).hom ≫ j ≫ SmoothFieldComponent.inclusion G = i :=
  hi.isClosedSubgroup.sourceIsoOfRangeEq_hom_comp
    (hj.comp_smoothComponentInclusion).isClosedSubgroup
    (hi.range_eq hj.comp_smoothComponentInclusion)

/-- Preservation of a supplied identity-component radical implies preservation
of every supplied radical of the whole smooth ambient group. -/
theorem IsUnipotentRadical.baseChange_of_smooth_component
    {K : Type u} [Field K] [Algebra k K] [IsAlgClosed K]
    {i : U ⟶ G} (hi : IsUnipotentRadical i)
    {j : V ⟶ SmoothFieldComponent.group G} (hj : IsUnipotentRadical j)
    (hjK : IsUnipotentRadical
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j)) :
    IsUnipotentRadical
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let e := SmoothFieldComponent.baseChangeIso G (algebraMap k K)
  have hcomp := (hjK.comp_iso e).comp_smoothComponentInclusion
  have hjcompK : IsUnipotentRadical (B.map (j ≫ SmoothFieldComponent.inclusion G)) := by
    simpa only [e, Category.assoc, SmoothFieldComponent.baseChangeIso_hom_inclusion,
      ← Functor.map_comp] using hcomp
  have he : B.map i = (B.mapIso (hi.smoothComponentSourceIso hj)).hom ≫
      B.map (j ≫ SmoothFieldComponent.inclusion G) := by
    change B.map i = B.map (hi.smoothComponentSourceIso hj).hom ≫
      B.map (j ≫ SmoothFieldComponent.inclusion G)
    rw [← B.map_comp, hi.smoothComponentSourceIso_hom_comp hj]
  rw [he]
  exact hjcompK.precomp_iso (B.mapIso (hi.smoothComponentSourceIso hj))

end Langlands.GroupScheme
