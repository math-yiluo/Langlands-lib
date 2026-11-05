import Langlands.GroupScheme.Reductive.UnipotentRadicalAction
import Langlands.GroupScheme.Rational.SplitSeriesBaseChange
import Langlands.GroupScheme.Rational.AffineLineRigidity
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Smooth actions on split kernels with wound scalar-extension quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.AutomorphicAction

section Descent

variable {B B' : Scheme.{u}} {H G V : GroupScheme B}
    (a : AutomorphicAction H G) (b : B' ⟶ B)

/-- Stability of a represented subgroup descends through fpqc base change. -/
theorem isStable_range_of_baseChange
    [QuasiCompact b] [Flat b] [Surjective b]
    (i : V ⟶ G) [Mono i.hom.hom]
    (h : (a.baseChange b).IsStable
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map i))) :
    a.IsStable (SubgroupFunctor.range i) := by
  intro T s x hx
  let W : Over B' := (Over.pullback b).obj T
  let p : (Over.map b).obj W ⟶ T :=
    Over.homMk (pullback.fst T.hom b) pullback.condition
  have : EffectiveEpi p.left := by
    change EffectiveEpi (pullback.fst T.hom b)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range i p
  let s' := (baseChangePointsEquiv b H W).symm (p ≫ s)
  let x' := (baseChangePointsEquiv b G W).symm (p ≫ x)
  have hx' : x' ∈
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).carrier W := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange]
    change baseChangePointsEquiv b G W
      ((baseChangePointsEquiv b G W).symm (p ≫ x)) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact (SubgroupFunctor.range i).comp_mem p hx
  have hm := h W s' x' hx'
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
    baseChangePointsEquiv_act] at hm
  simpa only [s', x', MulEquiv.apply_symm_apply, a.naturality] using hm

end Descent

section Field

variable {k : Type u} [Field k]
    {H G V Q : GroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction H G)

/-- A split full kernel is action-stable when the quotient is wound and the
smooth universal action source has dense actual rational points. -/
theorem isStable_splitKernel_of_denseRationalPoints
    [Smooth H.X.hom] [Smooth V.X.hom] [IsAffineHom V.X.hom]
    [IsSeparated Q.X.hom]
    (i : V ⟶ G) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hV : RelativeRoot.IsSplitUnipotent V)
    (hQ : HasConstantAffineLineMaps Q)
    (hD : HasDenseRationalPoints k (H.X ⊗ V.X)) :
    a.IsStable (SubgroupFunctor.range i) := by
  have : Smooth (H.X ⊗ V.X).hom := smooth_tensor H.X V.X inferInstance inferInstance
  have : IsReduced (H.X ⊗ V.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (H.X ⊗ V.X).hom
  let F : H.X ⊗ V.X ⟶ G.X :=
    a.act (fst H.X V.X) (snd H.X V.X ≫ i.hom.hom)
  have hkill : F ≫ q.hom.hom = (1 : H.X ⊗ V.X ⟶ Q.X) := by
    apply hom_ext_of_denseRationalPoints hD
    intro z
    let s := z ≫ fst H.X V.X
    let x := z ≫ snd H.X V.X
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    have hz := hQ.hom_eq_zero_of_isSplitUnipotent hV
      (i ≫ (a.sectionIso s).hom ≫ q)
    have hk : a.act s (x ≫ i.hom.hom) ≫ q.hom.hom = 1 := by
      have he := congrArg (fun f => x ≫ f.hom.hom) hz
      change x ≫ (i ≫ (a.sectionIso s).hom ≫ q).hom.hom =
        x ≫ (1 : V.X ⟶ Q.X) at he
      simpa only [Grp.comp_hom_hom, ← Category.assoc,
        a.comp_sectionIso_hom, a.naturality, comp_toUnit, hu,
        Category.id_comp, MonObj.comp_one] using he
    rw [← Category.assoc]
    change (z ≫ a.act (fst H.X V.X) (snd H.X V.X ≫ i.hom.hom)) ≫
      q.hom.hom = z ≫ 1
    rw [a.naturality, MonObj.comp_one]
    exact hk
  intro T s x hx
  obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hker]
  apply (mem_range_kernelι_iff q _).mpr
  have he := congrArg (fun f => lift s v ≫ f) hkill
  simpa only [F, ← Category.assoc, a.naturality, lift_fst, lift_snd,
    MonObj.comp_one] using he

variable (K : Type u) [Field K] [Algebra k K]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation "H_K" => Functor.obj (GroupScheme.baseChange b) H
local notation "V_K" => Functor.obj (GroupScheme.baseChange b) V

/-- Woundness and density after a field extension give stability on every
test scheme over the original field. -/
theorem isStable_splitKernel_of_woundBaseChange
    [Smooth H.X.hom] [Smooth V.X.hom] [IsAffineHom V.X.hom]
    [IsSeparated Q.X.hom]
    (i : V ⟶ G) [Mono i.hom.hom] (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hV : RelativeRoot.IsSplitUnipotent V)
    (hQ : HasConstantAffineLineMaps ((GroupScheme.baseChange b).obj Q))
    (hD : HasDenseRationalPoints K ((H_K).X ⊗ (V_K).X)) :
    a.IsStable (SubgroupFunctor.range i) := by
  obtain ⟨hb₁, hb₂, hb₃⟩ := fieldExtension_fpqc k K
  let : Surjective b := hb₁
  let : Flat b := hb₂
  let : QuasiCompact b := hb₃
  let : Smooth (H_K).X.hom := by
    change Smooth (pullback.snd H.X.hom b)
    infer_instance
  let : Smooth (V_K).X.hom := by
    change Smooth (pullback.snd V.X.hom b)
    infer_instance
  let : IsAffineHom (V_K).X.hom := by
    change IsAffineHom (pullback.snd V.X.hom b)
    infer_instance
  let : IsSeparated ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsSeparated (pullback.snd Q.X.hom b)
    infer_instance
  apply a.isStable_range_of_baseChange b i
  apply (a.baseChange b).isStable_splitKernel_of_denseRationalPoints
    ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map q)
  · simpa only [SubgroupFunctor.range_baseChangeHom] using (hq.baseChange b).2.2.2
  · exact hV.baseChange K
  · exact hQ
  · exact hD

/-- The actual action induced on a supplied split closed kernel whose quotient
becomes wound over a field with the stated rational density. -/
def onSplitKernelOfWoundBaseChange
    [Smooth H.X.hom] [Smooth V.X.hom] [IsAffineHom V.X.hom]
    [IsSeparated Q.X.hom]
    (i : V ⟶ G) (hi : IsClosedSubgroup i) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hV : RelativeRoot.IsSplitUnipotent V)
    (hQ : HasConstantAffineLineMaps ((GroupScheme.baseChange b).obj Q))
    (hD : HasDenseRationalPoints K ((H_K).X ⊗ (V_K).X)) :
    AutomorphicAction H V := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact a.onRepresentedSubgroup i ⟨inferInstance, rfl⟩
    (a.isStable_splitKernel_of_woundBaseChange K i q hq hV hQ hD)

/-- The induced action commutes with the original inclusion on every test. -/
theorem onSplitKernelOfWoundBaseChange_act_comp
    [Smooth H.X.hom] [Smooth V.X.hom] [IsAffineHom V.X.hom]
    [IsSeparated Q.X.hom]
    (i : V ⟶ G) (hi : IsClosedSubgroup i) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hV : RelativeRoot.IsSplitUnipotent V)
    (hQ : HasConstantAffineLineMaps ((GroupScheme.baseChange b).obj Q))
    (hD : HasDenseRationalPoints K ((H_K).X ⊗ (V_K).X))
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ H.X) (v : T ⟶ V.X) :
    (a.onSplitKernelOfWoundBaseChange K i hi q hq hV hQ hD).act s v ≫ i.hom.hom =
      a.act s (v ≫ i.hom.hom) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact a.onRepresentedSubgroup_act_comp i _ _ s v

end Field

end Langlands.GroupScheme.AutomorphicAction
