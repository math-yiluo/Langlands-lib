import Langlands.GroupScheme.NormalSubgroupQuotientStatement
import Langlands.GroupScheme.Torus.CentralMaximalQuotientStatement
import Langlands.GroupScheme.Torus.NoTorusBaseChangeStatement
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeStatement
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Reduction of the central case of Milne 17.82 to quotients and absence of tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The range of a central homomorphism is a normal subgroup functor. -/
theorem IsCentral.range_isNormal {S : Scheme.{u}} {H G : GroupScheme S} {i : H ⟶ G}
    (hi : IsCentral i) : (SubgroupFunctor.range i).IsNormal := by
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← (commute_of_mem_center (hi T y) g).eq, mul_inv_cancel_right]
  exact hx

/-- Existence of quotients by normal closed subgroups, absence of tori in the quotient by a
central maximal torus, and invariance of the absence of tori under field extension imply the
central case of the forward implication of Milne, Theorem 17.82, at every universe. -/
def CentralMaximalTorusBaseChangeReductionStatement : Prop :=
  NormalSubgroupQuotientStatement.{u} → CentralMaximalTorusQuotientStatement.{u} →
    NoTorusBaseChangeStatement.{u} → CentralMaximalTorusBaseChangeStatement.{u}

/-- Reduce the central case to the quotient `H/Z`, following Milne's proof of Theorem 17.82.
All three structural statements remain explicit hypotheses. -/
theorem centralMaximalTorusBaseChangeReduction :
    CentralMaximalTorusBaseChangeReductionStatement.{u} := by
  intro hquot hnoQ hbase k K _ _ _ H _ _ Z j hj hm
  obtain ⟨Q, q, hQs, hQa, hq⟩ := hquot k H Z.toGrp j hm.2.1 hj.range_isNormal
  have : Smooth Q.X.hom := hQs
  have : IsAffineHom Q.X.hom := hQa
  have hnoK := hbase k K Q (hnoQ k H Z j hj hm Q q hq)
  set b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hjK := hm.2.1.baseChange b
  refine ⟨hm.1.baseChange, hjK, ?_⟩
  intro T' i' f hT' hi' hf
  have hle : SubgroupFunctor.range i' ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map j) := by
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : (y ≫ i'.hom.hom) ≫ ((GroupScheme.baseChange b).map q).hom.hom = 1 := by
      have h : y ≫ (i' ≫ (GroupScheme.baseChange b).map q).hom.hom ∈
          (SubgroupFunctor.range (i' ≫ (GroupScheme.baseChange b).map q)).carrier U :=
        SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
      rw [hnoK T' hT' _, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h
      simpa only [Grp.comp_hom_hom, Category.assoc] using h
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange, ← hq.2.2.2,
      mem_range_kernelι_iff]
    exact (baseChangePointsEquiv_comp b q U _).symm.trans
      ((congrArg (baseChangePointsEquiv b Q U) hy).trans (map_one _))
  let : IsClosedImmersion ((GroupScheme.baseChange b).map j).hom.hom.left := hjK
  let : Mono ((GroupScheme.baseChange b).map j).hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion i'.hom.hom.left := hi'
  let : Mono i'.hom.hom := Over.mono_of_mono_left _
  have hr : (SubgroupFunctor.range ((GroupScheme.baseChange b).map j)).IsRepresentedBy
      ((GroupScheme.baseChange b).map j) := ⟨inferInstance, rfl⟩
  have hr' : (SubgroupFunctor.range i').IsRepresentedBy i' := ⟨inferInstance, rfl⟩
  -- The factorization `g` of `i'` through `Z_K` is inverse to `f`.
  let g : T'.toGrp ⟶ ((CommGroupScheme.baseChange b).obj Z).toGrp := hr.factorHom i' hle
  have hg : g ≫ (GroupScheme.baseChange b).map j = i' := hr.factorHom_comp i' hle
  refine ⟨⟨g, hr.hom_ext ?_, hr'.hom_ext ?_⟩⟩
  · exact (Category.assoc f g _).trans
      ((congrArg (f ≫ ·) hg).trans (hf.trans (Category.id_comp _).symm))
  · exact (Category.assoc g f i').trans
      ((congrArg (g ≫ ·) hf).trans (hg.trans (Category.id_comp _).symm))

end Langlands.GroupScheme
