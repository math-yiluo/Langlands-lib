import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Torus.CentralizerSmoothProof
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Reduction of Milne 17.84 to the algebraically closed case and Milne 17.82 -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Maximal tori over an algebraically closed field are self-centralizing** (Milne,
Proposition 17.61(a), in the case of an algebraically closed base field, to which its proof
reduces). Let `G` be a connected reductive group over an algebraically closed field `k` and
`j : T ⟶ G` a maximal torus. Then the centralizer of `T` in `G` is `T`, as subgroup functors
on every test scheme over `Spec k`. -/
def AlgClosedMaximalTorusCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j → torusCentralizer j = SubgroupFunctor.range j

section Descent

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

/-- A closed subgroup `j : T ⟶ G` of a field-valued group scheme, with `T` commutative and
affine, is its own all-test centralizer once its base change to a field extension `K` is. -/
theorem torusCentralizer_eq_range_of_baseChange
    {G : GroupScheme (Spec (CommRingCat.of k))} {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsAffineHom T.X.hom) (j : T.toGrp ⟶ G) (hj : IsClosedSubgroup j)
    (h : torusCentralizer
        (T := (CommGroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j)) :
    torusCentralizer j = SubgroupFunctor.range j := by
  set b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨C, c, hc, -⟩ := fieldCentralizerRepresentability k T G hT j
  set t := torusCentralizerFactor j hc
  have ht : t ≫ c = j := torusCentralizerFactor_comp j hc
  -- After base change, `c_K` represents the centralizer of `j_K`, which is the range of `j_K`.
  have hcK := hc.baseChange b
  rw [← torusCentralizer_baseChange, h] at hcK
  have : IsClosedImmersion ((GroupScheme.baseChange b).map j).hom.hom.left := hj.baseChange b
  have : Mono ((GroupScheme.baseChange b).map j).hom.hom := Over.mono_of_mono_left _
  have hjK : (SubgroupFunctor.range ((GroupScheme.baseChange b).map j)).IsRepresentedBy
      ((GroupScheme.baseChange b).map j) := ⟨inferInstance, rfl⟩
  -- So `t_K` is the comparison isomorphism between the two representatives.
  have htK : (GroupScheme.baseChange b).map t = (hjK.isoOfIsRepresentedBy hcK).hom := by
    apply hcK.hom_ext
    rw [hjK.isoOfIsRepresentedBy_hom_comp hcK, ← Functor.map_comp, ht]
  have : IsIso ((GroupScheme.baseChange b).map t) := by
    rw [htK]
    infer_instance
  -- Field extensions are faithfully flat, so `t` itself is an isomorphism.
  obtain ⟨hflat, hsurj⟩ : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff _).2 (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)
  have : IsIso t := isIso_of_baseChange b t
  rw [← hc.2, ← ht]
  exact (SubgroupFunctor.range_iso_comp (asIso t) c).symm

end Descent

/-- Milne's proof of Corollary 17.84: the forward implication of Theorem 17.82 and the
algebraically closed case of Proposition 17.61(a) imply that every maximal torus of a connected
reductive group over a field is its own centralizer. -/
def MaximalTorusCentralizerReductionStatement : Prop :=
  MaximalTorusBaseChangeForwardStatement.{u} → AlgClosedMaximalTorusCentralizerStatement.{u} →
    MaximalTorusCentralizerStatement.{u}

/-- Pass to the algebraic closure `k̄`: `T_k̄` is maximal in the connected reductive `G_k̄`, so
it is self-centralizing there, and this descends to `k`. -/
theorem maximalTorusCentralizerReduction : MaximalTorusCentralizerReductionStatement.{u} := by
  intro hfwd hac k _ G hG T j hj
  have := hG.smooth
  have := hG.isAffineHom
  apply torusCentralizer_eq_range_of_baseChange (AlgebraicClosure k)
    (hj.2.1.isAffineHom : IsAffineHom T.toGrp.X.hom) j hj.2.1
  exact hac (AlgebraicClosure k) _ hG.baseChange_toAlgebraicClosure _ _
    (hfwd k (AlgebraicClosure k) G T j hj)

/-- With the proved smoothness of torus centralizers, the central case of Milne 17.82 and the
algebraically closed case of Milne 17.61(a) imply Milne 17.84. -/
theorem maximalTorusCentralizer_of_centralMaximalTorusBaseChange
    (hcentral : CentralMaximalTorusBaseChangeStatement.{u})
    (hac : AlgClosedMaximalTorusCentralizerStatement.{u}) :
    MaximalTorusCentralizerStatement.{u} :=
  maximalTorusCentralizerReduction
    (maximalTorusBaseChangeForwardReduction torusCentralizerSmooth hcentral) hac

end Langlands.GroupScheme
