import Langlands.GroupScheme.Torus.SeparatedNormalizerStatement
import Langlands.GroupScheme.HomScheme.NormalizerConjugation
import Langlands.GroupScheme.Torus.CentralizerOpenInNormalizer
import Langlands.GroupScheme.Torus.CentralizerQuotient
import Langlands.GroupScheme.HomogeneousQuotientGroup

/-! # Weyl quotients of self-centralizing tori in separated smooth groups -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace SeparatedTorusWeylQuotient
open HomScheme HomogeneousQuotientFromEmbedding

variable {S : Scheme.{u}} {A : CommGroupScheme S} {G N Z : GroupScheme S}

private theorem evaluate_compHom {B C D : GroupScheme S} {T T' : Over S}
    (a : T' ⟶ T) (f : RelativeHom B C T) (g : RelativeHom C D T) :
    evaluate a (f ≫ g) = evaluate a f ≫ evaluate a g :=
  Descent.pullHom_comp a.left (Over.w a) (Over.w a) (Over.w a) f g

/-- The tautological point of a representing normalizer lies in the normalizer. -/
theorem mem_torusNormalizer_self (t : A.toGrp ⟶ G) (n : N ⟶ G)
    (hn : (torusNormalizer t).IsRepresentedBy n) :
    n.hom.hom ∈ (torusNormalizer t).carrier N.X := by
  have h : 𝟙 N.X ≫ n.hom.hom ∈ (torusNormalizer t).carrier N.X := by
    rw [← hn.2]
    exact ⟨𝟙 _, rfl⟩
  simpa only [Category.id_comp] using h

/-- The source-automorphism family of the torus over its represented normalizer. -/
def normalizerFamily (t : A.toGrp ⟶ G) [Mono t.hom.hom.left] (n : N ⟶ G)
    (hn : (torusNormalizer t).IsRepresentedBy n) :
    RelativeHom A.toGrp A.toGrp N.X :=
  (normalizerSourceIso t n.hom.hom (mem_torusNormalizer_self t n hn)).1.hom

/-- Composing the normalizer family with the torus gives conjugation. -/
theorem normalizerFamily_comp (t : A.toGrp ⟶ G) [Mono t.hom.hom.left] (n : N ⟶ G)
    (hn : (torusNormalizer t).IsRepresentedBy n) :
    normalizerFamily t n hn ≫ (GroupScheme.baseChange N.X.hom).map t =
      conjugationFamily t n.hom.hom :=
  (normalizerSourceIso t n.hom.hom (mem_torusNormalizer_self t n hn)).2.symm

/-- Restrictions of the normalizer family compose with the torus to conjugation. -/
theorem evaluate_normalizerFamily_comp (t : A.toGrp ⟶ G) [Mono t.hom.hom.left]
    (n : N ⟶ G) (hn : (torusNormalizer t).IsRepresentedBy n) {U : Over S}
    (a : U ⟶ N.X) :
    evaluate a (normalizerFamily t n hn) ≫ (GroupScheme.baseChange U.hom).map t =
      conjugationFamily t (a ≫ n.hom.hom) := by
  rw [← evaluate_baseChange a t, ← evaluate_compHom, normalizerFamily_comp,
    evaluate_conjugationFamily]

/-- Base change of a monomorphic homomorphism can be cancelled on the right. -/
theorem cancel_baseChange_map {B : GroupScheme S} (t : A.toGrp ⟶ G)
    [Mono t.hom.hom.left] {U : Over S}
    {e f : (GroupScheme.baseChange U.hom).obj B ⟶
      (GroupScheme.baseChange U.hom).obj A.toGrp}
    (h : e ≫ (GroupScheme.baseChange U.hom).map t =
      f ≫ (GroupScheme.baseChange U.hom).map t) : e = f := by
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let : Mono ((GroupScheme.baseChange U.hom).map t).hom.hom := by
    change Mono ((Over.pullback U.hom).map t.hom.hom)
    infer_instance
  apply Grp.hom_ext
  apply (cancel_mono ((GroupScheme.baseChange U.hom).map t).hom.hom).mp
  exact congrArg (fun k => k.hom.hom) h

/-- Conjugation on the torus, valued in the smooth Hom scheme of the torus,
has exactly the cosets of the represented centralizer preimage as fibers.  No
affineness of the ambient group is needed. -/
theorem exists_smooth_quotient [Smooth N.X.hom]
    (t : A.toGrp ⟶ G) [Mono t.hom.hom.left] (hA : RelativeTorus.IsTorus A.toGrp)
    (n : N ⟶ G) (hn : (torusNormalizer t).IsRepresentedBy n)
    (c : Z ⟶ N) (hc : ((torusCentralizer t).comap n).IsRepresentedBy c)
    (hZ : Smooth Z.X.hom) :
    ∃ (Q : Over S) (q : N.X ⟶ Q), Smooth q.left ∧ Surjective q.left ∧
      ∀ (U : Over S) (g h : U ⟶ N.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range c).carrier U := by
  let : Mono c.hom.hom := hc.1
  let : Smooth A.toGrp.X.hom := hA.smooth
  let : IsAffineHom A.toGrp.X.hom := hA.isAffineHom
  obtain ⟨Y, i, hi, _⟩ := exists_smooth_universal_of_relativeTorus (G := A.toGrp) hA
  let r : N.X ⟶ Y := Classical.choose (hi.existsUnique (normalizerFamily t n hn))
  have hr : evaluate r i = normalizerFamily t n hn :=
    (Classical.choose_spec (hi.existsUnique (normalizerFamily t n hn))).1
  have hfib : ∀ (U : Over S) (g h : U ⟶ N.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range c).carrier U := by
    intro U g h
    have key : g ≫ r = h ≫ r ↔
        conjugationFamily t (g ≫ n.hom.hom) = conjugationFamily t (h ≫ n.hom.hom) := by
      rw [← evaluate_normalizerFamily_comp t n hn g, ← evaluate_normalizerFamily_comp t n hn h]
      constructor
      · intro he
        rw [← hr, ← evaluate_comp, ← evaluate_comp, he]
      · intro he
        apply (hi U).injective
        change evaluate (g ≫ r) i = evaluate (h ≫ r) i
        rw [evaluate_comp, evaluate_comp, hr]
        exact cancel_baseChange_map t he
    rw [key, conjugationFamily_eq_iff, hc.2]
    change (g ≫ n.hom.hom)⁻¹ * (h ≫ n.hom.hom) ∈ (torusCentralizer t).carrier U ↔
      (g⁻¹ * h) ≫ n.hom.hom ∈ (torusCentralizer t).carrier U
    rw [MonObj.mul_comp, GrpObj.inv_comp]
  have hker : ∀ (U : Over S) (g h : U ⟶ N.X),
      g ≫ r = h ≫ r ↔ relation (arrowSpace c) (source c) (target c) U ⟨g⟩ ⟨h⟩ := by
    intro U g h
    exact (hfib U g h).trans (relation_iff c U g h).symm
  let D := schemeQuotientOfMapKernel (isEquivalenceRelation c)
    (hasSmoothProjections c hZ) (inferInstance : LocallyOfFiniteType N.X.hom) Y r hker
  exact ⟨D.scheme, D.projection, D.smooth_projection, D.surjective_projection,
    fun U g h => (D.fibers U g h).trans (relation_iff c U g h)⟩

/-- The quotient above is a homogeneous quotient when the subgroup is closed and
the normalizer is quasi-compact. -/
theorem exists_homogeneous_quotient [Smooth N.X.hom] [QuasiCompact N.X.hom]
    (t : A.toGrp ⟶ G) [Mono t.hom.hom.left] (hA : RelativeTorus.IsTorus A.toGrp)
    (n : N ⟶ G) (hn : (torusNormalizer t).IsRepresentedBy n)
    (c : Z ⟶ N) (hc : ((torusCentralizer t).comap n).IsRepresentedBy c)
    (hcclosed : IsClosedSubgroup c) (hZ : Smooth Z.X.hom) :
    Nonempty (HomogeneousQuotient c) := by
  let : Mono c.hom.hom := hc.1
  obtain ⟨Q, q, hsm, hsurj, hfib⟩ := exists_smooth_quotient t hA n hn c hc hZ
  let := hsm
  let := hsurj
  let hsep := TorusCentralizerQuotient.separated_of_closed_subgroup_quotient c hcclosed q hfib
  let : IsSeparated Q.hom := hsep
  have hqccomp : QuasiCompact (q.left ≫ Q.hom) := by rw [Over.w q]; infer_instance
  let := hqccomp
  have hqc : QuasiCompact Q.hom :=
    TorusCentralizerQuotient.quasiCompact_of_surjective_comp q.left Q.hom
  have hfp : LocallyOfFinitePresentation Q.hom := by
    have : LocallyOfFinitePresentation (q.left ≫ Q.hom) := by rw [Over.w q]; infer_instance
    exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.left Q.hom
  let := hfp
  exact ⟨⟨Q, q, hsep, inferInstance, hqc, hsm, hsurj,
    QuasiCompact.of_comp q.left Q.hom, hfib⟩⟩

end SeparatedTorusWeylQuotient

open SeparatedTorusWeylQuotient HomogeneousQuotientFromEmbedding in
/-- Given smooth closed torus normalizers in separated smooth quasi-compact
groups, a closed relative torus representing its own centralizer has a smooth
closed normalizer and a separated quasi-compact étale Weyl quotient, whose
projection is an fppf quotient by the torus. -/
theorem exists_separatedTorusWeylQuotient
    (hNorm : SeparatedTorusNormalizerStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hcent : (torusCentralizer t).IsRepresentedBy t) :
    ∃ (N : GroupScheme S) (n : N ⟶ G) (W : GroupScheme S) (q : N ⟶ W)
      (c : T.toGrp ⟶ N),
      IsClosedSubgroup n ∧ (torusNormalizer t).IsRepresentedBy n ∧
      Smooth N.X.hom ∧
      IsSeparated W.X.hom ∧ QuasiCompact W.X.hom ∧ Etale W.X.hom ∧
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      LocallyOfFinitePresentation q.hom.hom.left ∧
      (∀ (U : Over S) (y : U ⟶ N.X),
        y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (SubgroupFunctor.range t).carrier U) ∧
      c ≫ n = t ∧ IsClosedSubgroup c ∧ IsOpenImmersion c.hom.hom.left ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range c) q := by
  let : Mono t.hom.hom.left := ht.mono
  obtain ⟨N, n, hnclosed, hNs, hnrep⟩ :=
    hNorm S G inferInstance inferInstance inferInstance T t hT ht
  let : Smooth N.X.hom := hNs
  let : IsClosedImmersion n.hom.hom.left := hnclosed
  let : QuasiCompact N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  obtain ⟨c, hcn, hcopen, hcrep⟩ :=
    relativeTorusCentralizerNormalizerInclusion t hT n hnrep t hcent
  let : Mono c.hom.hom := hcrep.1
  have hcclosed : IsClosedSubgroup c :=
    IsClosedSubgroup.of_comp hnclosed (by rw [hcn]; exact ht)
  let D : HomogeneousQuotient c :=
    Classical.choice (exists_homogeneous_quotient t hT n hnrep c hcrep hcclosed hT.smooth)
  let : Smooth D.projection.left := D.smooth_projection
  let : Surjective D.projection.left := D.surjective_projection
  have hnormal : (SubgroupFunctor.range c).IsNormal := by
    rw [hcrep.2]
    intro U g x _ hx
    change (g * x * g⁻¹) ≫ n.hom.hom ∈ (torusCentralizer t).carrier U
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    apply torusCentralizer_isNormalizedBy_torusNormalizer t U
      (g ≫ n.hom.hom) (x ≫ n.hom.hom) ?_ hx
    rw [← hnrep.2]
    exact ⟨g, rfl⟩
  let W := D.groupScheme hnormal
  let q : N ⟶ W := D.groupProjection hnormal
  have hq := D.groupProjection_isFppfQuotient hnormal
  have hWe : Etale W.X.hom :=
    etale_of_open_subgroup_quotient c hcopen D.projection D.fibers
  refine ⟨N, n, W, q, c, hnclosed, hnrep, hNs, D.separated, D.quasiCompact, hWe,
    hq.1, hq.2.1, hq.2.2.1, ?_, hcn, hcclosed, hcopen, hq⟩
  intro U y
  rw [hcent.2, ← SubgroupFunctor.mem_comap, ← hcrep.2, ← hq.2.2.2, mem_range_kernelι_iff]

/-- The existence conjuncts of `SelfCentralizingTorusWeylAffinenessStatement`,
in its exact order and form, from smooth closed torus normalizers in separated
smooth quasi-compact groups. -/
theorem exists_selfCentralizingTorusWeylQuotient
    (hNorm : SeparatedTorusNormalizerStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hcent : (torusCentralizer t).IsRepresentedBy t) :
    ∃ (N : GroupScheme S) (n : N ⟶ G)
      (W : GroupScheme S) (q : N ⟶ W),
      IsClosedSubgroup n ∧ (torusNormalizer t).IsRepresentedBy n ∧
      Smooth N.X.hom ∧
      IsSeparated W.X.hom ∧ QuasiCompact W.X.hom ∧ Etale W.X.hom ∧
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      LocallyOfFinitePresentation q.hom.hom.left ∧
      (∀ (U : Over S) (y : U ⟶ N.X),
        y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (SubgroupFunctor.range t).carrier U) := by
  obtain ⟨N, n, W, q, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ :=
    exists_separatedTorusWeylQuotient hNorm G t hT ht hcent
  exact ⟨N, n, W, q, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Langlands.GroupScheme
