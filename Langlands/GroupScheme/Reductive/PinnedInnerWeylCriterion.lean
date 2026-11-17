import Langlands.GroupScheme.Reductive.PinnedWeylInner
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.AutomorphicAction.LocallyInnerTransport
import Langlands.GroupScheme.SchemeActionRationalPoints
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The Weyl criterion for inner automorphisms normalizing a split maximal torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The field adjoint quotient is an fppf quotient by the full centre. -/
theorem IsAdjointQuotient.isFppfQuotient
    {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A}
    (hq : IsAdjointQuotient q) : RelativeRoot.IsFppfQuotient (center G) q :=
  ⟨hq.flat, hq.surjective, hq.locallyOfFinitePresentation, hq.kernel_range_eq_center⟩

/-- The inner action of a field adjoint quotient pulls back to conjugation. -/
theorem IsAdjointQuotient.innerAction_restrict
    {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A}
    (hq : IsAdjointQuotient q) :
    hq.innerAction.restrict q = AutomorphicAction.conjugation (𝟙 G) := by
  apply AutomorphicAction.ext_hom
  have h :
      (hq.innerAction.restrict q).act (fst G.X G.X) (snd G.X G.X) =
        (AutomorphicAction.conjugation (𝟙 G)).act
          (fst G.X G.X) (snd G.X G.X) := by
    simp only [AutomorphicAction.restrict_act, hq.innerAction_act_lift,
      AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
  simpa only [AutomorphicAction.act, lift_fst_snd, Category.id_comp] using h

/-- Over an algebraically closed field, an fppf-locally inner automorphism is conjugation
by a rational point of the original group. -/
theorem IsFppfLocallyInner.exists_innerIso_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {f : G ≅ G}
    (hf : IsFppfLocallyInner f) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, G.innerIso n = f := by
  obtain ⟨V, hflat, hsurj, hpres, y, hy⟩ := hf
  let : LocallyOfFinitePresentation V.hom := hpres
  have : Nonempty V.left := ⟨(hsurj.surj (IsLocalRing.closedPoint k)).choose⟩
  obtain ⟨s⟩ := nonempty_rationalPoints V
  refine ⟨s ≫ y, ?_⟩
  apply Iso.ext
  apply hom_ext_points
  intro W g
  let t : W ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    Over.homMk W.hom (by simp)
  have h := hy (t ≫ s) g
  simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
    Category.comp_id, Category.assoc, comp_innerIso_hom, constantPoint] using h

namespace SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

/-- A full root-datum automorphism normalizing the chosen torus is Weyl if its ambient
automorphism is fppf-locally inner. -/
theorem mem_weylGroup_of_locallyInner
    (f : G ≅ G) (t : p.torus ≅ p.torus)
    (hf : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (δ : p.rootDatum.Aut) (hδ : ∀ χ, δ.weightMap χ = t.inv ≫ χ)
    (hinner : IsFppfLocallyInner f) : δ ∈ p.rootDatum.weylGroup := by
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let pK := p.baseChange (F := K)
  have hinnerK := hinner.baseChange b
  obtain ⟨n, hn⟩ := hinnerK.exists_innerIso_of_isAlgClosed
  have hfK : pK.inclusion ≫ (((GroupScheme.baseChange b).obj G).innerIso n).hom =
      CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).mapIso t).hom ≫
        pK.inclusion := by
    rw [hn]
    change (GroupScheme.baseChange b).map p.inclusion ≫
        (GroupScheme.baseChange b).map f.hom = _
    rw [← Functor.map_comp, hf, Functor.map_comp]
    rfl
  obtain ⟨w, hw, hwχ⟩ := StarActionIndependence.exists_weyl_of_isNormalizingPoint pK hfK
  let e := p.baseChangeRootDatumEquiv (F := K)
  let e' := RootPairing.Equiv.symm _ _ e
  have heq : StarActionIndependence.conjAut e' w = δ := by
    apply StarActionIndependence.equiv_ext_of_weightMap
    intro χ
    have hinv : e'.weightEquiv.symm χ = e.weightEquiv χ := by
      apply e'.weightEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      change χ = e.weightEquiv.symm (e.weightEquiv χ)
      rw [LinearEquiv.symm_apply_apply]
    apply e.weightEquiv.injective
    rw [StarActionIndependence.conjAut_weightMap, hinv]
    change e.weightEquiv (e.weightEquiv.symm (w.weightEquiv
        (e.weightEquiv χ))) = e.weightEquiv (δ.weightEquiv χ)
    rw [LinearEquiv.apply_symm_apply]
    change w.weightMap (characterLattice.baseChange b p.torus χ) =
      characterLattice.baseChange b p.torus (δ.weightMap χ)
    rw [hwχ, hδ]
    exact (characterLattice.baseChange_precomp b t.inv χ).symm
  rw [← heq]
  exact StarActionIndependence.conjAut_mem_weylGroup e' hw

/-- A torus-normalizing automorphism is represented by a point of the adjoint quotient
exactly when its full root-datum action is Weyl. -/
theorem exists_adjointPoint_iff_mem_weylGroup
    {A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A}
    (hq : IsAdjointQuotient q)
    (f : G ≅ G) (t : p.torus ≅ p.torus)
    (hf : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (δ : p.rootDatum.Aut) (hδ : ∀ χ, δ.weightMap χ = t.inv ≫ χ) :
    (∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X,
      hq.innerAction.basePointIso x = f) ↔ δ ∈ p.rootDatum.weylGroup := by
  constructor
  · rintro ⟨x, hx⟩
    apply p.mem_weylGroup_of_locallyInner f t hf δ hδ
    exact IsFppfLocallyInner.of_adjointPoint q hq.isFppfQuotient hq.innerAction
      hq.innerAction_restrict x hx
  · intro hw
    let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
    apply p.exists_adjointPoint_of_weylImage hq f t hf
    apply p.isRootDatum.abstractWeylImage_le
    refine ⟨δ, hw, ?_⟩
    ext χ
    exact hδ χ

/-- The full Weyl criterion for torus-normalizing automorphisms of this split pinning. -/
def InnerWeylCriterionStatement : Prop :=
  ∀ {A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A}
    (hq : IsAdjointQuotient q) (f : G ≅ G) (t : p.torus ≅ p.torus)
    (_hf : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (δ : p.rootDatum.Aut) (_hδ : ∀ χ, δ.weightMap χ = t.inv ≫ χ),
    (∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X,
      hq.innerAction.basePointIso x = f) ↔ δ ∈ p.rootDatum.weylGroup

/-- The criterion is proved by the local-inner necessity and pinned Weyl sufficiency. -/
theorem innerWeylCriterion : p.InnerWeylCriterionStatement := by
  intro A q hq f t hf δ hδ
  exact p.exists_adjointPoint_iff_mem_weylGroup hq f t hf δ hδ

end SplitPinning

end Langlands.GroupScheme
