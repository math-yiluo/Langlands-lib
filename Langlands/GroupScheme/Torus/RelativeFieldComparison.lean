import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalAmbient
import Mathlib.RingTheory.Etale.Field

/-! # Comparing relative tori and field tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Over a field, splitting over a field extension is equivalent to splitting
on an étale cover. -/
def RelativeFieldTorusComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    RelativeTorus.IsTorus G ↔ IsTorus G

/-- A field-valued point of an étale splitting cover gives a splitting field. -/
theorem RelativeTorus.IsTorus.isTorus {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : RelativeTorus.IsTorus G) :
    _root_.Langlands.GroupScheme.IsTorus G := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨a, y, _hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint k)
  let K := (𝒰.X a).residueField y
  let b := (𝒰.X a).fromSpecResidueField y ≫ 𝒰.f a
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  refine ⟨K, inferInstance, inferInstance, ?_⟩
  change IsSplitTorus ((GroupScheme.baseChange (Spec.map (Spec.preimage b))).obj G)
  rw [Spec.map_preimage]
  exact IsSplitTorus.of_iso
    (baseChangeCompIso (𝒰.f a) ((𝒰.X a).fromSpecResidueField y) G)
    ((h𝒰 a).baseChange _)

/-- A finite Galois splitting extension supplies a one-member étale cover. -/
theorem IsTorus.isRelativeTorus {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsTorus G) :
    RelativeTorus.IsTorus G := by
  obtain ⟨K, hK, aK, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k G hG
  let := hK
  let := aK
  let := hfin
  let := hgal
  let : Algebra.FinitePresentation k K :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hb : Etale b := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr
      ⟨Algebra.FormallyEtale.of_isSeparable k K, inferInstance⟩
  have hs : Surjective b := (fieldExtension_fpqc k K).1
  refine ⟨Scheme.Cover.mkOfCovers (P := @Etale) PUnit
    (fun _ => Spec (CommRingCat.of K)) (fun _ => b)
    (fun x => ?_) (fun _ => hb), fun _ => hsplit⟩
  obtain ⟨y, hy⟩ := hs.surj x
  exact ⟨PUnit.unit, y, hy⟩

/-- The two published torus predicates agree over every field. -/
theorem relativeFieldTorusComparison : RelativeFieldTorusComparisonStatement.{u} :=
  fun _ _ _ => ⟨RelativeTorus.IsTorus.isTorus, IsTorus.isRelativeTorus⟩

end Langlands.GroupScheme
