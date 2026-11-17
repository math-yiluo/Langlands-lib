import Langlands.GroupScheme.Torus.MaximalSeparableConjugacyStatement
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Reductive.SplitIsogenyRigidityReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisChartPoint
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Maximal tori are conjugate over a finite separable extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace SubgroupConjugate

variable {S : Scheme.{u}} {H H' G : GroupScheme S} {i : H ⟶ G} {i' : H' ⟶ G}

/-- Conjugacy after base change along the identity of the base is conjugacy. -/
theorem of_baseChange_id
    (h : SubgroupConjugate ((GroupScheme.baseChange (𝟙 S)).map i)
      ((GroupScheme.baseChange (𝟙 S)).map i')) :
    SubgroupConjugate i i' := by
  have hn := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫ Functor.mapGrpIdIso).hom.naturality i
  have hn' := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫ Functor.mapGrpIdIso).hom.naturality i'
  change (GroupScheme.baseChange (𝟙 S)).map i ≫ (baseChangeIdIso G).hom =
    (baseChangeIdIso H).hom ≫ i at hn
  change (GroupScheme.baseChange (𝟙 S)).map i' ≫ (baseChangeIdIso G).hom =
    (baseChangeIdIso H').hom ≫ i' at hn'
  have h' := h.postcomp (baseChangeIdIso G).hom
  rw [hn, hn'] at h'
  exact of_precomp_isos (baseChangeIdIso H) (baseChangeIdIso H') h'

end SubgroupConjugate

/-- Maximal tori of a smooth affine group over a field become conjugate over a finite
separable extension, and over the field itself when it is separably closed. -/
theorem maximalTorusSeparableConjugacy : MaximalTorusSeparableConjugacyStatement.{u} := by
  intro k _ G _ _ T T' j j' hj hj'
  obtain ⟨𝒰, h𝒰⟩ := EtaleLocallySubgroupConjugate.of_relativeTori
    hj.1.isRelativeTorus hj'.1.isRelativeTorus
    hj.isFibrewiseMaximalTorus hj'.isFibrewiseMaximalTorus
  obtain ⟨a, y, -⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint k)
  let E : Over (Spec (CommRingCat.of k)) := Over.mk (𝒰.f a)
  have : Etale E.hom := 𝒰.map_prop a
  have : Nonempty E.left := ⟨y⟩
  obtain ⟨K, _, _, hK, hKs, ⟨w⟩⟩ :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisChartPoint.exists_separable_point E
  have hw : w.left ≫ 𝒰.f a = Spec.map (CommRingCat.ofHom (algebraMap k K)) := Over.w w
  have hconj : SubgroupConjugate
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j') := by
    rw [← hw]
    exact ((h𝒰 a).baseChange w.left).of_baseChange_comp (𝒰.f a) w.left
  refine ⟨⟨K, inferInstance, inferInstance, hK, hKs, ?_⟩, fun hk => ?_⟩
  · obtain ⟨g, e, he⟩ := hconj
    exact ⟨g, he ▸ SubgroupFunctor.range_iso_comp e _⟩
  · let σ : K ≃ₐ[k] k :=
      (AlgEquiv.ofBijective (Algebra.ofId k K) (IsSepClosed.algebraMap_bijective k K)).symm
    let s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K) :=
      Spec.map (CommRingCat.ofHom (σ : K →+* k))
    have hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) = 𝟙 _ := by
      have hσ : (σ : K →+* k).comp (algebraMap k K) = RingHom.id k := by
        ext x
        exact σ.commutes x
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ, CommRingCat.ofHom_id, Spec.map_id]
    have h₁ := (hconj.baseChange s).of_baseChange_comp _ s
    rw [hs] at h₁
    obtain ⟨g, e, he⟩ := h₁.of_baseChange_id
    exact ⟨g, he ▸ SubgroupFunctor.range_iso_comp e _⟩

end Langlands.GroupScheme
