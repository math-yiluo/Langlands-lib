import Langlands.GroupScheme.Reductive.NormalIsogenyComplementStatement
import Langlands.GroupScheme.Reductive.CentralizerDerivedComparison
import Langlands.GroupScheme.Reductive.SemisimpleCentralizerCoreComplement
import Langlands.GroupScheme.Reductive.CommutingMultiplicationDescent
import Langlands.GroupScheme.Derived.SemisimplePerfectReduction
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.Action

/-! # Arbitrary-field normal complements from geometric generation and perfectness -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Almost-simple generation and semisimple perfectness over algebraically closed
fields imply the exact arbitrary-field normal-isogeny-complement proposition. -/
theorem semisimpleNormalIsogenyComplement_of_generation_and_perfectness
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u})
    (hperf : AlgebraicallyClosedSemisimplePerfectStatement.{u}) :
    SemisimpleNormalIsogenyComplementStatement.{u} := by
  intro k _ G H hG j hj hHs hHc hjn
  let : Smooth H.X.hom := hHs
  let : ConnectedSpace H.X.left := hHc
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hH : IsSemisimple H := hG.of_normalSubgroup j hj hjn
  let C := closedNormalCentralizer j hjn
  let : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedSubgroup
  let : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom C.group.X.hom := by
    rw [← Over.w C.inclusion.hom.hom]
    infer_instance
  let : LocallyOfFiniteType C.group.X.hom := by
    rw [← Over.w C.inclusion.hom.hom]
    infer_instance
  have hC : (AutomorphicAction.conjugation j).fixedSubgroup.IsRepresentedBy C.inclusion :=
    ⟨inferInstance, C.range_eq⟩
  obtain ⟨D, d, hDa, hDl, hd⟩ := derivedSubgroupRepresentability k C.group
  let : IsAffineHom D.X.hom := hDa
  let : LocallyOfFiniteType D.X.hom := hDl
  let i : D ⟶ G := d ≫ C.inclusion
  have hi : IsClosedSubgroup i := by
    let : IsClosedImmersion d.hom.hom.left := hd.1
    change IsClosedImmersion (d.hom.hom.left ≫ C.inclusion.hom.hom.left)
    infer_instance
  have hin : (SubgroupFunctor.range i).IsNormal :=
    hd.isNormal_comp C.inclusion C.isClosedSubgroup C.isNormal
  have hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ D.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom) := by
    intro T h x
    simpa only [i, Grp.comp_hom_hom, Category.assoc] using
      C.commute T h (x ≫ d.hom.hom)
  obtain ⟨Z, z, hz, _⟩ := hH.hasFiniteCenter
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have hGb : IsSemisimple (F.obj G) := hG.baseChange_toAlgebraicClosure
  have hHb : IsSemisimple (F.obj H) := hH.baseChange_toAlgebraicClosure
  let : IsAffineHom (F.obj G).X.hom := hGb.isConnectedReductive.isAffineHom
  let : Smooth (F.obj G).X.hom := hGb.isConnectedReductive.smooth
  let : Smooth (F.obj H).X.hom := hHb.isConnectedReductive.smooth
  let : ConnectedSpace (F.obj H).X.left := hHb.isConnectedReductive.connectedSpace
  have hjb : IsClosedSubgroup (F.map j) := hj.baseChange b
  have hjnb : (SubgroupFunctor.range (F.map j)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact SubgroupFunctor.IsNormal.baseChange b hjn
  have hCb := isRepresentedBy_conjugation_fixedSubgroup_baseChange b hC
  let Cb : ClosedNormalCentralizer (F.map j) := {
    group := F.obj C.group
    inclusion := F.map C.inclusion
    isClosedSubgroup := C.isClosedSubgroup.baseChange b
    range_eq := hCb.2
    isNormal := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact SubgroupFunctor.IsNormal.baseChange b C.isNormal
    commute := (range_le_conjugation_fixedSubgroup_iff (F.map j)
      (F.map C.inclusion)).mp (le_of_eq hCb.2) }
  let : IsClosedImmersion Cb.inclusion.hom.hom.left := Cb.isClosedSubgroup
  let : IsAffineHom Cb.group.X.hom := by
    rw [← Over.w Cb.inclusion.hom.hom]
    infer_instance
  let : LocallyOfFiniteType Cb.group.X.hom := by
    rw [← Over.w Cb.inclusion.hom.hom]
    infer_instance
  let K := ReducedSubgroup.identityCore Cb.group
  let d₀ : K ⟶ Cb.group := ReducedSubgroup.identityCoreι Cb.group
  let i₀ : K ⟶ F.obj G := d₀ ≫ Cb.inclusion
  have hd₀ : IsClosedSubgroup d₀ := inferInstanceAs
    (IsClosedImmersion (ReducedSubgroup.identityCoreι Cb.group).hom.hom.left)
  have hi₀ : IsClosedSubgroup i₀ := by
    change IsClosedImmersion (d₀.hom.hom.left ≫ Cb.inclusion.hom.hom.left)
    infer_instance
  have hi₀n : (SubgroupFunctor.range i₀).IsNormal :=
    ReducedSubgroup.isNormal_range_identityCoreι_comp
      Cb.inclusion Cb.isClosedSubgroup Cb.isNormal
  have hK : IsSemisimple K := hGb.of_normalSubgroup i₀ hi₀ hi₀n
  have hKp : derivedSubgroup K = ⊤ := hperf (AlgebraicClosure k) K hK
  have hm := flat_surjective_centralizerCoreMultiplication_of_almostSimpleGeneration
    hgen hGb (F.map j) hjb hjnb Cb
  let : Flat (subgroupMultiplication (F.map j) i₀).left := hm.1
  let : Surjective (subgroupMultiplication (F.map j) i₀).left := hm.2
  have hprod := ImageGeneration.affineFiniteType_tensor (F.obj H).X K.X
  let : IsAffineHom ((F.obj H) ⊗ K).X.hom := hprod.1
  let : IsAffineHom ((subgroupMultiplication (F.map j) i₀).left ≫ (F.obj G).X.hom) := by
    rw [Over.w]
    exact hprod.1
  let : IsAffineHom (subgroupMultiplication (F.map j) i₀).left :=
    IsAffineHom.of_comp _ (F.obj G).X.hom
  let : QuasiCompact (subgroupMultiplication (F.map j) i₀).left := inferInstance
  let e : K ≅ F.obj D :=
    CentralizerProduct.derivedIsoOfFieldExtension j C.inclusion hC z hz hd d₀ hd₀ hKp
  have he : e.hom ≫ F.map d = d₀ :=
    CentralizerProduct.derivedIsoOfFieldExtension_hom_comp
      j C.inclusion hC z hz hd d₀ hd₀ hKp
  have hD : IsSemisimple D :=
    CentralizerProduct.semisimple_of_fieldExtension
      j C.inclusion hC z hz hd d₀ hd₀ hKp hK
  let : Smooth D.X.hom := hD.isConnectedReductive.smooth
  let : ConnectedSpace D.X.left := hD.isConnectedReductive.connectedSpace
  have hei : e.hom ≫ F.map i = i₀ := by
    simp only [i, Functor.map_comp, ← Category.assoc, he]
    rfl
  let p : (F.obj H).X ⊗ K.X ⟶ (F.obj H).X ⊗ (F.obj D).X :=
    𝟙 (F.obj H).X ⊗ₘ e.hom.hom.hom
  have hp : p ≫ subgroupMultiplication (F.map j) (F.map i) =
      subgroupMultiplication (F.map j) i₀ := by
    simp only [p, subgroupMultiplication, MonObj.comp_mul, tensorHom_fst_assoc,
      tensorHom_snd_assoc, Category.id_comp]
    rw [← Grp.comp_hom_hom, hei]
  have hsb : Surjective (subgroupMultiplication (F.map j) (F.map i)).left := by
    let : Surjective (p.left ≫ (subgroupMultiplication (F.map j) (F.map i)).left) := by
      rw [← Over.comp_left, hp]
      exact hm.2
    exact Surjective.of_comp p.left _
  let m := semisimpleCommutingMultiplicationOfFieldExtension
    j i hj hi hG inferInstance inferInstance inferInstance inferInstance hc hsb
    hH.hasFiniteCenter hD.hasFiniteCenter
  exact ⟨hH, D, i, hD, hi, hin, m.property.2, hc, m.property.1⟩

/-- Choose the actual semisimple commuting normal complement, under the same
explicit geometric generation and perfectness inputs. -/
def semisimpleNormalIsogenyComplementOfGenerationAndPerfectness
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u})
    (hperf : AlgebraicallyClosedSemisimplePerfectStatement.{u})
    {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSemisimple G) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hjn : (SubgroupFunctor.range j).IsNormal) :
    {K : CommutingNormalComplement j //
      IsSemisimple H ∧ IsSemisimple K.group ∧ IsSemisimple (H ⊗ K.group) ∧
      IsCentralIsogeny (commutingSubgroupMultiplicationHom j K.inclusion K.commutes)} :=
  Classical.choice (by
    obtain ⟨hH, K, i, hK, hi, hin, hprod, hc, hm⟩ :=
      semisimpleNormalIsogenyComplement_of_generation_and_perfectness hgen hperf
        k G H hG j hj inferInstance inferInstance hjn
    exact ⟨⟨⟨K, i, hi, hin, hc, hm.flat, hm.surjective⟩, hH, hK, hprod, hm⟩⟩)

end Langlands.GroupScheme
