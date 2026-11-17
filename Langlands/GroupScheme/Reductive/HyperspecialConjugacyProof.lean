import Langlands.GroupScheme.Reductive.HyperspecialConjugacyStatement
import Langlands.GroupScheme.AutomorphicAction.QuotientNormalizer
import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.IntegralModel.AdjointNormalizer
import Langlands.GroupScheme.IntegralModel.OfReductive

/-! # Assembly of the hyperspecial conjugacy criterion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme

private abbrev IntegralNormalizerCriterion : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G Gad : GroupScheme (Spec (CommRingCat.of ↥𝒪[F])))
    (hG : IsReductive G) (hGad : IsReductive Gad) (p : G ⟶ Gad)
    (hflat : Flat p.hom.hom.left) (hsurj : Surjective p.hom.hom.left),
    LocallyOfFinitePresentation p.hom.hom.left →
    ∀ (hker : IsSchemeTheoreticCenter (kernelι p)),
    haveI := hflat
    haveI := hsurj
    haveI := hG.isAffineHom
    haveI := hGad.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : IsAffine Gad.X.left := isAffine_of_isAffineHom Gad.X.hom
    let a : AutomorphicAction Gad G :=
      (AutomorphicAction.conjugation (𝟙 G)).quotientAction p
        (AutomorphicAction.conjugation_kernelActsTrivially hker)
    let T : Over (Spec (CommRingCat.of ↥𝒪[F])) := Over.mk (Spec.algebraMap ↥𝒪[F] F)
    let res : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of ↥𝒪[F]))) := Over.homMk T.hom
    ∀ z : T ⟶ Gad.X, a.PreservesRestrictionImage res z →
      ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of ↥𝒪[F]))) ⟶ Gad.X, z = res ≫ y

private theorem integralNormalizerCriterion : IntegralNormalizerCriterion.{u} := by
  intro F _ _ _ _ G Gad hG hGad p hflat hsurj hlfp hker
  let := hflat
  let := hsurj
  let := hG.isAffineHom
  let := hGad.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine Gad.X.left := isAffine_of_isAffineHom Gad.X.hom
  let b := Spec.algebraMap ↥𝒪[F] F
  let GF := (GroupScheme.baseChange b).obj G
  let AF := (GroupScheme.baseChange b).obj Gad
  let pF : GF ⟶ AF := (GroupScheme.baseChange b).map p
  let hq : IsRelativeAdjointQuotient p :=
    ⟨hG, hGad, hflat, hsurj, hlfp, hker.2⟩
  let hqF : IsAdjointQuotient pF := hq.fieldQuotient b
  let : Surjective pF.hom.hom.left := hqF.surjective
  let : IsDominant pF.hom.hom.left := inferInstance
  let M : IntegralModel ↥𝒪[F] F GF := IntegralModel.ofReductive G hG
  let N : IntegralModel ↥𝒪[F] F AF := IntegralModel.ofReductive Gad hGad
  let T : Over (Spec (CommRingCat.of ↥𝒪[F])) := Over.mk b
  let res : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of ↥𝒪[F]))) := Over.homMk T.hom
  let a : AutomorphicAction Gad G :=
    (AutomorphicAction.conjugation (𝟙 G)).quotientAction p
      (AutomorphicAction.conjugation_kernelActsTrivially hker)
  let EG : rationalPoints GF ≃* (T ⟶ G.X) := baseChangeBasePointsEquiv b G
  let EA : rationalPoints AF ≃* (T ⟶ Gad.X) := baseChangeBasePointsEquiv b Gad
  let φ : rationalPoints GF →* rationalPoints AF := rationalPoints.map pF
  let qT : (T ⟶ G.X) →* (T ⟶ Gad.X) :=
    { toFun g := g ≫ p.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' _ _ := MonObj.mul_comp _ _ _ }
  let K : Subgroup (T ⟶ G.X) := (G.points.map res.op).hom.range
  have hKG : M.integralPoints.map EG.toMonoidHom = K := by
    ext g
    rw [Subgroup.mem_map_equiv]
    change (baseChangeBasePointsEquiv b G).symm g ∈
        (IntegralModel.ofReductive (K := F) G hG).integralPoints ↔
      ∃ y : rationalPoints G, res ≫ y = g
    rw [IntegralModel.ofReductive_baseChangePoint_mem_integralPoints_iff]
    exact exists_congr fun _ => eq_comm
  have hcomp : EA.toMonoidHom.comp φ = qT.comp EG.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    exact baseChangeBasePointsEquiv_comp b p g
  have hH : (M.integralPoints.map φ).map EA.toMonoidHom = K.map qT := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hKG]
  have hlift {U : Over (Spec (CommRingCat.of ↥𝒪[F]))} (h g : U ⟶ G.X) :
      a.act (h ≫ p.hom.hom) g = h * g * h⁻¹ := by
    dsimp only [a]
    rw [AutomorphicAction.quotientAction_act_lift, AutomorphicAction.conjugation_act,
      Grp.id_hom_hom, Category.comp_id]
  have hnormalizes (z : T ⟶ Gad.X) (hz : a.PreservesRestrictionImage res z) :
      EA.symm z ∈ Subgroup.normalizer
        (M.integralPoints.map φ : Set (rationalPoints AF)) := by
    have hKz : K.map (a.pointAut T z).toMonoidHom = K :=
      AutomorphicAction.PreservesRestrictionImage.map_pointAut_range_eq a res z hz
    have hzN := AutomorphicAction.mem_normalizer_map_of_map_pointAut_eq
      qT (a.pointAut T z) z K hKz (fun g => a.act_comp_eq_conjugation p hlift z g)
    have hzMap : z ∈ (Subgroup.normalizer
        (M.integralPoints.map φ : Set (rationalPoints AF))).map EA.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq, hH]
      exact hzN
    exact Subgroup.mem_map_equiv.mp hzMap
  have hIntegralNormalizes : M.IntegralPointsNormalizeImage N pF := by
    intro w hw
    obtain ⟨y, hy⟩ := (IntegralModel.ofReductive_mem_integralPoints_iff Gad hGad w).mp hw
    have hy' : EA w = res ≫ y := hy
    have hwPres : a.PreservesRestrictionImage res (EA w) := by
      rw [hy']
      exact a.preservesRestrictionImage_restrict res y
    simpa only [MulEquiv.symm_apply_apply] using hnormalizes (EA w) hwPres
  have hN : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj N.group) :=
    hGad.isConnectedReductive_baseChange _
  have hNormalEq := IntegralModel.normalizer_map_integralPoints_eq
    hqF.isConnectedReductive hqF.isAdjoint M N hN pF hIntegralNormalizes
  dsimp only
  intro z hz
  apply (IntegralModel.ofReductive_baseChangePoint_mem_integralPoints_iff Gad hGad z).mp
  rw [← hNormalEq]
  exact hnormalizes z hz

private theorem conjugacy_of_integralNormalizer
    (hnormal : IntegralNormalizerCriterion.{u}) :
    ReductiveHyperspecialConjugacyStatement.{u} := by
  intro F _ _ _ _ G Gad hG hGad p _hsplit hflat hsurj hlfp hker
  let := hflat
  let := hsurj
  let := hG.isAffineHom
  let := hGad.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine Gad.X.left := isAffine_of_isAffineHom Gad.X.hom
  let a : AutomorphicAction Gad G :=
    (AutomorphicAction.conjugation (𝟙 G)).quotientAction p
      (AutomorphicAction.conjugation_kernelActsTrivially hker)
  let T : Over (Spec (CommRingCat.of ↥𝒪[F])) := Over.mk (Spec.algebraMap ↥𝒪[F] F)
  let res : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of ↥𝒪[F]))) := Over.homMk T.hom
  have hlift (h g : T ⟶ G.X) :
      a.act (h ≫ p.hom.hom) g = h * g * h⁻¹ := by
    dsimp only [a]
    rw [AutomorphicAction.quotientAction_act_lift, AutomorphicAction.conjugation_act,
      Grp.id_hom_hom, Category.comp_id]
  dsimp only
  intro x
  exact a.conjugacy_iff_factorization_of_preservesRestrictionImage res p hlift
    (hnormal F G Gad hG hGad p hflat hsurj hlfp hker) x

/-- The unchanged hyperspecial conjugacy criterion, proved by the dense bounded
normalizer theorem and maximal compactness of integral points. -/
theorem reductiveHyperspecialConjugacy : ReductiveHyperspecialConjugacyStatement.{u} :=
  conjugacy_of_integralNormalizer integralNormalizerCriterion

end Langlands.GroupScheme
