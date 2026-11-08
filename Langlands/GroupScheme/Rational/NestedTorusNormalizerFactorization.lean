import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyReduction
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Correcting nested-torus normalizers by the full centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (f : S ⟶ T)
  (hi : IsMaximalSplitTorus i)
  (j : H ⟶ G)
  (hj : (torusCentralizer (CommGroupScheme.groupHom f ≫ i)).IsRepresentedBy j)
  (hjc : IsClosedSubgroup j)
  (hH : MaximalSplitToriAreConjugate H)

include hi hj hjc hH

/-- Conjugacy of maximal split tori inside the actual represented centralizer
corrects every lower normalizer to a common upper and lower normalizer. -/
theorem exists_centralizer_mul_commonNormalizer
    (nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i)) :
    ∃ z : centralizerPoints (CommGroupScheme.groupHom f ≫ i),
      ∃ nT : normalizerPoints i,
        (nT : Over.mk (𝟙 _) ⟶ G.X) ∈
            normalizerPoints (CommGroupScheme.groupHom f ≫ i) ∧
          (nS : Over.mk (𝟙 _) ⟶ G.X) =
            (z : Over.mk (𝟙 _) ⟶ G.X) * (nT : Over.mk (𝟙 _) ⟶ G.X) := by
  let a := CommGroupScheme.groupHom f ≫ i
  have hcontained : SubgroupFunctor.range i ≤ torusCentralizer a :=
    range_le_torusCentralizer_of_factor a i (CommGroupScheme.groupHom f) rfl
  let iH := hj.factorHom i hcontained
  have hiH : iH ≫ j = i := hj.factorHom_comp _ _
  have hconjcontained :
      SubgroupFunctor.range
          (i ≫ (G.innerIso (nS : Over.mk (𝟙 _) ⟶ G.X)).hom) ≤
        torusCentralizer a := by
    rintro U _ ⟨x, rfl⟩
    change U ⟶ T.X at x
    change x ≫ (i ≫ (G.innerIso
      (nS : Over.mk (𝟙 _) ⟶ G.X)).hom).hom.hom ∈
        (torusCentralizer a).carrier U
    simp only [Grp.comp_hom_hom, ← Category.assoc]
    rw [comp_innerIso_hom]
    exact torusCentralizer_isNormalizedBy_torusNormalizer a U _ _
      (normalizerPointsRestrict a U nS).property (hcontained U ⟨x, rfl⟩)
  let iH' := hj.factorHom
    (i ≫ (G.innerIso (nS : Over.mk (𝟙 _) ⟶ G.X)).hom) hconjcontained
  have hiH' : iH' ≫ j =
      i ≫ (G.innerIso (nS : Over.mk (𝟙 _) ⟶ G.X)).hom :=
    hj.factorHom_comp _ _
  have hm : IsMaximalSplitTorus iH := by
    apply IsMaximalSplitTorus.of_comp hjc
    rwa [hiH]
  have hm' : IsMaximalSplitTorus iH' := by
    apply IsMaximalSplitTorus.of_comp hjc
    rw [hiH']
    exact hi.comp_iso (G.innerIso (nS : Over.mk (𝟙 _) ⟶ G.X))
  obtain ⟨h, e, he⟩ := hH T T iH' iH hm' hm
  let c : Over.mk (𝟙 _) ⟶ G.X := h ≫ j.hom.hom
  have hc : c ∈ centralizerPoints a := by
    rw [← torusCentralizer_carrier_base a, ← hj.2]
    exact ⟨h, rfl⟩
  have hn : i ≫ (G.innerIso (c * (nS : Over.mk (𝟙 _) ⟶ G.X))).hom =
      e.hom ≫ i := by
    calc
      _ = (i ≫ (G.innerIso (nS : Over.mk (𝟙 _) ⟶ G.X)).hom) ≫
          (G.innerIso c).hom := by
        rw [innerIso_mul_hom, Category.assoc]
      _ = (iH' ≫ (H.innerIso h).hom) ≫ j := by
        rw [← hiH']
        simp only [c, Category.assoc, innerIso_hom_comp]
      _ = e.hom ≫ i := by
        rw [he, Category.assoc, hiH]
  let σ : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  let nT : normalizerPoints i :=
    ⟨c * (nS : Over.mk (𝟙 _) ⟶ G.X), ⟨σ, hn⟩⟩
  refine ⟨⟨c⁻¹, (centralizerPoints a).inv_mem hc⟩, nT, ?_, ?_⟩
  · exact (normalizerPoints a).mul_mem
      (centralizerPoints_le_normalizerPoints a hc) nS.property
  · change (nS : Over.mk (𝟙 _) ⟶ G.X) = c⁻¹ * (c * nS.val)
    group

/-- Choose an actual centralizer point and an actual common normalizer
whose product is the supplied lower normalizer. -/
def normalizerCentralizerFactorization
    (nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i)) :
    (z : centralizerPoints (CommGroupScheme.groupHom f ≫ i)) ×
      {nT : normalizerPoints i //
        (nT : Over.mk (𝟙 _) ⟶ G.X) ∈
            normalizerPoints (CommGroupScheme.groupHom f ≫ i) ∧
          (nS : Over.mk (𝟙 _) ⟶ G.X) =
            (z : Over.mk (𝟙 _) ⟶ G.X) * (nT : Over.mk (𝟙 _) ⟶ G.X)} :=
  let hex := exists_centralizer_mul_commonNormalizer i f hi j hj hjc hH nS
  ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

end Langlands.GroupScheme
