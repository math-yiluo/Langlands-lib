import Langlands.GroupScheme.Absolute.ParabolicNormalizerPointsReduction
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Correcting overgroup normalizers by maximal-torus conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Maximal-torus conjugacy corrects a normalizer of a monic overgroup to a
normalizer of its chosen maximal torus. -/
theorem exists_overgroup_mul_normalizerPoint
    (j : H ⟶ G) [Mono j.hom.hom]
    (f : T.toGrp ⟶ H) (hf : IsMaximalTorus f)
    (hconj : MaximalToriAreConjugate H)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : n ∈ (SubgroupFunctor.range j).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (nT : normalizerPoints (f ≫ j)),
      n = (p ≫ j.hom.hom) * (nT : Over.mk (𝟙 _) ⟶ G.X) := by
  let σ := SubgroupFunctor.normalizerRestrictionIso hn
  have hσ : j ≫ (G.innerIso n).hom = σ.hom ≫ j :=
    (SubgroupFunctor.normalizerRestrictionIso_hom_comp hn).symm
  obtain ⟨p, a, hp⟩ := hconj T T (f ≫ σ.hom) f (hf.comp_iso σ) hf
  let q := p ≫ j.hom.hom
  have hq : (f ≫ j) ≫ (G.innerIso (q * n)).hom = a.hom ≫ (f ≫ j) := by
    calc
      _ = (f ≫ σ.hom) ≫ (H.innerIso p).hom ≫ j := by
        rw [innerIso_mul_hom, innerIso_hom_comp j p]
        simp only [Category.assoc]
        rw [reassoc_of% hσ]
      _ = (a.hom ≫ f) ≫ j := by rw [← Category.assoc, hp]
      _ = a.hom ≫ (f ≫ j) := Category.assoc _ _ _
  let aT : T ≅ T :=
    { hom := Additive.ofMul a.hom
      inv := Additive.ofMul a.inv
      hom_inv_id := congrArg Additive.ofMul a.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul a.inv_hom_id }
  refine ⟨p⁻¹, ⟨q * n, ⟨aT, hq⟩⟩, ?_⟩
  rw [GrpObj.inv_comp]
  change n = q⁻¹ * (q * n)
  group

/-- The torus-normalizing factor stays in any point subgroup containing the
overgroup points and the original normalizing point. -/
theorem exists_overgroup_mul_normalizerPoint_mem
    (j : H ⟶ G) [Mono j.hom.hom]
    (f : T.toGrp ⟶ H) (hf : IsMaximalTorus f)
    (hconj : MaximalToriAreConjugate H)
    (A : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hHA : (SubgroupFunctor.range j).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤ A)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} (hnA : n ∈ A)
    (hn : n ∈ (SubgroupFunctor.range j).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (nT : normalizerPoints (f ≫ j)),
      (nT : Over.mk (𝟙 _) ⟶ G.X) ∈ A ∧
        n = (p ≫ j.hom.hom) * (nT : Over.mk (𝟙 _) ⟶ G.X) := by
  obtain ⟨p, nT, h⟩ := exists_overgroup_mul_normalizerPoint j f hf hconj hn
  refine ⟨p, nT, ?_, h⟩
  have hpA := hHA (show p ≫ j.hom.hom ∈
    (SubgroupFunctor.range j).carrier _ from ⟨p, rfl⟩)
  have hmem := A.mul_mem (A.inv_mem hpA) hnA
  rwa [h, inv_mul_cancel_left] at hmem

/-- It suffices to place the torus-normalizing points of a point subgroup in
the overgroup, provided every point normalizes that overgroup on all tests. -/
theorem pointSubgroup_le_range_of_normalizer_inter_le
    (j : H ⟶ G) [Mono j.hom.hom]
    (f : T.toGrp ⟶ H) (hf : IsMaximalTorus f)
    (hconj : MaximalToriAreConjugate H)
    (A : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hHA : (SubgroupFunctor.range j).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤ A)
    (hAnorm : A ≤ (SubgroupFunctor.range j).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hTnorm : A ⊓ normalizerPoints (f ≫ j) ≤
      (SubgroupFunctor.range j).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    A ≤ (SubgroupFunctor.range j).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  intro n hn
  obtain ⟨p, nT, hnTA, h⟩ :=
    exists_overgroup_mul_normalizerPoint_mem j f hf hconj A hHA hn (hAnorm hn)
  rw [h]
  exact ((SubgroupFunctor.range j).carrier _).mul_mem ⟨p, rfl⟩
    (hTnorm ⟨hnTA, nT.property⟩)

/-- Internal normalizer-factorization statement, retaining the monomorphism,
maximality and conjugacy hypotheses. -/
def OvergroupNormalizerFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (j : H ⟶ G) [Mono j.hom.hom]
    (f : T.toGrp ⟶ H), IsMaximalTorus f → MaximalToriAreConjugate H →
    ∀ (A : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)),
      (SubgroupFunctor.range j).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤ A →
      ∀ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X), n ∈ A →
        n ∈ (SubgroupFunctor.range j).normalizer.carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))) →
        ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
          (nT : normalizerPoints (f ≫ j)),
          (nT : Over.mk (𝟙 _) ⟶ G.X) ∈ A ∧
            n = (p ≫ j.hom.hom) * (nT : Over.mk (𝟙 _) ⟶ G.X)

/-- The generic factorization with retained point-subgroup membership. -/
theorem overgroupNormalizerFactorization :
    OvergroupNormalizerFactorizationStatement.{u} := by
  intro k _ H G T j _ f hf hconj A hHA n hnA hn
  exact exists_overgroup_mul_normalizerPoint_mem j f hf hconj A hHA hnA hn

/-- Over an algebraically closed field, smoothness, affineness and connectedness
of the overgroup discharge the maximal-torus conjugacy hypothesis. -/
theorem exists_overgroup_mul_normalizerPoint_mem_of_isAlgClosed
    [IsAlgClosed k] [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace H.X.left]
    (j : H ⟶ G) [Mono j.hom.hom]
    (f : T.toGrp ⟶ H) (hf : IsMaximalTorus f)
    (A : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hHA : (SubgroupFunctor.range j).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤ A)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} (hnA : n ∈ A)
    (hn : n ∈ (SubgroupFunctor.range j).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (nT : normalizerPoints (f ≫ j)),
      (nT : Over.mk (𝟙 _) ⟶ G.X) ∈ A ∧
        n = (p ≫ j.hom.hom) * (nT : Over.mk (𝟙 _) ⟶ G.X) := by
  apply exists_overgroup_mul_normalizerPoint_mem j f hf _ A hHA hnA hn
  intro T₁ T₂ f₁ f₂ hf₁ hf₂
  exact (subgroupConjugate_iff_exists_commGroupSchemeIso f₁ f₂).mpr
    (maximalTorusConjugacy k H T₁ T₂ f₁ f₂ hf₁ hf₂)

end Langlands.GroupScheme
