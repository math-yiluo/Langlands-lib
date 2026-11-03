import Langlands.GroupScheme.Absolute.BorelPromotion
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.BruhatCoveringReduction
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # Pointwise self-normalization from Borel conjugacy and normalization -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {H G : GroupScheme S} {i : H ⟶ G}

/-- A normalizing base point does not change the represented subgroup under conjugation. -/
theorem range_comp_innerIso_eq
    {n : Over.mk (𝟙 S) ⟶ G.X}
    (hn : n ∈ (range i).normalizer.carrier (Over.mk (𝟙 S))) :
    range (i ≫ (G.innerIso n).hom) = range i := by
  apply ext
  intro V
  ext x
  rw [mem_range, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    have hy := (hn V (Over.homMk V.hom (by simp)) (y ≫ i.hom.hom) ⟨y, rfl⟩).1
    rwa [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at ⊢
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz⟩ :=
      (hn V (Over.homMk V.hom (by simp)) (y ≫ i.hom.hom) ⟨y, rfl⟩).2
    refine ⟨z, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    change G.constantPoint n V * (z ≫ i.hom.hom) * (G.constantPoint n V)⁻¹ = _
    change z ≫ i.hom.hom =
      (G.constantPoint n V)⁻¹ * (y ≫ i.hom.hom) * G.constantPoint n V at hz
    rw [hz]
    group

/-- The restriction of a normalizing base point to any monic represented subgroup. -/
def normalizerRestrictionIso [Mono i.hom.hom]
    {n : Over.mk (𝟙 S) ⟶ G.X}
    (hn : n ∈ (range i).normalizer.carrier (Over.mk (𝟙 S))) : H ≅ H := by
  have : IsIso (G.innerIso n).hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget (Over S)).mapIso (G.innerIso n)).hom)
  let hi : (range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hj : (range i).IsRepresentedBy (i ≫ (G.innerIso n).hom) :=
    ⟨by rw [Grp.comp_hom_hom]; infer_instance, range_comp_innerIso_eq hn⟩
  exact hj.isoOfIsRepresentedBy hi

/-- The restricted automorphism has exactly the prescribed conjugation action. -/
theorem normalizerRestrictionIso_hom_comp [Mono i.hom.hom]
    {n : Over.mk (𝟙 S) ⟶ G.X}
    (hn : n ∈ (range i).normalizer.carrier (Over.mk (𝟙 S))) :
    (normalizerRestrictionIso hn).hom ≫ i = i ≫ (G.innerIso n).hom := by
  exact IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- An automorphism compatible with inner conjugation gives all-test normalization. -/
theorem mem_normalizer_range_of_innerIso
    {n : Over.mk (𝟙 S) ⟶ G.X} (σ : H ≅ H)
    (hσ : i ≫ (G.innerIso n).hom = σ.hom ≫ i) :
    n ∈ (range i).normalizer.carrier (Over.mk (𝟙 S)) := by
  have hconj {m : Over.mk (𝟙 S) ⟶ G.X} {τ : H ≅ H}
      (hτ : i ≫ (G.innerIso m).hom = τ.hom ≫ i)
      (V : Over S) (y : V ⟶ H.X) :
      (y ≫ τ.hom.hom.hom) ≫ i.hom.hom =
        G.constantPoint m V * (y ≫ i.hom.hom) * (G.constantPoint m V)⁻¹ := by
    have h := congrArg (fun f : H ⟶ G => y ≫ f.hom.hom) hτ
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at h
    simpa only [Grp.comp_hom_hom, ← Category.assoc] using h.symm
  rintro V a x ⟨y, rfl⟩
  rw [comp_eq_constantPoint a n]
  refine ⟨⟨y ≫ σ.hom.hom.hom, hconj hσ V y⟩,
    ⟨y ≫ σ.inv.hom.hom, ?_⟩⟩
  change (y ≫ σ.inv.hom.hom) ≫ i.hom.hom =
    (G.constantPoint n V)⁻¹ * (y ≫ i.hom.hom) * G.constantPoint n V
  simpa only [Iso.symm_hom, constantPoint_inv, inv_inv] using
    hconj (m := n⁻¹) (τ := σ.symm) (comp_innerIso_inv_hom hσ) V y

/-- All-test normalizers act on the ordinary point subgroup over any one test scheme. -/
theorem normalizer_carrier_le_pointNormalizer (F : SubgroupFunctor G) (T : Over S) :
    F.normalizer.carrier T ≤ Subgroup.normalizer (F.carrier T : Set (T ⟶ G.X)) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_of_mem_normalizer hn hx
  · intro hx
    have h := (hn T (𝟙 T) _ hx).2
    simpa only [Category.id_comp, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one] using h

end SubgroupFunctor

variable {k : Type u} [Field k]
  {B P G : GroupScheme (Spec (CommRingCat.of k))}

/-- Borel conjugacy inside a closed overgroup and pointwise Borel normalization force
each all-test normalizing base point of that overgroup into the overgroup. -/
theorem mem_range_of_mem_normalizer_of_borel
    (i : P ⟶ G) (j : B ⟶ G) (f : B ⟶ P)
    (hi : IsClosedSubgroup i) (hj : IsBorelSubgroup j) (hf : f ≫ i = j)
    (hconj : BorelSubgroupsAreConjugate P)
    (hnorm : Subgroup.normalizer
      ((SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : n ∈ (SubgroupFunctor.range i).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    n ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let σ := SubgroupFunctor.normalizerRestrictionIso hn
  have hσ : i ≫ (G.innerIso n).hom = σ.hom ≫ i :=
    (SubgroupFunctor.normalizerRestrictionIso_hom_comp hn).symm
  have hfB : IsBorelSubgroup f := IsBorelSubgroup.of_comp hi (by rwa [hf])
  obtain ⟨p, φ, hp⟩ := hconj B B (f ≫ σ.hom) f (hfB.comp_iso σ) hfB
  let q := p ≫ i.hom.hom
  have hq : j ≫ (G.innerIso (q * n)).hom = φ.hom ≫ j := by
    calc
      _ = (f ≫ σ.hom) ≫ (P.innerIso p).hom ≫ i := by
        rw [innerIso_mul_hom, ← hf, innerIso_hom_comp i p]
        simp only [Category.assoc]
        rw [reassoc_of% hσ]
      _ = (φ.hom ≫ f) ≫ i := by rw [← Category.assoc, hp]
      _ = φ.hom ≫ j := by rw [Category.assoc, hf]
  have hqn := SubgroupFunctor.mem_normalizer_range_of_innerIso φ hq
  have hqnB : q * n ∈ (SubgroupFunctor.range j).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [← hnorm]
    exact SubgroupFunctor.normalizer_carrier_le_pointNormalizer _ _ hqn
  have hqnP := SubgroupFunctor.range_le_of_factor f hf _ hqnB
  have hqP : q ∈ (SubgroupFunctor.range i).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := ⟨p, rfl⟩
  simpa only [inv_mul_cancel_left] using
    ((SubgroupFunctor.range i).carrier _).mul_mem
      (((SubgroupFunctor.range i).carrier _).inv_mem hqP) hqnP

end Langlands.GroupScheme
