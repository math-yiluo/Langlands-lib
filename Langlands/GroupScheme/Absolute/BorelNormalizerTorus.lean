import Langlands.GroupScheme.Absolute.RationalNormalizer
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Correcting a Borel-normalizing point to normalize a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G B : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual overgroup automorphism induced by `x` can be corrected by a point
of that overgroup so that the corrected point normalizes its chosen maximal torus. -/
theorem exists_mul_mem_normalizerPoints_of_overgroupIso
    (i : B ⟶ G) (f : T.toGrp ⟶ B) (hf : IsMaximalTorus f)
    (hconj : MaximalToriAreConjugate B)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (φ : B ≅ B) (hφ : i ≫ (G.innerIso x).hom = φ.hom ≫ i) :
    ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X,
      (p ≫ i.hom.hom) * x ∈ normalizerPoints (f ≫ i) := by
  obtain ⟨p, e, hp⟩ := hconj T T (f ≫ φ.hom) f (hf.comp_iso φ) hf
  have hn : (f ≫ i) ≫ (G.innerIso ((p ≫ i.hom.hom) * x)).hom =
      e.hom ≫ (f ≫ i) := by
    calc
      _ = ((f ≫ φ.hom) ≫ (B.innerIso p).hom) ≫ i := by
        rw [innerIso_mul_hom]
        simp only [Category.assoc]
        rw [reassoc_of% hφ, innerIso_hom_comp i p]
      _ = (e.hom ≫ f) ≫ i := by rw [hp]
      _ = e.hom ≫ (f ≫ i) := Category.assoc _ _ _
  let σ : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact ⟨p, σ, hn⟩

variable [IsAlgClosed k] {i : B ⟶ G}

/-- Choose an actual Borel point whose left multiplication corrects a normalizing
point to normalize the given maximal torus. The relation to the original point
is retained in the subtype's property. -/
def IsBorelSubgroup.torusNormalizerCorrection
    (hi : IsBorelSubgroup i) (f : T.toGrp ⟶ B) (hf : IsMaximalTorus f)
    (hconj : MaximalToriAreConjugate B)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    {p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X //
      (p ≫ i.hom.hom) * x ∈ normalizerPoints (f ≫ i)} :=
  let hex := exists_mul_mem_normalizerPoints_of_overgroupIso i f hf hconj x
    (hi.conjugatingIsoOfMemNormalizer hx)
    (hi.conjugatingIsoOfMemNormalizer_hom_comp hx)
  ⟨hex.choose, hex.choose_spec⟩

/-- To prove pointwise self-normalization of this Borel, it suffices to handle
the points that also normalize one fixed maximal torus of the Borel. -/
theorem IsBorelSubgroup.pointNormalizer_eq_of_torusNormalizer
    (hi : IsBorelSubgroup i) (f : T.toGrp ⟶ B) (hf : IsMaximalTorus f)
    (hconj : MaximalToriAreConjugate B)
    (hspecial : ∀ n : normalizerPoints (f ≫ i),
      n.val ∈ Subgroup.normalizer
        ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) →
      n.val ∈ (SubgroupFunctor.range i).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      (SubgroupFunctor.range i).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  apply le_antisymm ?_ Subgroup.le_normalizer
  intro x hx
  let p := hi.torusNormalizerCorrection f hf hconj hx
  have hp : p.val ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := ⟨p.val, rfl⟩
  have hn := hspecial ⟨(p.val ≫ i.hom.hom) * x, p.property⟩
    ((Subgroup.normalizer _).mul_mem (Subgroup.le_normalizer hp) hx)
  simpa only [inv_mul_cancel_left] using
    ((SubgroupFunctor.range i).carrier _).mul_mem
      (((SubgroupFunctor.range i).carrier _).inv_mem hp) hn

end Langlands.GroupScheme
