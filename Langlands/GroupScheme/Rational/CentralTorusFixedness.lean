import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # The relative Weyl action fixes actual central cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Central

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Every inner automorphism fixes an actual central group-scheme map. -/
theorem IsCentral.comp_innerIso_hom {a : H ⟶ G} (ha : IsCentral a)
    (n : Over.mk (𝟙 S) ⟶ G.X) :
    a ≫ (G.innerIso n).hom = a := by
  apply hom_ext_points
  intro U x
  rw [Grp.comp_hom_hom, ← Category.assoc, Langlands.GroupScheme.comp_innerIso_hom]
  have hc := commute_of_mem_center (ha U x) (G.constantPoint n U)
  rw [hc.symm.eq, mul_inv_cancel_right]

end Central

section Torus

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Conjugation on the chosen torus fixes every map whose composite is central. -/
theorem normalizingAut_comp_of_central (f : A ⟶ T)
    (hf : IsCentral (CommGroupScheme.groupHom f ≫ i)) (n : normalizerPoints i) :
    f ≫ (normalizingAut i n).hom = f := by
  have hn := isNormalizingPoint_normalizingAut i n
  have h : CommGroupScheme.groupHom (f ≫ (normalizingAut i n).hom) ≫ i =
      CommGroupScheme.groupHom f ≫ i := by
    change (CommGroupScheme.groupHom f ≫
      CommGroupScheme.groupHom (normalizingAut i n).hom) ≫ i = _
    rw [Category.assoc, ← hn, ← Category.assoc]
    exact hf.comp_innerIso_hom n
  have h' := congrArg (fun g => g.hom.hom.left) h
  simp only [Grp.comp_hom_hom, Over.comp_left] at h'
  have h'' := (cancel_mono _).1 h'
  change Additive.ofMul (CommGroupScheme.groupHom (f ≫ (normalizingAut i n).hom)) =
    Additive.ofMul (CommGroupScheme.groupHom f)
  congr 1
  apply Grp.hom_ext
  exact Over.OverMorphism.ext h''

namespace RealTorusSpace

/-- The vectors fixed by every element of the actual relative Weyl quotient. -/
def relativeWeylFixedSubspace : Submodule ℝ (V T) :=
  ⨅ w : relativeWeylGroup i, ((relativeWeylRealAction i w).toLinearMap - LinearMap.id).ker

@[simp] theorem mem_relativeWeylFixedSubspace (v : V T) :
    v ∈ relativeWeylFixedSubspace i ↔
      ∀ w : relativeWeylGroup i, relativeWeylRealAction i w v = v := by
  simp only [relativeWeylFixedSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

/-- The actual normalizer fixes the real image of every central torus map. -/
theorem normalizerAction_cocharacterMapReal_of_central (f : A ⟶ T)
    (hf : IsCentral (CommGroupScheme.groupHom f ≫ i))
    (n : normalizerPoints i) (v : V A) :
    normalizerAction i n (cocharacterMapReal f v) = cocharacterMapReal f v := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [cocharacterMapReal_tmul, normalizerAction_tmul, Category.assoc,
      normalizingAut_comp_of_central i f hf n]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The actual relative Weyl quotient fixes real central cocharacter images. -/
theorem relativeWeylRealAction_cocharacterMapReal_of_central (f : A ⟶ T)
    (hf : IsCentral (CommGroupScheme.groupHom f ≫ i))
    (w : relativeWeylGroup i) (v : V A) :
    relativeWeylRealAction i w (cocharacterMapReal f v) = cocharacterMapReal f v := by
  refine Quotient.inductionOn w ?_
  intro n
  exact normalizerAction_cocharacterMapReal_of_central i f hf n v

/-- Every vector in the image of an actual central torus is fixed pointwise. -/
theorem relativeWeylRealAction_eq_self_of_mem_central_range (f : A ⟶ T)
    (hf : IsCentral (CommGroupScheme.groupHom f ≫ i))
    (w : relativeWeylGroup i) {v : V T} (hv : v ∈ (cocharacterMapReal f).range) :
    relativeWeylRealAction i w v = v := by
  obtain ⟨x, rfl⟩ := hv
  exact relativeWeylRealAction_cocharacterMapReal_of_central i f hf w x

/-- The actual image of a central torus lies in the common fixed subspace. -/
theorem central_range_le_relativeWeylFixedSubspace (f : A ⟶ T)
    (hf : IsCentral (CommGroupScheme.groupHom f ≫ i)) :
    (cocharacterMapReal f).range ≤ relativeWeylFixedSubspace i := by
  intro v hv
  rw [mem_relativeWeylFixedSubspace]
  intro w
  exact relativeWeylRealAction_eq_self_of_mem_central_range i f hf w hv

end RealTorusSpace

end Torus

end Langlands.GroupScheme
