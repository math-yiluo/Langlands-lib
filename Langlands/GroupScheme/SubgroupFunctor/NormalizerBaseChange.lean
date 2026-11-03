import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Base change and fpqc descent of normalizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S S' : Scheme.{u}} {G H : GroupScheme S}

/-- A normalizing point remains normalizing after arbitrary base change. -/
theorem normalizer_baseChange_le (b : S' ⟶ S) (F : SubgroupFunctor G) :
    F.normalizer.baseChange b ≤ (F.baseChange b).normalizer := by
  intro U g hg V a x hx
  change baseChangePointsEquiv b G U g ∈ F.normalizer.carrier _ at hg
  have h := hg ((Over.map b).obj V) ((Over.map b).map a)
    (baseChangePointsEquiv b G V x) hx
  constructor
  · change baseChangePointsEquiv b G V ((a ≫ g) * x * (a ≫ g)⁻¹) ∈ F.carrier _
    simpa only [map_mul, map_inv, baseChangePointsEquiv_naturality] using h.1
  · change baseChangePointsEquiv b G V ((a ≫ g)⁻¹ * x * (a ≫ g)) ∈ F.carrier _
    simpa only [map_mul, map_inv, baseChangePointsEquiv_naturality] using h.2

/-- Normalizer membership after base change tests all refinements over the original base. -/
theorem normalizer_le_baseChange (b : S' ⟶ S) (F : SubgroupFunctor G) :
    (F.baseChange b).normalizer ≤ F.normalizer.baseChange b := by
  intro U g hg
  change baseChangePointsEquiv b G U g ∈ F.normalizer.carrier _
  intro V a x hx
  let W : Over S' := Over.mk (a.left ≫ U.hom)
  let e : (Over.map b).obj W ≅ V := Over.isoMk (Iso.refl _) (by
    change (𝟙 V.left) ≫ V.hom = (a.left ≫ U.hom) ≫ b
    have hw : a.left ≫ (U.hom ≫ b) = V.hom := a.w
    simpa only [Category.id_comp, Category.assoc] using hw.symm)
  let a' : W ⟶ U := Over.homMk a.left rfl
  let y := (baseChangePointsEquiv b G W).symm (e.hom ≫ x)
  have hy : y ∈ (F.baseChange b).carrier W := by
    change baseChangePointsEquiv b G W
      ((baseChangePointsEquiv b G W).symm (e.hom ≫ x)) ∈ F.carrier _
    rw [MulEquiv.apply_symm_apply]
    exact F.comp_mem e.hom hx
  have h := hg W a' y hy
  have ha : (Over.map b).map a' = e.hom ≫ a := by
    apply Over.OverMorphism.ext
    change a.left = (𝟙 V.left) ≫ a.left
    simp only [Category.id_comp]
  have h₁ : e.hom ≫ ((a ≫ baseChangePointsEquiv b G U g) * x *
      (a ≫ baseChangePointsEquiv b G U g)⁻¹) ∈ F.carrier _ := by
    simpa only [mem_baseChange, map_mul, map_inv, baseChangePointsEquiv_naturality,
      y, MulEquiv.apply_symm_apply, ha, MonObj.comp_mul, GrpObj.comp_inv,
      Category.assoc] using h.1
  have h₂ : e.hom ≫ ((a ≫ baseChangePointsEquiv b G U g)⁻¹ * x *
      (a ≫ baseChangePointsEquiv b G U g)) ∈ F.carrier _ := by
    simpa only [mem_baseChange, map_mul, map_inv, baseChangePointsEquiv_naturality,
      y, MulEquiv.apply_symm_apply, ha, MonObj.comp_mul, GrpObj.comp_inv,
      Category.assoc] using h.2
  exact ⟨by simpa only [Iso.inv_hom_id_assoc] using F.comp_mem e.inv h₁,
    by simpa only [Iso.inv_hom_id_assoc] using F.comp_mem e.inv h₂⟩

/-- Normalizers of arbitrary subgroup functors commute with arbitrary base change. -/
theorem normalizer_baseChange (b : S' ⟶ S) (F : SubgroupFunctor G) :
    F.normalizer.baseChange b = (F.baseChange b).normalizer :=
  le_antisymm (normalizer_baseChange_le b F) (normalizer_le_baseChange b F)

/-- Pullback identifies the normalizer points with the original normalizer points. -/
def normalizerBaseChangeEquiv (b : S' ⟶ S) (F : SubgroupFunctor G) (U : Over S') :
    ((F.baseChange b).normalizer).carrier U ≃*
      F.normalizer.carrier ((Over.map b).obj U) := by
  rw [← normalizer_baseChange]
  exact baseChangeCarrierEquiv b F.normalizer U

/-- Self-normalization descends through an fpqc base change into a represented subgroup. -/
theorem normalizer_eq_of_baseChange_eq (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b] (i : H ⟶ G) [Mono i.hom.hom]
    (h : ((range i).baseChange b).normalizer = (range i).baseChange b) :
    (range i).normalizer = range i := by
  apply le_antisymm
  · apply le_range_of_baseChange_le b i
    rw [normalizer_baseChange, h]
  · exact le_normalizer _

/-- Self-normalization of a represented subgroup can be checked after fpqc base change. -/
theorem normalizer_baseChange_eq_iff (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b] (i : H ⟶ G) [Mono i.hom.hom] :
    ((range i).baseChange b).normalizer = (range i).baseChange b ↔
      (range i).normalizer = range i := by
  constructor
  · exact normalizer_eq_of_baseChange_eq b i
  · intro h
    rw [← normalizer_baseChange, h]

end Langlands.GroupScheme.SubgroupFunctor
