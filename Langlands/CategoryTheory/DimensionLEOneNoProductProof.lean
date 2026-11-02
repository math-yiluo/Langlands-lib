import Langlands.CategoryTheory.AbelianSubcategoryStatement

/-!
# The line has no binary product in the dimension-at-most-one subcategory

Proof of `Langlands.CategoryTheory.DimensionLEOneLineHasNoBinaryProduct`:
for any field `K`, no object of the full subcategory of vector spaces of
dimension at most one, with any pair of projections, is a categorical binary
product of the actual line `K` with itself.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.CategoryTheory

/-- The endomorphism of the actual line sending `1` to the scalar `a`. -/
noncomputable def dimensionLEOneLineEndo (K : Type u) [Field K] (a : K) :
    dimensionLEOneLine K ⟶ dimensionLEOneLine K :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton K K a))

@[simp]
lemma dimensionLEOneLineEndo_apply_one (K : Type u) [Field K] (a : K) :
    (dimensionLEOneLineEndo K a).hom.hom (1 : K) = a := by
  simp [dimensionLEOneLineEndo]

/-- If the line has an internal binary product `V` with projections `p, q`,
then `x ↦ (p x, q x)` is a surjective linear map `V → K × K`. -/
lemma dimensionLEOneLine_prod_surjective (K : Type u) [Field K]
    [HasBinaryProduct (dimensionLEOneLine K) (dimensionLEOneLine K)] :
    Function.Surjective
      (((prod.fst : dimensionLEOneLine K ⨯ dimensionLEOneLine K ⟶ _).hom.hom).prod
        (prod.snd : dimensionLEOneLine K ⨯ dimensionLEOneLine K ⟶ _).hom.hom) := by
  rintro ⟨a, b⟩
  refine ⟨(prod.lift (dimensionLEOneLineEndo K a) (dimensionLEOneLineEndo K b)).hom.hom 1, ?_⟩
  have ha : (prod.fst : dimensionLEOneLine K ⨯ dimensionLEOneLine K ⟶ _).hom.hom
      ((prod.lift (dimensionLEOneLineEndo K a) (dimensionLEOneLineEndo K b)).hom.hom 1) = a := by
    exact (congrArg (fun g => g.hom.hom (1 : K))
      (prod.lift_fst (dimensionLEOneLineEndo K a) (dimensionLEOneLineEndo K b))).trans
        (dimensionLEOneLineEndo_apply_one K a)
  have hb : (prod.snd : dimensionLEOneLine K ⨯ dimensionLEOneLine K ⟶ _).hom.hom
      ((prod.lift (dimensionLEOneLineEndo K a) (dimensionLEOneLineEndo K b)).hom.hom 1) = b := by
    exact (congrArg (fun g => g.hom.hom (1 : K))
      (prod.lift_snd (dimensionLEOneLineEndo K a) (dimensionLEOneLineEndo K b))).trans
        (dimensionLEOneLineEndo_apply_one K b)
  exact Prod.ext ha hb

/-- The actual line has no categorical binary product with itself in the
dimension-at-most-one full subcategory. -/
theorem dimensionLEOneLineHasNoBinaryProduct_proof (K : Type u) [Field K] :
    DimensionLEOneLineHasNoBinaryProduct K := by
  intro h
  obtain ⟨hfin, hle⟩ := (dimensionLEOneLine K ⨯ dimensionLEOneLine K).property
  have h2 := LinearMap.finrank_le_finrank_of_surjective (dimensionLEOneLine_prod_surjective K)
  simp only [Module.finrank_prod, Module.finrank_self] at h2
  omega

end Langlands.CategoryTheory
