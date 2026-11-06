import Langlands.Geometry.Building.FacetOrderVertexEquiv
import Langlands.Geometry.Building.RealizationApartmentTransport

/-! # Vertex permutations recovered from the original quotient action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ValuationBuildingData.PolysimplicialRealization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : ValuationBuildingData G} (R : B.PolysimplicialRealization)

@[simp] theorem facetTranslateOrderIso_one (hR : R.IsFaceCompatible)
    (Fc : R.complex.facets) :
    R.facetTranslateOrderIso hR 1 Fc = Fc := by
  apply R.realize.injective
  rw [R.realize_facetTranslateOrderIso, B.facetTranslateEquiv_one]

theorem facetTranslateOrderIso_mul (hR : R.IsFaceCompatible)
    (g h : rationalPoints G) (Fc : R.complex.facets) :
    R.facetTranslateOrderIso hR (g * h) Fc =
      R.facetTranslateOrderIso hR g (R.facetTranslateOrderIso hR h Fc) := by
  apply R.realize.injective
  simp only [R.realize_facetTranslateOrderIso, B.facetTranslateEquiv_mul]

/-- The unique vertex permutation inducing the original action on realized facets. -/
def vertexTranslateEquiv (hR : R.IsFaceCompatible) (g : rationalPoints G) :
    Equiv.Perm (∀ i, R.V i) :=
  R.complex.facetOrderVertexEquiv R.complex (R.facetTranslateOrderIso hR g)

/-- Every facet has exactly the image specified by the original quotient action. -/
theorem vertexTranslateEquiv_image (hR : R.IsFaceCompatible)
    (g : rationalPoints G) (Fc : R.complex.facets) :
    R.vertexTranslateEquiv hR g '' Fc.val =
      (R.facetTranslateOrderIso hR g Fc).val :=
  R.complex.facetOrderVertexEquiv_image R.complex _ Fc

/-- The exact original-action comparison in the definition of a polysimplicial action. -/
theorem vertexTranslateEquiv_image_iff (hR : R.IsFaceCompatible)
    (g : rationalPoints G) (Fc Fc' : R.complex.facets) :
    Fc'.val = R.vertexTranslateEquiv hR g '' Fc.val ↔
      (R.realize Fc').val =
        (fun y : B.ReducedBuilding => g • y) '' (R.realize Fc).val := by
  rw [R.vertexTranslateEquiv_image]
  constructor
  · intro h
    have H : Fc' = R.facetTranslateOrderIso hR g Fc := Subtype.ext h
    rw [H, R.realize_facetTranslateOrderIso, B.facetTranslateEquiv_val]
    rfl
  · intro h
    have H : R.realize Fc' = B.facetTranslateEquiv g (R.realize Fc) :=
      Subtype.ext h
    exact congrArg Subtype.val (R.realize.injective
      (H.trans (R.realize_facetTranslateOrderIso hR g Fc).symm))

/-- Any vertex permutation with the exact original-action comparison is the recovered one. -/
theorem vertexTranslateEquiv_unique (hR : R.IsFaceCompatible)
    (g : rationalPoints G) (e : Equiv.Perm (∀ i, R.V i))
    (he : ∀ Fc Fc' : R.complex.facets, Fc'.val = e '' Fc.val ↔
      (R.realize Fc').val =
        (fun y : B.ReducedBuilding => g • y) '' (R.realize Fc).val) :
    e = R.vertexTranslateEquiv hR g := by
  apply R.complex.facetOrderVertexEquiv_unique
  intro Fc
  apply Eq.symm
  apply (he Fc (R.facetTranslateOrderIso hR g Fc)).mpr
  rw [R.realize_facetTranslateOrderIso, B.facetTranslateEquiv_val]
  rfl

@[simp] theorem vertexTranslateEquiv_one (hR : R.IsFaceCompatible) :
    R.vertexTranslateEquiv hR 1 = 1 := by
  symm
  apply R.complex.facetOrderVertexEquiv_unique
  intro Fc
  change (fun x => x) '' Fc.val = (R.facetTranslateOrderIso hR 1 Fc).val
  rw [R.facetTranslateOrderIso_one]
  exact Set.image_id _

theorem vertexTranslateEquiv_mul (hR : R.IsFaceCompatible)
    (g h : rationalPoints G) :
    R.vertexTranslateEquiv hR (g * h) =
      R.vertexTranslateEquiv hR g * R.vertexTranslateEquiv hR h := by
  symm
  apply R.complex.facetOrderVertexEquiv_unique
  intro Fc
  change (fun x => R.vertexTranslateEquiv hR g (R.vertexTranslateEquiv hR h x)) ''
    Fc.val = (R.facetTranslateOrderIso hR (g * h) Fc).val
  rw [← Set.image_image, R.vertexTranslateEquiv_image,
    R.vertexTranslateEquiv_image, R.facetTranslateOrderIso_mul]

/-- The reconstructed vertex permutations form a group action, with no global instance. -/
def vertexActionHom (hR : R.IsFaceCompatible) :
    rationalPoints G →* Equiv.Perm (∀ i, R.V i) where
  toFun := R.vertexTranslateEquiv hR
  map_one' := R.vertexTranslateEquiv_one hR
  map_mul' := R.vertexTranslateEquiv_mul hR

@[simp] theorem vertexTranslateEquiv_inv (hR : R.IsFaceCompatible)
    (g : rationalPoints G) :
    R.vertexTranslateEquiv hR g⁻¹ = (R.vertexTranslateEquiv hR g).symm :=
  map_inv (R.vertexActionHom hR) g

/-- For this canonical vertex action the remaining condition is precisely factor compatibility. -/
theorem isPolysimplicialAction_iff_vertexTranslateEquiv (hR : R.IsFaceCompatible) :
    R.IsPolysimplicialAction ↔
      ∀ g : rationalPoints G,
        AbstractBuilding.IsPolysimplicialAutomorphism R.complex
          (R.vertexTranslateEquiv hR g) := by
  constructor
  · intro h g
    obtain ⟨e, he, himage⟩ := h g
    have H := R.vertexTranslateEquiv_unique hR g e himage
    rwa [H] at he
  · intro h g
    exact ⟨R.vertexTranslateEquiv hR g, h g,
      R.vertexTranslateEquiv_image_iff hR g⟩

end Langlands.Geometry.Building.ValuationBuildingData.PolysimplicialRealization
