import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality

/-! # The zero group acts without inversions on facets over the maximal unramified field

For a nonarchimedean local field `F`, its maximal unramified extension
`K = inertiaFixedField F`, supplied building data `C` of a `K`-group `H` and a supplied
datum `E` computing `H(K)^0`, an element of `E.zeroPoints` cannot move a point of the
apartment of `C` to a different point of the same apartment facet (KP 4.1.12(1),
Proposition 7.6.4(1), Axiom 4.1.9). The statement is unproved here. The module also proves
that the statement gives the facet form of KP 4.1.12(1): an element of `E.zeroPoints`
mapping a facet of the reduced building of `C` into itself fixes that facet pointwise.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace MaximalUnramified

/-- **The zero group acts without inversions on facets over `K`** (Kaletha–Prasad
4.1.12(1), Proposition 7.6.4(1) and Remark 7.6.5 over the maximal unramified extension;
Axiom 4.1.9). Let `F` be a nonarchimedean local field, `K = inertiaFixedField F`, `H` a
`K`-group, `C` supplied building data of `H` for the normalized valuation of `K` and `E`
any datum computing `H(K)^0` as `E.zeroPoints`. If `x` and `y` are points of the apartment
of `C` with `y` in the facet of `x` for the affine roots of `C`, and `g ∈ H(K)^0` maps the
image of `x` in the reduced building of `C` to the image of `y`, then `y = x`. -/
def ZeroFacetNoInversionsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (C : BuildingData F H) (E : UnramifiedZeroDatum F H)
    (x y : C.Apartment) (g : rationalPoints H),
    y ∈ AffineRootSystem.facet C.affineRoots x →
    g ∈ E.zeroPoints →
    g • C.apartmentMap x = C.apartmentMap y →
    y = x

namespace ZeroFacetNoInversionsStatement

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom H.X.hom]

/-- Under the statement, an element of `H(K)^0` that maps the image of an apartment point
into the image of its own apartment facet fixes that image. -/
theorem smul_apartmentMap_eq (h : ZeroFacetNoInversionsStatement.{u})
    (C : BuildingData F H) (E : UnramifiedZeroDatum F H) {x y : C.Apartment}
    {g : rationalPoints H} (hy : y ∈ AffineRootSystem.facet C.affineRoots x)
    (hg : g ∈ E.zeroPoints) (hgx : g • C.apartmentMap x = C.apartmentMap y) :
    g • C.apartmentMap x = C.apartmentMap x := by
  rw [hgx, h F H C E x y g hy hg hgx]

/-- **Facet stabilizers in `H(K)^0` are pointwise fixers** (the facet form of KP
4.1.12(1) over `K`). Under the statement, an element of `E.zeroPoints` mapping a facet `Y`
of the reduced building of `C` into itself fixes `Y` pointwise. The proof uses that
`E.zeroPoints` is normal in `H(K)`, since it contains `H(K)^♮`. -/
theorem mem_pointwiseFixer_of_isFacet (h : ZeroFacetNoInversionsStatement.{u})
    (C : BuildingData F H) (E : UnramifiedZeroDatum F H) {Y : Set C.ReducedBuilding}
    (hY : C.IsFacet Y) {g : rationalPoints H} (hg : g ∈ E.zeroPoints)
    (hgY : (g • ·) '' Y ⊆ Y) : g ∈ C.pointwiseFixer Y := by
  obtain ⟨k, Fa, ⟨z, rfl⟩, rfl⟩ := hY
  rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x', hx', hx'eq⟩ := hgY ⟨k • C.apartmentMap x, ⟨x, hx, rfl⟩, rfl⟩
  change k • C.apartmentMap x' = g • k • C.apartmentMap x at hx'eq
  have hN : E.zeroPoints.Normal :=
    normal_of_simplyConnectedImage_le E.isSimplyConnectedDerivedCover
      E.simplyConnectedImage_le_zeroPoints
  have hconj : k⁻¹ * g * k ∈ E.zeroPoints := by
    simpa only [inv_inv] using hN.conj_mem g hg k⁻¹
  have hmem : x' ∈ AffineRootSystem.facet C.affineRoots x := by
    rw [AffineRootSystem.facet_eq_of_mem hx]
    exact hx'
  have hmove : (k⁻¹ * g * k) • C.apartmentMap x = C.apartmentMap x' := by
    rw [mul_smul, mul_smul, ← hx'eq, inv_smul_smul]
  have hxx : x' = x := h F H C E x x' (k⁻¹ * g * k) hmem hconj hmove
  show g • k • C.apartmentMap x = k • C.apartmentMap x
  rw [← hx'eq, hxx]

end ZeroFacetNoInversionsStatement

end MaximalUnramified

end Langlands.Geometry.Building
