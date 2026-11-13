import Langlands.Geometry.Building.IntegerOmegaApartmentUniqueness
import Langlands.Geometry.Building.IntegerValuationBuildingBasedTransport
import Langlands.Geometry.Building.CrossTorusBuildingComparison
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof

/-! # Comparing supplied integer-valued building data over an arbitrary field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

open DatumTransport

namespace IntegerValuation

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {D : KPApartmentData i (order v)} {E : KPApartmentData j (order v)}
  {C : CentralizerDatum i} {C' : CentralizerDatum j}

/-- Full V 6 identifies transported data with separately supplied target data.
No common valuation family has to be supplied. -/
theorem IsOmegaCompatible.transport_eq_of_isMaximalSplitTorus
    (hD : IsOmegaCompatible v D C) (hE : IsOmegaCompatible v E C')
    (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (hH : IsConnectedReductive H) (hj : IsMaximalSplitTorus j) :
    D.transport e f h = E :=
  (hD.transport_basedIso v C C' e f h).eq_of_isMaximalSplitTorus hE hH hj

/-- Every transported source family lies in the supplied target class. -/
theorem IsOmegaCompatible.transport_mem_of_isMaximalSplitTorus
    (hD : IsOmegaCompatible v D C) (hE : IsOmegaCompatible v E C')
    (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (hH : IsConnectedReductive H) (hj : IsMaximalSplitTorus j)
    (x : D.Apartment) :
    RootFunctionFamily.transportEquiv e f x.val ∈ E.carrier := by
  rw [← hD.transport_eq_of_isMaximalSplitTorus hE e f h hH hj]
  exact ⟨x.val, x.mem, rfl⟩

end IntegerValuation

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (B : IntegerValuationBuildingData v G) (B' : IntegerValuationBuildingData v H)
  (e : B.S ≅ B'.S) (f : G ≅ H)
  (h : B.i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ B'.i)

/-- The source class transported through the given based isomorphism is the
class of the supplied target building datum. -/
theorem transport_apartment_eq :
    B.apartment.transport e f h = B'.apartment :=
  B.isOmegaCompatible.transport_eq_of_isMaximalSplitTorus B'.isOmegaCompatible e f h
    B'.isConnectedReductive B'.isMaximalSplitTorus

private def comparisonPoint : B.Apartment := Classical.choice inferInstance

include h in
private theorem comparisonPoint_mem :
    RootFunctionFamily.transportEquiv e f (comparisonPoint B).val ∈ B'.apartment.carrier :=
  B.isOmegaCompatible.transport_mem_of_isMaximalSplitTorus B'.isOmegaCompatible e f h
    B'.isConnectedReductive B'.isMaximalSplitTorus (comparisonPoint B)

/-- The affine comparison to the independently supplied target apartment. -/
def apartmentComparison : B.Apartment ≃ᵃ[ℝ] B'.Apartment :=
  B.apartment.apartmentTransportAffineEquivOfMem e f h B'.apartment
    (comparisonPoint B) (comparisonPoint_mem B B' e f h)

/-- The quotient comparison to the independently supplied target building. -/
def buildingComparison : B.ReducedBuilding ≃ B'.ReducedBuilding :=
  B.apartment.reducedBuildingTransportEquivOfMem e f h B'.apartment
    (comparisonPoint B) (comparisonPoint_mem B B' e f h)

/-- The actual canonical apartment charts commute with the comparisons. -/
theorem buildingComparison_apartmentMap (x : B.Apartment) :
    B.buildingComparison B' e f h (B.apartmentMap x) =
      B'.apartmentMap (B.apartmentComparison B' e f h x) :=
  B.apartment.reducedBuildingTransportEquivOfMem_apartmentMap e f h B'.apartment
    (comparisonPoint B) (comparisonPoint_mem B B' e f h) x

/-- The comparison intertwines the actual ambient rational-point actions. -/
theorem buildingComparison_smul (g : rationalPoints G) (y : B.ReducedBuilding) :
    B.buildingComparison B' e f h (g • y) =
      rationalPoints.map f.hom g • B.buildingComparison B' e f h y :=
  B.apartment.reducedBuildingTransportEquivOfMem_smul e f h B'.apartment
    (comparisonPoint B) (comparisonPoint_mem B B' e f h) g y

/-- Full fixers have the expected images under the ambient isomorphism. -/
theorem map_fixer_buildingComparison (y : B.ReducedBuilding) :
    (B.fixer y).map (rationalPoints.map f.hom) =
      B'.fixer (B.buildingComparison B' e f h y) :=
  B.apartment.map_reducedFixer_comparison e f h B'.apartment
    (comparisonPoint B) (comparisonPoint_mem B B' e f h) y

/-- The actual character-kernel point stabilizers are also transported. -/
theorem map_oneStabilizer_buildingComparison (y : B.ReducedBuilding) :
    (B.oneStabilizer y).map (rationalPoints.map f.hom) =
      B'.oneStabilizer (B.buildingComparison B' e f h y) := by
  ext z
  obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective z
  rw [pointsEquiv_apply, mem_map_iff, B.mem_oneStabilizer, B'.mem_oneStabilizer,
    mem_characterValuationKernel_mapIso_iff, ← B.buildingComparison_smul]
  exact and_congr_right fun _ => (B.buildingComparison B' e f h).injective.eq_iff.symm

/-- The comparison carries precisely the source affine roots onto the target roots. -/
theorem transportedRoots_apartmentComparison :
    AffineRootSystem.transportedRoots (B.apartmentComparison B' e f h) B.affineRoots =
      B'.affineRoots :=
  B.apartment.transported_affineRoots_of_mem e f h B'.apartment
    (comparisonPoint B) (comparisonPoint_mem B B' e f h)

/-- Special points are preserved and reflected on the supplied quotients. -/
theorem isSpecialPoint_buildingComparison_iff (y : B.ReducedBuilding) :
    B'.IsSpecialPoint (B.buildingComparison B' e f h y) ↔ B.IsSpecialPoint y := by
  have hspecial (x : B.Apartment) :
      AffineRootSystem.IsSpecialPoint B'.affineRoots (B.apartmentComparison B' e f h x) ↔
        AffineRootSystem.IsSpecialPoint B.affineRoots x := by
    rw [← B.transportedRoots_apartmentComparison B' e f h]
    exact AffineRootSystem.isSpecialPoint_transportedRoots_iff _ _ _
  constructor
  · rintro ⟨g, x, hxy, hx⟩
    obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective g
    obtain ⟨x, rfl⟩ := (B.apartmentComparison B' e f h).surjective x
    refine ⟨g, x, (B.buildingComparison B' e f h).injective ?_, (hspecial x).mp hx⟩
    rw [B.buildingComparison_smul, B.buildingComparison_apartmentMap]
    exact hxy
  · rintro ⟨g, x, rfl, hx⟩
    exact ⟨rationalPoints.map f.hom g, B.apartmentComparison B' e f h x,
      by rw [B.buildingComparison_smul, B.buildingComparison_apartmentMap],
      (hspecial x).mpr hx⟩

end IntegerValuationBuildingData

/-- Any two supplied integer-valued building data for the same connected
reductive group have a same-action quotient equivalence preserving full fixers,
character-kernel stabilizers and special points. -/
def IntegerValuationBuildingSameGroupComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B B' : IntegerValuationBuildingData v G),
    ∃ Φ : B.ReducedBuilding ≃ B'.ReducedBuilding,
      (∀ (g : rationalPoints G) (y : B.ReducedBuilding), Φ (g • y) = g • Φ y) ∧
      (∀ y, B'.fixer (Φ y) = B.fixer y) ∧
      (∀ y, B'.oneStabilizer (Φ y) = B.oneStabilizer y) ∧
      (∀ y, B'.IsSpecialPoint (Φ y) ↔ B.IsSpecialPoint y)

/-- Conjugate the actual maximal split tori, identify full V 6 classes, then
cancel the inner twisting on the target quotient. -/
theorem integerValuationBuildingSameGroupComparison :
    IntegerValuationBuildingSameGroupComparisonStatement.{u} := by
  intro k _ v G _ B B'
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy k G B.isConnectedReductive).1
    B.S B'.S B.i B'.i B.isMaximalSplitTorus B'.isMaximalSplitTorus
  let σ : B.S ≅ B'.S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hσ : B.i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ B'.i := he
  let c := B.buildingComparison B' σ (G.innerIso g) hσ
  let Φ : B.ReducedBuilding ≃ B'.ReducedBuilding := c.trans (MulAction.toPerm g⁻¹)
  have hΦ (a : rationalPoints G) (y : B.ReducedBuilding) : Φ (a • y) = a • Φ y := by
    change g⁻¹ • c (a • y) = a • (g⁻¹ • c y)
    rw [show c (a • y) = rationalPoints.map (G.innerIso g).hom a • c y from
      B.buildingComparison_smul B' σ (G.innerIso g) hσ a y]
    rw [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self, mul_smul,
      mul_smul, inv_smul_smul, ← mul_smul]
  refine ⟨Φ, hΦ, ?_, ?_, ?_⟩
  · intro y
    ext a
    rw [B'.mem_fixer, B.mem_fixer, ← hΦ]
    exact Φ.injective.eq_iff
  · intro y
    ext a
    rw [B'.mem_oneStabilizer, B.mem_oneStabilizer, ← hΦ]
    exact and_congr_right fun _ => Φ.injective.eq_iff
  · intro y
    have hspecial := B.isSpecialPoint_buildingComparison_iff B' σ (G.innerIso g) hσ y
    change B'.IsSpecialPoint (g⁻¹ • c y) ↔ B.IsSpecialPoint y
    constructor
    · intro hy
      have hz := KPApartmentData.IsSpecialBuildingPoint.smul B'.apartment hy g
      rw [smul_inv_smul] at hz
      exact hspecial.mp hz
    · intro hy
      exact KPApartmentData.IsSpecialBuildingPoint.smul B'.apartment (hspecial.mpr hy) g⁻¹

end Langlands.Geometry.Building
