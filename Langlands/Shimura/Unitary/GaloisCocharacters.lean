import Langlands.GroupScheme.CocharacterTransport
import Langlands.Shimura.Unitary.ComplexCocharacter

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura

/-- The usual complex point of the rational base. -/
abbrev rationalComplexBaseMap : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℚ) :=
  AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℂ

/-- The real-to-complex scalar tower gives the same map to the rational base. -/
theorem rationalComplexBaseMap_tower :
    DeligneTorus.complexBaseMap ≫ AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ =
      rationalComplexBaseMap := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) = _
  rw [← Spec.map_comp]
  congr 1

/-- The geometric base map associated to a rational coefficient automorphism. -/
def complexGaloisBaseMap (s : ℂ ≃ₐ[ℚ] ℂ) :
    Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom s.toRingHom)

/-- The coefficient automorphism acts over the rational base. -/
theorem complexGaloisBaseMap_over (s : ℂ ≃ₐ[ℚ] ℂ) :
    complexGaloisBaseMap s ≫ rationalComplexBaseMap = rationalComplexBaseMap := by
  change Spec.map (CommRingCat.ofHom s.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact s.toAlgHom.comp_algebraMap

@[simp] theorem complexGaloisBaseMap_one :
    complexGaloisBaseMap (1 : ℂ ≃ₐ[ℚ] ℂ) = 𝟙 _ := by
  change Spec.map (𝟙 (CommRingCat.of ℂ)) = _
  exact Spec.map_id _

/-- Spectrum reverses coefficient maps, giving this geometric composition convention. -/
theorem complexGaloisBaseMap_mul (s t : ℂ ≃ₐ[ℚ] ℂ) :
    complexGaloisBaseMap (s * t) = complexGaloisBaseMap s ≫ complexGaloisBaseMap t := by
  unfold complexGaloisBaseMap
  rw [← Spec.map_comp]
  rfl

namespace CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- The actual iterated complex pullback is canonically isomorphic to direct rational pullback. -/
def complexDirectGroupSchemeIso :
    D.complexRationalGroupScheme ≅ D.rationalBaseChange rationalComplexBaseMap :=
  (GroupScheme.baseChangeCompIso (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ)
    DeligneTorus.complexBaseMap D.rationalGroupScheme).symm ≪≫
      eqToIso (congrArg (fun b => D.rationalBaseChange b) rationalComplexBaseMap_tower)

/-- Actual Galois transport of a scheme cocharacter of the iterated complex Harris group. -/
def galoisCocharacter (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme) :
    (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme :=
  GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
      (complexGaloisBaseMap_over s) D.rationalGroupScheme
      (χ ≫ D.complexDirectGroupSchemeIso.hom) ≫ D.complexDirectGroupSchemeIso.inv

omit [IsScalarTower E K A] in
/-- Transport commutes with the canonical comparison to the direct rational pullback. -/
theorem galoisCocharacter_comparison (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme) :
    D.galoisCocharacter s χ ≫ D.complexDirectGroupSchemeIso.hom =
      GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
        (complexGaloisBaseMap_over s) D.rationalGroupScheme
        (χ ≫ D.complexDirectGroupSchemeIso.hom) := by
  simp [galoisCocharacter]

omit [IsScalarTower E K A] in
@[simp] theorem galoisCocharacter_one
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme) :
    D.galoisCocharacter 1 χ = χ := by
  unfold galoisCocharacter
  simp only [complexGaloisBaseMap_one, GroupScheme.transportCocharacter_id]
  simp

omit [IsScalarTower E K A] in
/-- Galois transport is a left action on actual scheme cocharacters. -/
theorem galoisCocharacter_mul (s t : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme) :
    D.galoisCocharacter (s * t) χ = D.galoisCocharacter s (D.galoisCocharacter t χ) := by
  unfold galoisCocharacter
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [GroupScheme.transportCocharacter_comp]
  simp only [complexGaloisBaseMap_mul]

/-- Each Galois automorphism permutes actual cocharacters, with inverse transport by s inverse. -/
def galoisCocharacterEquiv (s : ℂ ≃ₐ[ℚ] ℂ) : Equiv.Perm
    ((GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme) where
  toFun := D.galoisCocharacter s
  invFun := D.galoisCocharacter s⁻¹
  left_inv χ := by rw [← D.galoisCocharacter_mul, inv_mul_cancel, D.galoisCocharacter_one]
  right_inv χ := by rw [← D.galoisCocharacter_mul, mul_inv_cancel, D.galoisCocharacter_one]

/-- The Galois action on actual Harris scheme cocharacters, as a permutation representation. -/
def galoisCocharacterAction : (ℂ ≃ₐ[ℚ] ℂ) →* Equiv.Perm
    ((GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme) where
  toFun := D.galoisCocharacterEquiv
  map_one' := by
    apply Equiv.ext
    exact D.galoisCocharacter_one
  map_mul' s t := by
    apply Equiv.ext
    exact D.galoisCocharacter_mul s t

/-- The complex points of the iterated pullback are actual rational-group complex points. -/
def complexRationalPointsEquiv :
    (Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ D.complexRationalGroupScheme.X) ≃*
      ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶ D.rationalGroupScheme.X) :=
  (((yonedaGrp.mapIso D.complexDirectGroupSchemeIso).app
    (op (Over.mk (𝟙 _)))).groupIsoToMulEquiv).trans
      (GroupScheme.baseChangeBasePointsEquiv rationalComplexBaseMap D.rationalGroupScheme)

end CentralSimpleUnitaryData
end Langlands.Shimura
