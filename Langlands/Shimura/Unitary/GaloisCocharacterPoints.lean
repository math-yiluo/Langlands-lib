import Langlands.GroupScheme.CocharacterAffineTransport
import Langlands.Shimura.Unitary.GaloisCocharacters
import Langlands.Shimura.Unitary.GaloisPoints

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura

/-- Evaluate in the rational affine point model using the named complex base map. -/
def rationalComplexCocharacterValue
    (G : GroupScheme (Spec (CommRingCat.of ℚ)))
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      (Over.pullback rationalComplexBaseMap).mapGrp.obj G) (u : ℂˣ) :
    (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶ G.X :=
  G.affineCocharacterValue χ u

/-- The affine transport formula at the named rational-to-complex base map. -/
theorem rationalComplexCocharacterValue_transport
    (G : GroupScheme (Spec (CommRingCat.of ℚ))) (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      (Over.pullback rationalComplexBaseMap).mapGrp.obj G) (u : ℂˣ) :
    rationalComplexCocharacterValue G
      (GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
        (complexGaloisBaseMap_over s) G χ) u =
      G.affinePointAut s (rationalComplexCocharacterValue G χ (Units.map s.symm.toMonoidHom u)) :=
  GroupScheme.affineCocharacterValue_transport (R := ℚ) (S := ℂ) G s χ
    (complexGaloisBaseMap_over s) u

end Langlands.Shimura

namespace Langlands.Shimura.CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- Evaluate a cocharacter in the direct rational base-change model. -/
def directComplexCocharacterValue
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.rationalBaseChange rationalComplexBaseMap) (u : ℂˣ) :
    (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶ D.rationalGroupScheme.X :=
  rationalComplexCocharacterValue D.rationalGroupScheme χ u

omit [IsScalarTower E K A] in
/-- The affine transport formula in the direct Harris model. -/
theorem directComplexCocharacterValue_transport (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.rationalBaseChange rationalComplexBaseMap) (u : ℂˣ) :
    D.directComplexCocharacterValue
      (GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
        (complexGaloisBaseMap_over s) D.rationalGroupScheme χ) u =
      D.complexPointGaloisAction s
        (D.directComplexCocharacterValue χ (Units.map s.symm.toMonoidHom u)) :=
  rationalComplexCocharacterValue_transport D.rationalGroupScheme s χ u

/-- Evaluate a complex scheme cocharacter using the canonical direct-model comparison. -/
def complexCocharacterValue
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (u : ℂˣ) :
    (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶ D.rationalGroupScheme.X :=
  D.directComplexCocharacterValue (χ ≫ D.complexDirectGroupSchemeIso.hom) u

omit [IsScalarTower E K A] in
/-- Evaluation agrees with evaluation in the direct rational pullback model. -/
theorem complexCocharacterValue_comparison
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (u : ℂˣ) :
    D.complexCocharacterValue χ u =
      D.directComplexCocharacterValue (χ ≫ D.complexDirectGroupSchemeIso.hom) u := rfl

omit [IsScalarTower E K A] in
/-- Transported evaluation agrees with the direct-model transported evaluation. -/
theorem complexCocharacterValue_galois_comparison (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (u : ℂˣ) :
    D.complexCocharacterValue (D.galoisCocharacter s χ) u =
      D.directComplexCocharacterValue
        (GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
          (complexGaloisBaseMap_over s) D.rationalGroupScheme
          (χ ≫ D.complexDirectGroupSchemeIso.hom)) u := by
  exact congrArg
    (fun k : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.rationalBaseChange rationalComplexBaseMap => D.directComplexCocharacterValue k u)
    (D.galoisCocharacter_comparison s χ)

end Langlands.Shimura.CentralSimpleUnitaryData
