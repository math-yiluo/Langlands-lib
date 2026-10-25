import Langlands.GroupScheme.HomConjugacy
import Langlands.Shimura.Unitary.CocharacterEmbeddingWeights
import Langlands.Shimura.Unitary.DiagonalCocharacters

set_option maxHeartbeats 20000

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj Classical

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation after a group-scheme isomorphism agrees with its induced point map. -/
theorem affineCocharacterValue_comp_iso {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] (G : GroupScheme (Spec (CommRingCat.of R)))
    (H : GroupScheme (Spec (CommRingCat.of S)))
    (e : H ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj G)
    (χ : (Gm (Spec (CommRingCat.of S))).toGrp ⟶ H) (u : Sˣ) :
    G.affineCocharacterValue (χ ≫ e.hom) u =
      ((((yonedaGrp.mapIso e).app (op (Over.mk (𝟙 _)))).groupIsoToMulEquiv).trans
        (baseChangeBasePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap R S))) G))
          ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of S)))).symm u ≫ χ.hom.hom) := by
  exact congrArg (baseChangeBasePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap R S))) G)
    (Category.assoc ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of S)))).symm u)
      χ.hom.hom e.hom.hom.hom).symm

end Langlands.GroupScheme

namespace Langlands.Shimura.CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- Inner conjugacy of actual complex Harris scheme cocharacters. -/
abbrev ComplexCocharacterConjugate
    (χ ψ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) : Prop := GroupScheme.HomConjugate χ ψ

omit [IsScalarTower E K A] in
/-- Affine evaluation is evaluation at the identity test followed by the point comparison. -/
theorem complexCocharacterValue_eq_points
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (u : ℂˣ) :
    D.complexCocharacterValue χ u = D.complexRationalPointsEquiv
      ((GroupScheme.Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of ℂ)))).symm u ≫
        χ.hom.hom) :=
  GroupScheme.affineCocharacterValue_comp_iso D.rationalGroupScheme
    D.complexRationalGroupScheme D.complexDirectGroupSchemeIso χ u


omit [IsScalarTower E K A] in
/-- An actual inner automorphism evaluates as conjugation by the corresponding rational-model point. -/
theorem complexCocharacterValue_inner
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ D.complexRationalGroupScheme.X)
    (u : ℂˣ) :
    D.complexCocharacterValue (χ ≫ (GroupScheme.innerIso D.complexRationalGroupScheme g).hom) u =
      D.complexRationalPointsEquiv g * D.complexCocharacterValue χ u *
        (D.complexRationalPointsEquiv g)⁻¹ := by
  rw [D.complexCocharacterValue_eq_points, Grp.comp_hom_hom, ← Category.assoc,
    GroupScheme.comp_innerIso_hom, GroupScheme.constantPoint_self,
    map_mul, map_mul, map_inv, ← D.complexCocharacterValue_eq_points]

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E K Φ)

/-- Actual scheme conjugacy preserves the inverse-weight rank at every CM embedding. -/
theorem finrank_complexCocharacterWeightSpace_of_conjugate
    {χ ψ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme}
    (h : D.ComplexCocharacterConjugate χ ψ) (i : K →+* ℂ) :
    Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ χ i) =
      Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ ψ i) := by
  obtain ⟨g, rfl⟩ := h
  have hf := funext (D.complexCocharacterValue_inner χ g)
  unfold complexCocharacterWeightSpace
  rw [hf]
  exact (D.finrank_complexEmbeddingWeightSpace_conj C hΦ
    (D.complexCocharacterValue χ) i (D.complexRationalPointsEquiv g)).symm

/-- The general scheme-conjugacy relation specializes to the existing diagonal classification. -/
theorem complexCocharacterConjugate_diagonal_iff
    (p q : (E →+* ℝ) → Fin n → Prop) :
    D.ComplexCocharacterConjugate (D.diagonalCocharacter C p) (D.diagonalCocharacter C q) ↔
      ∀ τ, (Finset.univ.filter (p τ)).card = (Finset.univ.filter (q τ)).card :=
  D.diagonalCocharacterConjugate_iff_card_eq C p q

end Langlands.Shimura.CentralSimpleUnitaryData
