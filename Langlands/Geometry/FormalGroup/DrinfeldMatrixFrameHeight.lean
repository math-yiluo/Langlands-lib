import Langlands.Geometry.FormalGroup.DrinfeldMatrixDegree

/-! # Signed kernel-rank height of the matrix action on the source cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralSimple ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}

namespace SpecialModule.MatrixCoordinates

variable {Φ : SpecialModule K D ι κ} (c : Φ.MatrixCoordinates)

/-- Choose a ranked integral numerator for the actual matrix quasi-isogeny over the frame field. -/
def heightPresentation {q H : ℕ} (hq : 1 < q) (hπ : Irreducible π)
    (hΦ : Φ.formalModule.HasPiHeight π q (H * reducedDegree K D))
    (g : GL (Fin (reducedDegree K D)) K) :
    {P : RationalHom.GlobalHeightPresentation π q (c.quasiIsogeny g).hom.val //
      P.index (H * reducedDegree K D) = (H : ℤ) * (Plancherel.fieldOrderUnits K g.det).toAdd} :=
  let h := (c.quasiIsogeny g).toModuleQuasiIsogeny.exists_globalHeight_of_fieldDegree_zpow
    hπ hq hΦ hΦ.piDivisible ((c.degree_val hπ hΦ.piDivisible g).symm.trans
      (c.degree_eq_zpow (zero_lt_one.trans hq) hπ hΦ g))
  ⟨h.choose, h.choose_spec⟩

end SpecialModule.MatrixCoordinates

namespace DrinfeldFramedAtlas

variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (X : DrinfeldFramedAtlas Φ A) (c : Φ.val.MatrixCoordinates)

/-- Every test of the original source cover sees the same signed determinant height. -/
theorem matrixSource_hasConstantChartHeight (g : GL (Fin (reducedDegree K D)) K) :
    (X.matrixSourceQuasiIsogeny c g).hom.val.HasConstantChartHeight π (Nat.card 𝓀[K])
      ((reducedDegree K D : ℤ) * (Plancherel.fieldOrderUnits K g.det).toAdd) := by
  have hq : 1 < Nat.card 𝓀[K] := LocalField.residueCardinality_gt_one K
  have hΦ : Φ.val.formalModule.HasPiHeight π (Nat.card 𝓀[K])
      (reducedDegree K D * reducedDegree K D) := by
    simpa only [pow_two] using Φ.property.2
  let P := c.heightPresentation hq Φ.property.1 hΦ g
  rw [← P.property]
  exact BasicAtlas.RationalHom.hasConstantChartHeight_ofGlobal (P.val.map X.residueMap)
    (hΦ.map X.residueMap) X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers

/-- In Drinfeld's framing formula the matrix is inverted, so its signed height changes sign. -/
theorem inverseMatrixSource_hasConstantChartHeight (g : GL (Fin (reducedDegree K D)) K) :
    (X.matrixSourceQuasiIsogeny c g⁻¹).hom.val.HasConstantChartHeight π (Nat.card 𝓀[K])
      (-(reducedDegree K D : ℤ) * (Plancherel.fieldOrderUnits K g.det).toAdd) := by
  simpa only [map_inv, toAdd_inv, mul_neg, neg_mul] using
    X.matrixSource_hasConstantChartHeight c g⁻¹

end DrinfeldFramedAtlas

end Langlands.FormalGroup.LocalDivision
