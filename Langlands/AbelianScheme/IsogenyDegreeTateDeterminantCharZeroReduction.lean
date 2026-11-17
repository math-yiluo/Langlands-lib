import Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialStatement
import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormStatement
import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantCharZeroStatement
import Langlands.AbelianScheme.StructureCohomologyVanishing
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceReduction
import Langlands.Algebra.DegreeDeterminant.DetComparison

/-! # The characteristic-zero degree statement from its two inputs

`IsogenyDegreeTateDeterminantCharZeroReductionStatement` says that the line form of Milne's
Proposition 12.4 (`EndomorphismDegreeLinePolynomialStatement`) and the `p`-adic comparison
in Milne's proof of Proposition 12.9 (`IsogenyDegreeTateDeterminantNormStatement`) imply the
characteristic-zero degree statement `IsogenyDegreeTateDeterminantCharZeroStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Rosati.MumfordTraceReduction Langlands.Algebra.DegreeDeterminant

/-- The line form of Proposition 12.4 and the `p`-adic comparison of Proposition 12.9 imply
the characteristic-zero degree statement, at the same universe. -/
def IsogenyDegreeTateDeterminantCharZeroReductionStatement : Prop :=
  EndomorphismDegreeLinePolynomialStatement.{u} →
    IsogenyDegreeTateDeterminantNormStatement.{u} →
      IsogenyDegreeTateDeterminantCharZeroStatement.{u}

/-- Proof of the reduction: the degree data on `End A` with the matrix of the rational
`p`-adic Tate map satisfy `DegreeData`, so `DegreeData.det_eq` applies. -/
theorem isogenyDegreeTateDeterminantCharZeroReduction :
    IsogenyDegreeTateDeterminantCharZeroReductionStatement.{u} := by
  intro hG1 hG23 k _ _ _ A p _ α
  obtain ⟨g, hA⟩ := exists_hasRelativeDimension_of_field A
  have hp : IsUnit ((p : ℕ) : Γ(Scheme.Spec.obj (Opposite.op (CommRingCat.of k)), ⊤)) := by
    simpa using isUnit_intCast_global (k := k) (p : ℤ)
      (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  obtain ⟨-, hfin, hrank⟩ := Tate.PrimeAdic.geometricPrimeAdicRank _ A g hA p hp k (𝟙 _)
  let b := Module.finBasisOfFinrankEq ℚ_[p] _ hrank
  let Vp : CategoryTheory.End A →+* Module.End ℚ_[p]
      (Tate.PrimeAdic.Rational A (Over.mk (𝟙 (Scheme.Spec.obj
        (Opposite.op (CommRingCat.of k))))) p) :=
    (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A).toRingHom.comp (endToEnd0 A)
  have hVp : ∀ f : A ⟶ A, Vp f = Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p f :=
    fun f => rationalEndAction_homToHom0 A p f
  let ρ : CategoryTheory.End A →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p] :=
    (LinearMap.toMatrixAlgEquiv b).toRingHom.comp Vp
  have hdet : ∀ f : A ⟶ A,
      (ρ f).det = LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p f) := by
    intro f
    rw [← hVp f]
    exact LinearMap.det_toMatrix b (Vp f)
  obtain ⟨δ, hδiso, hδline⟩ := hG1 k A g hA
  obtain ⟨y₀⟩ := nonempty_left A
  have hD : DegreeData ρ δ (fun β : CategoryTheory.End A => IsIsogeny (β : A ⟶ A)) :=
    { line := fun φ ψ => hδline φ ψ
      mul := by
        intro β γ hβ hγ
        change δ (γ ≫ β) = δ β * δ γ
        rw [hδiso _ (hγ.comp hβ) y₀, hδiso β hβ y₀, hδiso γ hγ y₀,
          finrank_comp_of_isIsogeny γ β hγ hβ ((hom γ).finrank y₀)
            (fun y => finrank_eq_of_isIsogeny γ hγ y y₀) y₀ y₀]
        push_cast
        ring
      norm := by
        intro β hβ
        rw [hdet, hδiso β hβ y₀, ← (hG23 k A p β).1 hβ y₀]
        push_cast
        rfl
      zero := by
        intro β hβ
        rw [hdet]
        exact (hG23 k A p β).2 hβ }
  have key := hD.det_eq (show CategoryTheory.End A from α)
  rw [hdet] at key
  refine ⟨fun hiso y => ?_, fun hniso => (hG23 k A p α).2 hniso⟩
  rw [← key, hδiso α hiso y]
  push_cast
  rfl

end Langlands.AbelianScheme
