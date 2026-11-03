import Langlands.AbelianScheme.FieldMultiplicationFiniteEtale
import Langlands.AbelianScheme.FiberwiseIsogeny

/-! # Multiplication by an invertible index over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} (A : AbelianScheme S) (n : ℕ)

/-- Multiplication by an index invertible in global sections is an isogeny. -/
theorem multiplication_isIsogeny_of_isUnit (hn : IsUnit (n : Γ(S, ⊤))) :
    GroupScheme.IsIsogeny (GroupScheme.multiplication A.toGrp (n : ℤ)) := by
  apply GroupScheme.fiberwiseIsogeny S A.toGrp A.toGrp
    A.smooth A.smooth A.proper A.proper
  intro s
  let f := S.fromSpecResidueField s
  have hunit : IsUnit (n : S.residueField s) := by
    simpa using (hn.map f.appTop.hom).map (Scheme.ΓSpecIso (S.residueField s)).hom.hom
  rw [GroupScheme.multiplication_baseChange]
  exact multiplication_isIsogeny_of_ne_zero ((baseChange f).obj A) n hunit.ne_zero

/-- Multiplication by an invertible natural index, bundled with its proved isogeny property. -/
def invertibleMultiplicationIsogeny (hn : IsUnit (n : Γ(S, ⊤))) :
    {f : A ⟶ A // IsIsogeny f} :=
  ⟨n • 𝟙 A, multiplication_isIsogeny_of_isUnit A n hn⟩

/-- The bundle retains the actual integer-multiplication homomorphism. -/
@[simp] theorem invertibleMultiplicationIsogeny_val (hn : IsUnit (n : Γ(S, ⊤))) :
    (invertibleMultiplicationIsogeny A n hn).val = n • 𝟙 A := rfl

end Langlands.AbelianScheme
