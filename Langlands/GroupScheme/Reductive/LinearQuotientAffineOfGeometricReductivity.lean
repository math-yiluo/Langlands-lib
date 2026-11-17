import Langlands.GroupScheme.Reductive.LinearQuotientAffineStatement
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.HomogeneousQuotientAffineOfGeometricallyReductive

/-! # Linear quotient affineness from the geometric reductivity statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The full geometric-reductivity statement implies the unchanged supplied
linear-quotient affineness statement. -/
theorem reductiveLinearQuotientAffine_of_geometricReductivity
    (hGR : ReductiveGeometricReductivityStatement.{u}) :
    ReductiveLinearQuotientAffineStatement.{u} := by
  intro k _ _ G hG N ρ _ Q
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.left :=
    GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of k)
  have hgeom : IsGeometricallyReductive G :=
    isGeometricallyReductive_of_statement hGR hG.isPseudoReductive
  let : IsAffine Q.scheme.left :=
    Q.isAffine_of_geometricallyReductive hgeom
  exact isAffineHom_of_isAffine Q.scheme.hom

namespace ReductiveLinearQuotientAffine

/-- Assuming the full geometric-reductivity statement, the original supplied
linear quotient is canonically the spectrum of its own global section ring. -/
def affineModelIso
    (hGR : ReductiveGeometricReductivityStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient ρ) :
    Q.scheme.left ≅ Spec Γ(Q.scheme.left, ⊤) := by
  letI : IsAffineHom Q.scheme.hom :=
    reductiveLinearQuotientAffine_of_geometricReductivity hGR k G hG N ρ hρ Q
  letI : IsAffine Q.scheme.left := isAffine_of_isAffineHom Q.scheme.hom
  exact Q.scheme.left.isoSpec

@[simp]
theorem affineModelIso_hom
    (hGR : ReductiveGeometricReductivityStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient ρ) :
    (affineModelIso hGR hG ρ hρ Q).hom = Q.scheme.left.toSpecΓ := rfl

end ReductiveLinearQuotientAffine

end Langlands.GroupScheme
