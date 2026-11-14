import Langlands.GroupScheme.Reductive.LinearQuotientAffineStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.HomogeneousQuotientProof

/-! # Actual affine linear homogeneous spaces from linear quotient affineness -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The linear quotient affineness input supplies a closed linear embedding and an
actual affine homogeneous quotient for each connected reductive group. -/
theorem exists_affine_linearQuotient_of_reductiveLinearQuotientAffine
    (hA : ReductiveLinearQuotientAffineStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      IsClosedSubgroup ρ ∧
        ∃ (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient ρ),
          IsAffineHom Q.scheme.hom := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  let : Smooth (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    GeneralLinear.smoothStatement (Fin N) _
  let : IsAffineHom (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme (Fin N) (CommRingCat.of k)
  obtain ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)) G ρ hρ hG.smooth
  let D : HomogeneousQuotientFromEmbedding.HomogeneousQuotient ρ :=
    ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩
  exact ⟨N, ρ, hρ, D, hA k G hG N ρ hρ D⟩

end Langlands.GroupScheme
