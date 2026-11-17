import Langlands.GroupScheme.HomScheme.NormalizerOrbit
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddingAction

/-! # Quasi-affine full-normalizer orbit targets for finite diagonalizable groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddings

variable (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M]

/-- All actual source automorphisms are locally among the constant character
automorphisms, on every relative scheme test. -/
theorem sourceCharacterIso_locallyExhaust [AddMonoid.FG M] :
    LocallyExhaustSourceIsomorphisms (Diagonalizable.groupScheme R M).toGrp
      (sourceCharacterIso R M) := by
  intro T e x
  obtain ⟨W, a, g, ha, hx, he⟩ :=
    Diagonalizable.exists_open_neighborhood_eq_restrictMap_on_test T e x
  exact ⟨W, a, MulOpposite.op (Multiplicative.ofAdd g), ha, hx, he⟩

variable [Fintype M] (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

/-- The finite closed-embedding scheme modulo all character automorphisms
gives an actual quasi-affine target with exactly full normalizer cosets. -/
def normalizerOrbitModel (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    (hi : IsClosedSubgroup i) :
    Σ Y : Over (Spec R), {r : G.X ⟶ Y // Y.left.IsQuasiAffine ∧
      ∀ (T : Over (Spec R)) (g h : T ⟶ G.X),
        g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (torusNormalizer i).carrier T} := by
  let U := embeddingModel R M G
  let : U.scheme.left.IsQuasiAffine := embeddingModel_isQuasiAffine R M G
  let A := characterAction R M G
  let Q := A.quasiAffineQuotient.val
  let Y := U.normalizerOrbitTarget (sourceCharacterIso R M) (sourceCharacterIso_one R M)
    (sourceCharacterIso_mul R M) (sourceCharacterIso_baseChange_injective R M) Q
  let r := U.normalizerOrbitMap (sourceCharacterIso R M) (sourceCharacterIso_one R M)
    (sourceCharacterIso_mul R M) (sourceCharacterIso_baseChange_injective R M) Q i hi
  refine ⟨Y, r, ?_, ?_⟩
  · exact Q.isQuasiAffine
  · exact U.normalizerOrbitMap_fibers (sourceCharacterIso R M) (sourceCharacterIso_one R M)
      (sourceCharacterIso_mul R M) (sourceCharacterIso_baseChange_injective R M)
      Q (sourceCharacterIso_locallyExhaust R M) i hi

end Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddings
