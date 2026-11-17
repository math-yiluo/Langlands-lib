import Langlands.GroupScheme.HomScheme.ClosedEmbeddingModel
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddingLocus
import Langlands.GroupScheme.HomScheme.FibreComparison
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange

/-! # Quasi-affine schemes of embeddings of finite diagonalizable groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.FiniteBialgebraHom

namespace Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Fintype M]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance : Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G) :=
  FiniteDiagonalizable.finitePresentation_hopfAlgebra G

/-- The actual affine Hom parameter algebra for a finite character group. -/
abbrev homAlgebra : Type u :=
  HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R M)

/-- The affine base of the universal Hom family. -/
abbrev homBase : Over (Spec (CommRingCat.of R)) :=
  FiniteSource.specOver R (homAlgebra R M G)

local instance : IsAffine (homBase R M G).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (homAlgebra R M G))))

/-- The universal actual family of homomorphisms `D_R(M) → G`. -/
def universalHom : RelativeHom (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp G
    (homBase R M G) :=
  transport (Diagonalizable.hopfSpecIso (CommRingCat.of R) M).symm
    (FiniteDiagonalizable.coordinateIso G) (FiniteSource.universalFamily R _ _)

/-- Universality includes every scheme test over the original ring. -/
theorem isUniversal_universalHom : IsUniversal (universalHom R M G) :=
  (FiniteSource.isUniversal_universalFamily R _ _).transport _ _

/-- The standard diagonal Hopf source on the parameter scheme is the pulled-back source. -/
def universalSourceIso :
    TorusClosedImmersionLocus.diagonalSource (CommRingCat.of (homAlgebra R M G)) M ≅
      (GroupScheme.baseChange (homBase R M G).hom).obj
        (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp :=
  Diagonalizable.hopfSpecIso (CommRingCat.of (homAlgebra R M G)) M ≪≫
    (Diagonalizable.baseChangeIso (homBase R M G).hom M).symm

/-- The universal family with the literal diagonal Hopf spectrum as source. -/
def diagonalFamily :
    TorusClosedImmersionLocus.diagonalSource (CommRingCat.of (homAlgebra R M G)) M ⟶
      (GroupScheme.baseChange (homBase R M G).hom).obj G :=
  (universalSourceIso R M G).hom ≫ universalHom R M G

local instance : IsAffine ((GroupScheme.baseChange (homBase R M G).hom).obj G).X.left :=
  by
  let : IsAffineHom ((GroupScheme.baseChange (homBase R M G).hom).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom (homBase R M G).hom inferInstance
  exact isAffine_of_isAffineHom ((GroupScheme.baseChange (homBase R M G).hom).obj G).X.hom

/-- The actual scheme representing all closed embeddings of `D_R(M)` into `G`. -/
def embeddingModel : ClosedEmbeddingModel
    (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp G :=
  ClosedEmbeddingModel.ofOpen (universalHom R M G) (isUniversal_universalHom R M G)
    (FiniteDiagonalizableEmbeddingLocus.embeddingOpen (diagonalFamily R M G)) (by
      intro T a
      change _ ↔ IsClosedImmersion (evaluate a (universalHom R M G)).hom.hom.left
      refine (FiniteDiagonalizableEmbeddingLocus.range_subset_embeddingOpen_iff
        (diagonalFamily R M G) a.left).trans ?_
      unfold diagonalFamily
      rw [TorusClosedImmersionLocus.closed_baseChange_precomp_iso_iff]
      exact (isClosedImmersion_evaluate_iff a (universalHom R M G)).symm)

/-- The full closed-embedding parameter scheme is quasi-affine. -/
theorem embeddingModel_isQuasiAffine : (embeddingModel R M G).scheme.left.IsQuasiAffine := by
  change (FiniteDiagonalizableEmbeddingLocus.embeddingOpen
    (diagonalFamily R M G)).toScheme.IsQuasiAffine
  let : LocallyOfFinitePresentation
      ((GroupScheme.baseChange (homBase R M G).hom).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom (homBase R M G).hom inferInstance
  exact FiniteDiagonalizableEmbeddingLocus.embeddingOpen_isQuasiAffine _

end Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddings
