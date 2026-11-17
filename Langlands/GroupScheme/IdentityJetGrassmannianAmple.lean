import Langlands.GroupScheme.IdentityJetAmpleTransfer
import Langlands.AlgebraicGeometry.Picard.DeterminantBiproduct
import Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminantFrames

/-! # Actual stabilized Grassmannian jets give Lie determinant-dual ampleness -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

open Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.Modules
open Module.Grassmannian.ProjectiveEmbedding

variable {S B : Scheme.{u}}

/-- The genuine actual jet-module stabilization by an actual pulled-back base sheaf. -/
def stabilizedModule (G : GroupScheme S) (n : ℕ) (p : S ⟶ B) (C : B.Modules) : S.Modules :=
  module G n ⊞ (Scheme.Modules.pullback p).obj C

variable (G : GroupScheme S) [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- The actual stabilization of the actual jet module has finite local bases. -/
theorem stabilizedModule_hasFiniteLocalBasis (n : ℕ) (p : S ⟶ B)
    {C : B.Modules} (hC : HasFiniteLocalBasis C) :
    HasFiniteLocalBasis (stabilizedModule G n p C) :=
  (hasFiniteLocalBasis G n).biprod (hC.pullback p)

/-- An actual affine-point Grassmannian comparison for the genuine stabilized
positive-order jet proves ampleness of the actual Lie determinant dual. -/
theorem lieDeterminantDual_isAmple_of_stabilizedGrassmannian
    [CompactSpace S] [QuasiSeparatedSpace S] [IsAffine B]
    (n : ℕ) (hn : 0 < n) (p : S ⟶ B)
    {C : B.Modules} (hC : HasFiniteLocalBasis C)
    {R E : Type u} [CommRing R] [AddCommGroup E] [Module R E] {k : ℕ}
    (D : Rep R E k) (f : S ⟶ D.Gr) [IsAffineHom f]
    (q : E → Γ(stabilizedModule G n p C, ⊤))
    (hc : GrassmannianDeterminant.HasAffinePointComparison D f
      (stabilizedModule G n p C) q) :
    (smoothLieDeterminant G ‹Smooth G.X.hom›).dual.IsAmple := by
  let hP := stabilizedModule_hasFiniteLocalBasis G n p hC
  have hample : (finiteLocallyFreeDeterminant hP).IsAmple :=
    GrassmannianDeterminant.finiteLocallyFreeDeterminant_isAmple_of_affinePointComparison
      D f (stabilizedModule G n p C) q hP hc
  have hjet : (determinant G n).IsAmple :=
    (finiteLocallyFreeDeterminant_biprod_pullback_isAmple_iff
      (hasFiniteLocalBasis G n) hC p hP).mp hample
  exact lieDeterminantDual_isAmple_of_positiveJet G n hn hjet

end Langlands.GroupScheme.IdentityJet
