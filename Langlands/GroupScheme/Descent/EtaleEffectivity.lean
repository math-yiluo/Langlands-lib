import Langlands.GroupScheme.Descent.LocalSolutionEffectivity
import Langlands.GroupScheme.Descent.EtaleAffineBaseEffectivity

/-! # Effective étale descent of affine group schemes over an arbitrary base -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 2500

namespace Langlands.GroupScheme.Descent

/-- Every chart of the directed affine cover is affine. -/
instance directedAffineCover_isAffine (B : Scheme.{u}) (i : B.directedAffineCover.I₀) :
    IsAffine (B.directedAffineCover.X i) :=
  inferInstanceAs (IsAffine (show B.affineOpens from i))

namespace LocalSolutionGluing

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  (D : Datum p G)
  (𝒰 : B.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]
  [Etale p] [Surjective p]
  (s : ∀ i : 𝒰.I₀, Solution (D.baseChange (𝒰.f i)))
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  [∀ i, IsAffineHom (s i).obj.X.hom]

/-- Affineness of the chosen local quotients passes to the glued structure map. -/
instance obj_isAffineHom : IsAffineHom (obj D 𝒰 s).hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom) 𝒰
  intro i
  change IsAffineHom (pullback.snd (data D 𝒰 s).toBase (𝒰.f i))
  let h := ((data D 𝒰 s).isPullback_natTrans_ι_toBase i).flip
  rw [← h.isoPullback_inv_snd]
  change IsAffineHom (h.isoPullback.inv ≫ (s i).obj.X.hom)
  infer_instance

/-- Reconstructing group operations retains the affine glued structure map. -/
instance solution_isAffineHom : IsAffineHom (solution D 𝒰 s).obj.X.hom :=
  inferInstanceAs (IsAffineHom (obj D 𝒰 s).hom)

end LocalSolutionGluing

namespace Datum

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  (D : Datum p G) [Etale p] [Surjective p] [IsAffineHom G.X.hom]

/-- Effective descent of an affine group scheme along an arbitrary surjective étale map. -/
def etaleSolution : Solution D :=
  LocalSolutionGluing.solution D B.directedAffineCover
    (fun i => by
      letI : IsAffineHom
          ((GroupScheme.baseChange (pullback.fst p (B.directedAffineCover.f i))).obj G).X.hom := by
        change IsAffineHom (pullback.snd G.X.hom (pullback.fst p (B.directedAffineCover.f i)))
        exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›
      exact (D.baseChange (B.directedAffineCover.f i)).etaleAffineBaseSolution)

/-- The descended group scheme is affine over the original arbitrary base. -/
instance etaleSolution_isAffineHom : IsAffineHom D.etaleSolution.obj.X.hom := by
  unfold etaleSolution
  infer_instance

end Datum
end Langlands.GroupScheme.Descent
