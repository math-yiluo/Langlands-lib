import Langlands.GroupScheme.RelativeLevi.ModuliTorsorConstruction
import Langlands.GroupScheme.RelativeLevi.TorsorLocalPoint

/-! # Smooth affine models of the actual Levi presheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P U : GroupScheme S} {i : P ⟶ G} {r : U ⟶ P}
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r)

/-- The affine cocycle model of actual Levi images, from the two sheaf
conditions needed by local-point assembly and effective descent. -/
def affineModuliModel [IsAffine S]
    (hZ : Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (moduliFunctorOfParabolic hi hG))
    (hE : ∀ {V W : Over S} (p : V ⟶ W) [Etale p.left] [Surjective p.left],
      Presieve.IsSheafFor (moduliFunctorOfParabolic hi hG) (.singleton p)) :
    PresheafTorsor.SmoothAffineModel (moduliFunctorOfParabolic hi hG) := by
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth U.X.hom := hr.smooth
  let q := affineEtaleLeviPoint hi hG hZ
  let : IsAffine q.test.left := q.affine
  let : Etale q.test.hom := q.etale
  let : Surjective q.test.hom := q.surjective
  exact (moduliAction i r hG hi hr).affineModel q.point hE

/-- Models of the changed-base parabolic presheaf also represent
restriction of the original presheaf to that base. -/
def restrictModuliModel {B : Scheme.{u}} (b : B ⟶ S)
    (M : PresheafTorsor.SmoothAffineModel
      (moduliFunctorOfParabolic (hi.baseChange hG b) (hG.baseChange b))) :
    PresheafTorsor.SmoothAffineModel
      ((Over.map b).op ⋙ moduliFunctorOfParabolic hi hG) where
  scheme := M.scheme
  represents := M.represents.ofIso (moduliPresheafBaseChangeIso (i := i) (hi := hi) (hG := hG) (b := b))
  affine := M.affine
  smooth := M.smooth
  surjective := M.surjective

/-- Actual affine-base models glue to a model over an arbitrary base. -/
def moduliModelOfAffineModels
    (hZ : Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
      (moduliFunctorOfParabolic hi hG))
    (hModels : ∀ {B : Scheme.{u}} (b : B ⟶ S) [IsAffine B],
      PresheafTorsor.SmoothAffineModel
        (moduliFunctorOfParabolic (hi.baseChange hG b) (hG.baseChange b))) :
    PresheafTorsor.SmoothAffineModel (moduliFunctorOfParabolic hi hG) := by
  let 𝒰 := S.affineCover
  apply PresheafTorsor.SmoothAffineModel.zariskiGlue hZ 𝒰
  intro j
  let : IsAffine (𝒰.X j) := by
    dsimp [𝒰]
    infer_instance
  exact restrictModuliModel hG hi (𝒰.f j) (hModels (𝒰.f j))

end Langlands.GroupScheme.RelativeLevi
