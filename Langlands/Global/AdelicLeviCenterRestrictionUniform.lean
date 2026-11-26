import Langlands.Automorphic.GroupSchemePlotSmoothRightCovariance
import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationStatement
import Langlands.Global.AdelicInducedHarishChandraCenterReduction

/-! # Uniform Levi center restriction from restriction at the identity -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped Classical CategoryTheory.MonObj ContDiff Manifold TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "R∞" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "D" => plotSmoothEnvelopingAction F G hsmooth hcalc
local notation "I∞" => 𝓘(ℝ, smoothModel F d)
local notation "Z" => AdelicEnvelopingCenter F G hsmooth
local notation "rightAction" => G.plotSmoothRightAction R∞ (B := mixedEmbedding.mixedSpace F)
  (RingEquiv.toRingHom (InfiniteAdeleRing.ringEquiv_mixedSpace F))

/-- If the adjoint action fixes the center, right translation commutes with each actual
center derivative on every infinite plot-smooth function. -/
theorem plotSmoothRightAction_center (hAd : AdelicEnvelopingCenterConjugationStatement.{u})
    (hG : GroupScheme.IsConnectedReductive G) (g : G∞) (z : Z) (f : InfinitePlotSmoothFunctions F G) :
    rightAction g (plotSmoothCenterAction F G hsmooth hcalc z f) =
      plotSmoothCenterAction F G hsmooth hcalc z (rightAction g f) := by
  change rightAction g (D z.val f) = D z.val (rightAction g f)
  rw [adelicPlotSmoothEnvelopingRightCovariance F G hsmooth hcalc, hAd F G hsmooth hG g z.val z.property]

end Langlands.Global.InfiniteAdelicGroupPoints

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G P U M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine M.X.left]
  {p : P ⟶ G} (iU : U ⟶ P) (l : M ⟶ P)
  {d e : ℕ} (hsG : SmoothOfRelativeDimension d G.X.hom) (hcG : AdelicDifferentialCommutator F G hsG)
  (hsM : SmoothOfRelativeDimension e M.X.hom) (hcM : AdelicDifferentialCommutator F M hsM)

local notation "R∞" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "M∞" => InfiniteAdelicGroupPoints F M
local notation "DG" => plotSmoothCenterAction F G hsG hcG
local notation "DM" => plotSmoothEnvelopingAction F M hsM hcM
local notation "rightAction" => G.plotSmoothRightAction R∞ (B := mixedEmbedding.mixedSpace F)
  (RingEquiv.toRingHom (InfiniteAdeleRing.ringEquiv_mixedSpace F))

/-- Restrict a plot-smooth function on the infinite group to the infinite Levi
through the identity. -/
def infiniteLeviIdentitySlice (v : InfinitePlotSmoothFunctions F G) : InfinitePlotSmoothFunctions F M :=
  ⟨fun m => v.val (M.affinePointsTarget (l ≫ p) R∞ m),
    (show G.IsPlotSmooth R∞ (B := mixedEmbedding.mixedSpace F)
      (RingEquiv.toRingHom (InfiniteAdeleRing.ringEquiv_mixedSpace F)) v.val from v.property).postcomp
      (l ≫ p).hom.hom⟩

/-- An unnormalized Levi restriction identity at the group identity extends to every
adelic fibre by right translation and invariance of the ambient center. -/
theorem hasUniformLeviCenterTransfer_of_identity [IsAffine U.X.left]
    (hAd : AdelicEnvelopingCenterConjugationStatement.{u}) (hG : IsConnectedReductive G)
    (h₁ : ∀ z : AdelicEnvelopingCenter F G hsG, ∃ y : AdelicEnvelopingAlgebra F M hsM,
      ∀ (v : InfinitePlotSmoothFunctions F G),
        (∀ (u : U∞) (a : G∞), v.val (U.affinePointsTarget (iU ≫ p) R∞ u * a) = v.val a) →
          DM y (infiniteLeviIdentitySlice (p := p) l v) = infiniteLeviIdentitySlice (p := p) l (DG z v)) :
    HasUniformLeviCenterTransfer (p := p) iU l hsG hcG hsM hcM := by
  intro z
  obtain ⟨y, hy⟩ := h₁ z
  refine ⟨y, fun f hinv hf x m => ?_⟩
  let v : InfinitePlotSmoothFunctions F G := ⟨functionInfiniteSlice F G f (finite F G x), hf _⟩
  let a := infinite F G x
  let translated := rightAction a v
  have hLeft (u : U∞) (b : G∞) :
      translated.val (U.affinePointsTarget (iU ≫ p) R∞ u * b) = translated.val b := by
    let u₁ := map F U G (iU ≫ p) (ofInfinite F U u)
    have hu : u₁ ∈ parabolicQuotientSubgroup F p iU l := Subgroup.mem_sup_left ⟨_, rfl⟩
    have he : u₁ * pair F G (b * a) (finite F G x) =
        pair F G (U.affinePointsTarget (iU ≫ p) R∞ u * b * a) (finite F G x) := by
      unfold u₁
      rw [map_ofInfinite, ofInfinite_eq_pair, pair_mul, one_mul, mul_assoc]
    change f (pair F G (U.affinePointsTarget (iU ≫ p) R∞ u * b * a) (finite F G x)) =
      f (pair F G (b * a) (finite F G x))
    rw [← he]
    exact hinv u₁ hu _
  have eq := hy translated hLeft
  change DM y (infiniteLeviIdentitySlice (p := p) l (rightAction a v)) =
    infiniteLeviIdentitySlice (p := p) l (DG z (rightAction a v)) at eq
  rw [← plotSmoothRightAction_center hsG hcG hAd hG] at eq
  exact congrArg (fun w : InfinitePlotSmoothFunctions F M => w.val m) eq

end Langlands.Global.AdelicGroupPoints
