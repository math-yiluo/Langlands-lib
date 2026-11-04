import Langlands.GroupScheme.Lie.PointTangent
import Langlands.GroupScheme.Lie.FiniteDimensional
import Langlands.AlgebraicGeometry.FlatQuasiFiniteStalkDimension
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Lie dimensions under smooth group-scheme isogenies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual Lie dimension of a smooth affine group is its identity stalk dimension. -/
theorem finrank_kernel_cast_eq_ringKrullDim (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] :
    let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
    (Module.finrank k (Additive (lieKernel G k)) : WithBot ℕ∞) =
      ringKrullDim (G.X.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))) := by
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
  let R := G.X.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))
  have hreg : IsRegularLocalRing R :=
    Smooth.isRegularLocalRing_stalk (f := G.X.hom) (e.left (IsLocalRing.closedPoint k))
  have := hreg
  rw [finrank_kernel_eq_cotangent G]
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp hreg

/-- Flat locally quasi-finite homomorphisms between smooth affine groups preserve Lie dimension. -/
theorem finrank_kernel_eq_of_flat_locallyQuasiFinite
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom]
    (q : G ⟶ H) [Flat q.hom.hom.left] [LocallyQuasiFinite q.hom.hom.left] :
    Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel H k)) := by
  let eG : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
  let eH : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X := 1
  have he : q.hom.hom.left (eG.left (IsLocalRing.closedPoint k)) =
      eH.left (IsLocalRing.closedPoint k) := by
    have hm : eG ≫ q.hom.hom = eH := MonObj.one_comp _
    exact congrArg (fun p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X =>
      p.left (IsLocalRing.closedPoint k)) hm
  have hd := Langlands.AlgebraicGeometry.stalk_ringKrullDim_eq_of_flat_locallyQuasiFinite
    q.hom.hom.left (eG.left (IsLocalRing.closedPoint k))
  rw [he] at hd
  have hc := (finrank_kernel_cast_eq_ringKrullDim G).trans
    (hd.trans (finrank_kernel_cast_eq_ringKrullDim H).symm)
  exact_mod_cast hc

/-- An abstract linear equivalence of Lie spaces; it is not asserted to be the differential. -/
def kernelLinearEquivOfFlatLocallyQuasiFinite
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom]
    (q : G ⟶ H) [Flat q.hom.hom.left] [LocallyQuasiFinite q.hom.hom.left] :
    Additive (lieKernel G k) ≃ₗ[k] Additive (lieKernel H k) :=
  LinearEquiv.ofFinrankEq _ _ (finrank_kernel_eq_of_flat_locallyQuasiFinite q)

/-- In particular, a smooth affine isogeny preserves the actual Lie finrank. -/
theorem finrank_kernel_eq_of_isogeny
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom]
    (q : G ⟶ H) (hq : IsIsogeny q) :
    Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel H k)) := by
  have : IsFinite q.hom.hom.left := hq.1
  have : Flat q.hom.hom.left := hq.2.1
  exact finrank_kernel_eq_of_flat_locallyQuasiFinite q

end Langlands.GroupScheme.Lie
