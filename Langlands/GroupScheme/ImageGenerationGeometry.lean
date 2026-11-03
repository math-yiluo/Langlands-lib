import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.GroupScheme.ImageGenerationStatement
import Mathlib.AlgebraicGeometry.Group.Smooth
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected

/-! # Geometric assembly for a dominant generated subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GeneratedImage

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {V : Over (Spec (CommRingCat.of k))} {f : V ⟶ G.X}

/-- A geometrically reduced and geometrically irreducible closed subgroup of a
 locally finite-type affine group, with a dominant positive product, supplies
 the full geometric conclusion for the fixed closed image envelope. -/
def ofGeometricPower [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (g : V ⟶ H.X) (hg : g ≫ i.hom.hom = f) (n : ℕ) (hn : 0 < n)
    [GeometricallyReduced H.X.hom] [GeometricallyIrreducible H.X.hom]
    [hDom : IsDominant (orderedPowerMap g n).left] :
    {D : GeneratedImage f // D.HasSmoothConnectedGeneration} := by
  letI : IsClosedImmersion i.hom.hom.left := hi
  letI : IsAffineHom H.X.hom := by
    rw [← i.hom.hom.w]
    infer_instance
  letI : LocallyOfFiniteType H.X.hom := by
    rw [← i.hom.hom.w]
    infer_instance
  letI : IsReduced H.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian H.X.hom
  let D := ofDominantPower i hi g hg n
  refine ⟨D, ?_⟩
  change Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧
    GeometricallyConnected H.X.hom ∧
    ∃ m : ℕ, 0 < m ∧ IsDominant (D.powerMap m).left
  refine ⟨?_, inferInstance,
    GeometricallyIrreducible.geometricallyConnected H.X.hom, n, hn, ?_⟩
  · let : GrpObj (Over.mk H.X.hom) := inferInstanceAs (GrpObj H.X)
    exact smooth_of_grpObj H.X.hom
  · dsimp only [D]
    rw [ofDominantPower_powerMap]
    exact hDom

end GeneratedImage

end Langlands.GroupScheme
