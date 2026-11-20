import Langlands.GroupScheme.Torus.GenericPointCentralizerStatement
import Langlands.GroupScheme.Absolute.StronglyRegularTorusPointProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.Integral
import Langlands.AlgebraicGeometry.ClosedRationalPoints

/-! # Proof: a torus has a point with the same centralizer (Milne 16.42) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusGenericPointCentralizer

variable {k : Type u} [Field k]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The centralizer of a torus lies in the centralizer of each of its rational points. -/
theorem torusCentralizer_le_pointCentralizer (j : T.toGrp ⟶ G)
    (s : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ T.X) :
    torusCentralizer j ≤ G.pointCentralizer (s ≫ j.hom.hom) := by
  intro Z c hc
  rw [mem_pointCentralizer]
  have h := (hc Z (𝟙 Z) (toUnit Z ≫ s)).eq
  simpa only [Category.id_comp, Category.assoc] using h

end TorusGenericPointCentralizer

/-- **Milne 16.42.** A torus in a smooth affine group over an algebraically closed field has a
rational point whose all-test centralizer equals the centralizer of the torus. -/
theorem torusGenericPointCentralizer : TorusGenericPointCentralizerStatement.{u} := by
  classical
  intro k _ _ G _ _ _ T j _ hT
  have : Smooth T.X.hom := hT.smooth
  have : IsIntegral T.X.left := hT.isIntegral
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  have hTs : IsSplitTorus T.toGrp :=
    hT.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨σ, hσ, hdiag⟩ := StronglyRegularTorusPoint.exists_rationalDiagonal ρ j hTs
  have : Mono σ.hom.hom := hσ
  let d : Fin N → Γ(T.X.left, ⊤) := fun i => (σ.restrict j).pointMatrix T.X (𝟙 T.X) i i
  have hd := StronglyRegularTorusPoint.universal_diagonal (σ.restrict j) hdiag
  obtain ⟨U, hUne, hUsep⟩ := StronglyRegularTorusPoint.exists_separatingOpen d
  obtain ⟨s, hs⟩ :=
    Langlands.AlgebraicGeometry.ClosedRationalPoints.exists_rationalPoint_mem U hUne
  have hsU : Set.range s.left ⊆ U := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint k :=
      Subsingleton.elim (α := ↥(Spec (CommRingCat.of k))) _ _
    rwa [hp]
  refine ⟨s, le_antisymm ?_
    (TorusGenericPointCentralizer.torusCentralizer_le_pointCentralizer j s)⟩
  intro Z c hc
  rw [mem_pointCentralizer] at hc
  exact StronglyRegularTorusPoint.mem_centralizer_of_separating σ j d hd s (hUsep s hsU) c hc

end Langlands.GroupScheme
