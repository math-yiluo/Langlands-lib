import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureAbelianSchemeStatement
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureGroupSchemeProof
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureConnected
import Langlands.AlgebraicGeometry.AlgClosedConnectedProof

/-! # The actual torsion closure as an abelian scheme -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

theorem twoPowerTorsionClosureAbelianScheme_exists :
    TwoPowerTorsionClosureAbelianSchemeStatement.{u} := by
  intro K _ _ _ A
  obtain ⟨G, f, hi, hs, hp, hrange⟩ :=
    twoPowerTorsionClosureGroupScheme_exists K A
  have : IsClosedImmersion (CommGroupScheme.hom f) := hi
  have : Smooth G.X.hom := hs
  have : IsProper G.X.hom := hp
  have hconn : _root_.IsConnected (Set.range (CommGroupScheme.hom f)) := by
    rw [hrange]
    exact isConnected_closure_twoPowerTorsionLocus A
  have : ConnectedSpace G.X.left := by
    obtain ⟨_, ⟨x, rfl⟩⟩ := hconn.nonempty
    refine connectedSpace_iff_univ.mpr ⟨⟨x, Set.mem_univ _⟩, ?_⟩
    apply (CommGroupScheme.hom f).isClosedEmbedding.isInducing.isPreconnected_image.mp
    simpa only [Set.image_univ] using hconn.isPreconnected
  have : GeometricallyConnected G.X.hom :=
    Langlands.AlgebraicGeometry.algClosedConnected K G.X.left G.X.hom
  let B : AbelianScheme (Spec (CommRingCat.of K)) := { G with }
  let j : B ⟶ A := f
  exact ⟨B, j, hi, hrange⟩

end Langlands.AbelianScheme.Tate
