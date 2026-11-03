import Langlands.Algebra.GradedHopf.SplitUnipotent
import Langlands.Algebra.GradedHopf.UnipotentFlag
import Langlands.GroupScheme.Rational.TorusHopfGradingAdapter
import Langlands.GroupScheme.Rational.TorusUnipotenceStatement
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.AffineHopfCoordinates

/-! # Split unipotence for split torus actions without zero Lie weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]

/-- Smoothness of the structure morphism is invariant under group-scheme isomorphism. -/
theorem smooth_hom_of_iso {H H' : GroupScheme (Spec (CommRingCat.of k))} (e : H ≅ H')
    (h : Smooth H'.X.hom) : Smooth H.X.hom := by
  have : IsIso e.hom.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map e.hom))
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- Connectedness of the underlying space is invariant under group-scheme isomorphism. -/
theorem connectedSpace_left_of_iso {H H' : GroupScheme (Spec (CommRingCat.of k))} (e : H ≅ H')
    (h : ConnectedSpace H'.X.left) : ConnectedSpace H.X.left := by
  have : IsIso e.inv.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map e.inv))
  exact Function.Surjective.connectedSpace
    (Scheme.homeoOfIso (asIso e.inv.hom.hom.left)).surjective
    (Scheme.homeoOfIso (asIso e.inv.hom.hom.left)).continuous

/-- The splitness argument for any smooth connected unipotent affine group with no zero Lie
weight for a split torus action. -/
theorem torusActionSplitUnipotence : TorusActionSplitUnipotenceStatement.{u} := by
  intro k _ H hSmooth hAff hConn hU S hS b hb
  have : IsAffineHom H.X.hom := hAff
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨𝒜, _, h𝒜, h0⟩ := TorusGradedHopf.exists_graded_of_noZeroWeight H hSmooth S hS b hb
  have e := AffineCoordinates.hopfSpecIso H
  have hSm := smooth_hom_of_iso e hSmooth
  have hC := connectedSpace_left_of_iso e hConn
  have hU' : IsUnipotent ((hopfSpec (CommRingCat.of k)).obj (op (AffineCoordinates.hopfAlgebra H))) :=
    hU.of_iso e
  have hsm : Algebra.Smooth (CommRingCat.of k) (AffineCoordinates.hopfAlgebra H) :=
    (Langlands.Algebra.GradedHopf.smooth_hopfSpec_iff _).1 hSm
  have : Algebra.FiniteType k (AffineCoordinates.hopfAlgebra H) :=
    inferInstanceAs (Algebra.FiniteType (CommRingCat.of k) (AffineCoordinates.hopfAlgebra H))
  obtain ⟨G, hdiag, hlow⟩ :=
    Langlands.Algebra.GradedHopf.exists_unitriangular_of_isUnipotent _ 𝒜 h𝒜 hU'
  exact (Langlands.Algebra.GradedHopf.isSplitUnipotent_of_graded _ 𝒜 h𝒜 h0 G hdiag hlow hSm
    hC).of_iso e

end Langlands.GroupScheme.RelativeRoot
