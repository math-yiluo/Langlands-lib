import Langlands.GroupScheme.Rational.CyclicWeightQuotientAssembly
import Langlands.GroupScheme.Rational.WeightSemigroupStatement

/-! # Proof of the cyclic weight filtration statement -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeRoot

open Corepresented

/-- The corepresented model of an affine group is affine over the base. -/
theorem isAffineHom_affineCoordinates {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] :
    IsAffineHom (groupScheme (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G)).X.hom := by
  change IsAffineHom ((algSpec (CommRingCat.of k)).obj (op (AffineCoordinates.algebra G))).hom
  rw [algSpec_obj_hom]
  exact isAffineHom_of_isAffine (X := Spec (CommRingCat.of (AffineCoordinates.algebra G))) _

/-- Conrad–Gabber–Prasad, Lemma 3.3.8: for a split torus acting on a smooth affine group, each
positive cyclic weight subgroup is normalized by the first one, and the quotient of any
representative by the next cyclic weight subgroup is an fppf quotient carrying an equivariant
action with a unique weight vector structure of weight `r • a`. -/
theorem cyclicWeightFiltration : CyclicWeightFiltrationStatement.{u} := by
  intro k _ G hG hAff S hS b a ha r hr
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨I, hI, ⟨φ⟩⟩ := id hS
  have : Fintype I := Fintype.ofFinite I
  classical
  have := isAffineHom_affineCoordinates G
  have := AffineCoordinates.formallySmooth_algebra G hG
  have := AffineCoordinates.finiteType_algebra G hG
  exact cyclicWeightFiltration_of_model (AffineCoordinates.corepresentation G)
    (AffineCoordinates.groupSchemeIso G) φ b hS a ha r hr

end Langlands.GroupScheme.RelativeRoot
