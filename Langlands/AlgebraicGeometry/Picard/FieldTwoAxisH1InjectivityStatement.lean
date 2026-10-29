import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Degree-one restriction to the two axes of a product over a field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules

/-- Over a field `K`, let `P` be a fibre product of smooth proper geometrically
connected `K`-schemes `X` and `Y` with rational points `x₀`, `y₀`. A class in
`H¹(P, 𝒪_P)` whose images under the units `𝒪_P ⟶ iⱼ_* iⱼ^* 𝒪_P` of the two
section axes `i₁ = (id, y₀)` and `i₂ = (x₀, id)` both vanish is zero. -/
def FieldTwoAxisH1InjectivityStatement : Prop :=
  ∀ (K : CommRingCat.{u}), IsField K →
  ∀ (X Y : Over (Spec K)),
    Smooth X.hom → IsProper X.hom → GeometricallyConnected X.hom →
    Smooth Y.hom → IsProper Y.hom → GeometricallyConnected Y.hom →
    ∀ (x₀ : Over.mk (𝟙 (Spec K)) ⟶ X) (y₀ : Over.mk (𝟙 (Spec K)) ⟶ Y)
      (P : Scheme.{u}) (p₁ : P ⟶ X.left) (p₂ : P ⟶ Y.left)
      (hP : IsPullback p₁ p₂ X.hom Y.hom),
      let i₁ : X.left ⟶ P := hP.lift (𝟙 X.left) (X.hom ≫ y₀.left) (by simp)
      let i₂ : Y.left ⟶ P := hP.lift (Y.hom ≫ x₀.left) (𝟙 Y.left) (by simp)
      let O := Langlands.Scheme.Modules.structureSheaf P
      let H := DerivedSections.relativeCohomology (p₁ ≫ X.hom) 1
      ∀ c : H.obj O,
        (H.map ((Scheme.Modules.pullbackPushforwardAdjunction i₁).unit.app O)).hom c = 0 →
        (H.map ((Scheme.Modules.pullbackPushforwardAdjunction i₂).unit.app O)).hom c = 0 →
        c = 0

end Langlands.AlgebraicGeometry.Picard
