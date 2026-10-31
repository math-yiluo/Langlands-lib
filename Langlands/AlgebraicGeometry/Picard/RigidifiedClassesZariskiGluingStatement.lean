import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassPresheaf

/-! # Zariski gluing of rigidified abelian-scheme classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Actual rigidified classes on members of a Zariski open cover of the test
scheme that agree on pairwise overlaps come from an actual global class. -/
def RigidifiedClassesZariskiGluingStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S)
    (𝒰 : T.left.OpenCover.{u})
    (q : ∀ i, RigidifiedClasses A (Over.mk (𝒰.f i ≫ T.hom))),
    (∀ i j,
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom)) (q i) =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j))
            (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom)) (q j)) →
    ∃ q₀ : RigidifiedClasses A T, ∀ i,
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) q₀ = q i

end Langlands.AbelianScheme
