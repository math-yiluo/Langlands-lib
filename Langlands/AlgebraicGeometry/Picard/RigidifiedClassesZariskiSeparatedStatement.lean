import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassPresheaf

/-! # Zariski separatedness of rigidified abelian-scheme classes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Two actual rigidified isomorphism classes on `T ×_S A` that agree after
pullback to every member of a Zariski open cover of `T` are equal. -/
def RigidifiedClassesZariskiSeparatedStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S)
    (𝒰 : T.left.OpenCover.{u}) (q r : RigidifiedClasses A T),
    (∀ i,
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) q =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) r) →
    q = r

end Langlands.AbelianScheme
