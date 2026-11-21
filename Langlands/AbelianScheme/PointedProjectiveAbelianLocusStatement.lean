import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The abelian-scheme locus of a pointed projective family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry

/-- The pullback of `p` along `t` carries an abelian scheme of relative dimension `g`
whose identity is the section induced by `s`. -/
def HasPointedAbelianPullback {S X T : Scheme.{u}} (p : X ⟶ S) (s : S ⟶ X)
    (g : ℕ) (t : T ⟶ S) : Prop :=
  ∃ (A : AbelianScheme T) (e : A.X.left ≅ pullback p t),
    A.HasRelativeDimension g ∧
      e.hom ≫ pullback.snd p t = A.X.hom ∧
      η[A.X].left ≫ e.hom ≫ pullback.fst p t = t ≫ s

/-- A flat, locally finitely presented, pointed projective family over a locally
noetherian base has an open locus for pointed abelian-scheme structures of any
fixed relative dimension. -/
def PointedProjectiveAbelianLocusStatement : Prop :=
  ∀ (S X : Scheme.{u}) [IsLocallyNoetherian S] (m g : ℕ)
    (i : X ⟶ RelativeProjectiveSpace S m) (_hi : IsClosedImmersion i) (s : S ⟶ X),
    let p := i ≫ RelativeProjectiveSpace.toBase S m
    s ≫ p = 𝟙 S → Flat p → LocallyOfFinitePresentation p →
      ∃ U : S.Opens, ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S),
        Set.range t ⊆ U ↔ HasPointedAbelianPullback p s g t

end Langlands.AbelianScheme
