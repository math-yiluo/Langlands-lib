import Langlands.AbelianScheme.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Descent of group schemes and abelian schemes to finitely generated subalgebras -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands

/-- Let `G` be a group scheme over `Spec A` whose underlying scheme is a base change of a
quasi-compact, quasi-separated scheme `X₀` of finite presentation over `Spec A₀`. Then `G` is,
as a group scheme, the base change of a group scheme `G₀` over `Spec T`, for a finitely
generated `A₀`-subalgebra `T` of `A` containing any given finite set. The underlying scheme of
`G₀` is a base change of `X₀`, and `G₀` is commutative when `G` is. -/
def GroupScheme.SubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f₀]
    [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀]
    (G : GroupScheme (Spec (CommRingCat.of A))) (a : G.X.left ⟶ X₀),
    IsPullback a G.X.hom f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) →
    ∀ (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (G₀ : GroupScheme (Spec (CommRingCat.of ↥T))) (a₀ : G₀.X.left ⟶ X₀),
        IsPullback a₀ G₀.X.hom f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ∧
        (IsCommMonObj G.X → IsCommMonObj G₀.X) ∧
        Nonempty (G ≅ (GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))).obj G₀)

/-- Every abelian scheme over `Spec R` is isomorphic to the base change of an abelian scheme
over `Spec R₀`, for a finitely generated subring `R₀` of `R`. -/
def AbelianScheme.SubalgebraDescentStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (A : AbelianScheme (Spec R)),
    ∃ (R₀ : Subalgebra ℤ R), R₀.FG ∧
      ∃ (A₀ : AbelianScheme (Spec (CommRingCat.of ↥R₀))),
        Nonempty (A ≅ (AbelianScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap ↥R₀ R)))).obj A₀)

end Langlands
