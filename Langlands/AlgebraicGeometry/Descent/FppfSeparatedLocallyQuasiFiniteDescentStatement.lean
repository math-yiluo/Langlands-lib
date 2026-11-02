import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Effective fppf descent of separated locally quasi-finite schemes, sheaf form -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace

/-- Let `G` be an actual fppf sheaf over `S` with a map `p` to the functor of points of a
scheme `T` over `S`. Suppose that on some fppf covering sieve `J` of `T`, every base change of
`p` along a member `g : T' ⟶ T` of `J` is represented by a separated morphism `x' : X' ⟶ T'`
that is locally quasi-finite and locally of finite type. Then `G` is represented by a scheme
`X` over `T`, compatibly with `p`. -/
def FppfSeparatedLocallyQuasiFiniteDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : FppfSheaf S) (T : Over S) (p : G.obj ⟶ (schemeYoneda S).obj T)
    (J : Sieve T), J ∈ fppfTopology S T →
    (∀ ⦃T' : Over S⦄ (g : T' ⟶ T), J g →
      ∃ (X' : Over S) (x' : X' ⟶ T') (a' : (schemeYoneda S).obj X' ⟶ G.obj),
        IsPullback a' ((schemeYoneda S).map x') p ((schemeYoneda S).map g) ∧
          IsSeparated x'.left ∧ LocallyQuasiFinite x'.left ∧ LocallyOfFiniteType x'.left) →
    ∃ (X : Over S) (x : X ⟶ T) (e : (schemeYoneda S).obj X ≅ G.obj),
      e.hom ≫ p = (schemeYoneda S).map x

end Langlands.AlgebraicGeometry
