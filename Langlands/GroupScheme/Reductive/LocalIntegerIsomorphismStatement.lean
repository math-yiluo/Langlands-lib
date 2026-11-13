import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # Statement: generic isomorphisms of reductive groups over local integers -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel

namespace Langlands.GroupScheme

/-- **Generic isomorphisms extend after the adjoint action** (Conrad, *Reductive group
schemes* (2014), Theorem 7.2.16). Let `F` be a nonarchimedean local field with valuation
ring `R = 𝒪[F]`, and let `G`, `G'` be reductive group schemes over `R`. Let
`q : G_F ⟶ A` be an adjoint quotient of the generic fibre `G_F`, acting on `G_F` by its
inner action. For every isomorphism `f : G_F ≅ G'_F` there are a point `x ∈ A(F)` and an
isomorphism `Φ : G ≅ G'` of group schemes over `R` whose generic fibre is `f` composed with
the action of `x`: on every test scheme `T` over `F` and every `g ∈ G_F(T)`,
`Φ_F(g) = f(x · g)`. -/
def ReductiveLocalIntegerIsomorphismStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G G' : GroupScheme (Spec (CommRingCat.of ↥𝒪[F]))), IsReductive G → IsReductive G' →
    ∀ (f : (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj G ≅
        (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj G')
      (A : GroupScheme (Spec (CommRingCat.of F)))
      (q : (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj G ⟶ A)
      (hq : IsAdjointQuotient q),
    ∃ (x : rationalPoints A) (Φ : G ≅ G'),
      ∀ (T : Over (Spec (CommRingCat.of F)))
        (g : T ⟶ ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj G).X),
        g ≫ ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).map Φ.hom).hom.hom =
          hq.innerAction.act
              ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of F)))) ≫ x) g ≫
            f.hom.hom.hom

end Langlands.GroupScheme
