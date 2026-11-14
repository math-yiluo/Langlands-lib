import Langlands.AbelianScheme.Isogeny
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Statement: isogenies of reductive groups that agree on a maximal torus -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Isogenies agreeing on a maximal torus differ by `(T/Z_G)(S)`** (Conrad, *Reductive group
schemes* (2014), Corollary 6.1.15, second assertion). Let `G'` and `G` be reductive group
schemes over a scheme `S` with maximal tori `i' : T' ⟶ G'` and `i : T ⟶ G` (closed subgroups
that are `S`-tori with maximal residue fibres), and let `f F : G' ⟶ G` be isogenies that carry
`T'` into `T`. Say that a point `t` of `T` over an `S`-scheme `V` conjugates `F` into `f` when
`f(g) = t F(g) t⁻¹` for every point `g` of `G'` over every `V`-scheme. Then:
1. `f` and `F` agree on `T'` if and only if, fppf-locally on `S`, some point of `T` conjugates
   `F` into `f` (this is `f = c_t ∘ F` for some `t ∈ (T/Z_G)(S)`);
2. two points of `T` over the same `V` that both conjugate `F` into `f` differ by a point that
   is central in `G` over every `V`-scheme (this is the uniqueness of `t ∈ (T/Z_G)(S)`). -/
def ReductiveIsogenyTorusRigidityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G' G : GroupScheme S), IsReductive G' → IsReductive G →
    ∀ (T' T : CommGroupScheme S) (i' : T'.toGrp ⟶ G') (i : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T'.toGrp → IsClosedSubgroup i' → IsFibrewiseMaximalTorus i' →
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup i → IsFibrewiseMaximalTorus i →
      ∀ f F : G' ⟶ G, IsIsogeny f → IsIsogeny F →
        (∃ τ : T'.toGrp ⟶ T.toGrp, i' ≫ f = τ ≫ i) →
        (∃ τ : T'.toGrp ⟶ T.toGrp, i' ≫ F = τ ≫ i) →
        let Conjugates : ∀ {V : Over S}, (V ⟶ T.X) → Prop := fun {V} t =>
          ∀ (U : Over S) (a : U ⟶ V) (g : U ⟶ G'.X),
            g ≫ f.hom.hom =
              (a ≫ t ≫ i.hom.hom) * (g ≫ F.hom.hom) * (a ≫ t ≫ i.hom.hom)⁻¹
        (i' ≫ f = i' ≫ F ↔
          ∃ 𝒰 : Scheme.Cover.{u}
              (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S,
            ∀ k : 𝒰.I₀, ∃ t : Over.mk (𝒰.f k) ⟶ T.X, Conjugates t) ∧
        ∀ (V : Over S) (t₁ t₂ : V ⟶ T.X), Conjugates t₁ → Conjugates t₂ →
          ∀ (U : Over S) (a : U ⟶ V) (h : U ⟶ G.X),
            ((a ≫ t₁ ≫ i.hom.hom)⁻¹ * (a ≫ t₂ ≫ i.hom.hom)) * h =
              h * ((a ≫ t₁ ≫ i.hom.hom)⁻¹ * (a ≫ t₂ ≫ i.hom.hom))

end Langlands.GroupScheme
