import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Rational.Characters

/-! # Central extensions of `SL₂` split uniquely -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Central extensions of `SL₂` split uniquely** (Conrad, *Reductive group schemes*,
Proposition 4.3.1, due to Gabber). Let `S` be a scheme, `Z` a commutative separated group
scheme over `S`, and `1 → Z → E → SL₂ → 1` a central extension of fppf group sheaves in which
`E` is a group scheme: `z : Z ⟶ E` is a central monomorphism whose points are exactly the
points of `E` killed by `q : E ⟶ SL₂`, and every point of `SL₂` lifts to `E` on some fppf
cover. Then `q` has exactly one homomorphic section. -/
def SpecialLinearCentralExtensionSplitStatement : Prop :=
  ∀ (S : Scheme.{u}),
    let SL₂ : GroupScheme S := (GroupScheme.baseChange (Gm.toSpecZ S)).obj
      (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of (ULift.{u} ℤ)))
    ∀ (Z : CommGroupScheme S), IsSeparated Z.toGrp.X.hom →
    ∀ (E : GroupScheme S) (z : Z.toGrp ⟶ E) (q : E ⟶ SL₂),
      Mono z.hom.hom → IsCentral z →
      (∀ (T : Over S) (x : T ⟶ E.X),
        x ≫ q.hom.hom = 1 ↔ x ∈ (SubgroupFunctor.range z).carrier T) →
      (∀ (T : Over S) (y : T ⟶ SL₂.X),
        ∃ 𝒰 : Scheme.Cover.{u}
            (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left,
          ∀ i : 𝒰.I₀, ∃ x : Over.mk (𝒰.f i ≫ T.hom) ⟶ E.X,
            x ≫ q.hom.hom = (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ y) →
      ∃! s : SL₂ ⟶ E, s ≫ q = 𝟙 SL₂

end Langlands.GroupScheme
