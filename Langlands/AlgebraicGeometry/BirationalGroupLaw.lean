import Langlands.AbelianScheme.GroupScheme
import Langlands.AlgebraicGeometry.FibreGenericPoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Birational group laws and their solutions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The universal left translation `(x, y) ↦ (x, x y)` of a law `m` defined on an open
subscheme `D` of `X ×_S X`. -/
def leftTranslation (D : (pullback f f).Opens) (m : D.toScheme ⟶ X)
    (hm : m ≫ f = D.ι ≫ pullback.fst f f ≫ f) : D.toScheme ⟶ pullback f f :=
  pullback.lift (D.ι ≫ pullback.fst f f) m (by rw [hm, Category.assoc])

/-- The universal right translation `(x, y) ↦ (x y, y)` of a law `m` defined on an open
subscheme `D` of `X ×_S X`. -/
def rightTranslation (D : (pullback f f).Opens) (m : D.toScheme ⟶ X)
    (hm : m ≫ f = D.ι ≫ pullback.fst f f ≫ f) : D.toScheme ⟶ pullback f f :=
  pullback.lift m (D.ι ≫ pullback.snd f f)
    (by rw [hm, Category.assoc, pullback.condition])

/-- An `S`-birational group law on `X ⟶ S`, given by a representative: a morphism `mul`
on an `S`-dense open subscheme `domain` of `X ×_S X`, on which both universal
translations are open immersions with `S`-dense images, and which is associative
whenever both products are defined. Density in the fibres over `S` is
`FibreGenerizationDense`. -/
structure BirationalGroupLaw where
  /-- The open subscheme of `X ×_S X` on which the law is given. -/
  domain : (pullback f f).Opens
  /-- The law `(x, y) ↦ x y` on `domain`. -/
  mul : domain.toScheme ⟶ X
  mul_comp : mul ≫ f = domain.ι ≫ pullback.fst f f ≫ f
  domain_dense : FibreGenerizationDense (pullback.fst f f ≫ f) (domain : Set _)
  isOpenImmersion_leftTranslation : IsOpenImmersion (leftTranslation f domain mul mul_comp)
  leftTranslation_dense : FibreGenerizationDense (pullback.fst f f ≫ f)
    (Set.range (leftTranslation f domain mul mul_comp).base)
  isOpenImmersion_rightTranslation : IsOpenImmersion (rightTranslation f domain mul mul_comp)
  rightTranslation_dense : FibreGenerizationDense (pullback.fst f f ≫ f)
    (Set.range (rightTranslation f domain mul mul_comp).base)
  /-- `(x y) z = x (y z)` for points `a = (x, y)`, `c = (y, z)`, `b = (x y, z)` and
  `d = (x, y z)` of `domain`. -/
  assoc : ∀ (T : Scheme.{u}) (a b c d : T ⟶ domain.toScheme),
    a ≫ domain.ι ≫ pullback.snd f f = c ≫ domain.ι ≫ pullback.fst f f →
    b ≫ domain.ι ≫ pullback.fst f f = a ≫ mul →
    b ≫ domain.ι ≫ pullback.snd f f = c ≫ domain.ι ≫ pullback.snd f f →
    d ≫ domain.ι ≫ pullback.fst f f = a ≫ domain.ι ≫ pullback.fst f f →
    d ≫ domain.ι ≫ pullback.snd f f = c ≫ mul →
    b ≫ mul = d ≫ mul

namespace BirationalGroupLaw

variable {f}

/-- A solution of an `S`-birational group law `m` on `X`: a smooth separated group scheme
of finite type over `S`, an `S`-dense open subscheme `domain` of `X`, and an open
immersion of `domain` into the group with `S`-dense image, such that the group law
restricts to `m` on `domain`. -/
structure Solution (m : BirationalGroupLaw f) where
  /-- The group scheme over `S`. -/
  group : Langlands.GroupScheme S
  smooth : Smooth group.X.hom
  isSeparated : IsSeparated group.X.hom
  locallyOfFiniteType : LocallyOfFiniteType group.X.hom
  quasiCompact : QuasiCompact group.X.hom
  /-- The `S`-dense open subscheme of `X` which embeds in the group. -/
  domain : X.Opens
  domain_dense : FibreGenerizationDense f (domain : Set _)
  /-- The open immersion of `domain` into the group. -/
  embedding : domain.toScheme ⟶ group.X.left
  embedding_comp : embedding ≫ group.X.hom = domain.ι ≫ f
  isOpenImmersion_embedding : IsOpenImmersion embedding
  embedding_dense : FibreGenerizationDense group.X.hom (Set.range embedding.base)
  /-- Whenever `x` and `y` are points of `domain` with `(x, y)` in the domain of `m` and
  `m (x, y)` in `domain`, the group product of their images is the image of `m (x, y)`. -/
  mul_eq : ∀ (T : Scheme.{u}) (a : T ⟶ m.domain.toScheme) (x y z : T ⟶ domain.toScheme)
    (hx : a ≫ m.domain.ι ≫ pullback.fst f f = x ≫ domain.ι)
    (hy : a ≫ m.domain.ι ≫ pullback.snd f f = y ≫ domain.ι),
    a ≫ m.mul = z ≫ domain.ι →
    z ≫ embedding =
      (lift
          (Over.homMk (U := Over.mk (x ≫ domain.ι ≫ f)) (V := group.X) (x ≫ embedding)
            (by simp only [Over.mk_hom, Category.assoc, embedding_comp]))
          (Over.homMk (U := Over.mk (x ≫ domain.ι ≫ f)) (V := group.X) (y ≫ embedding)
            (by
              simp only [Over.mk_hom, Category.assoc, embedding_comp]
              rw [← reassoc_of% hy, ← reassoc_of% hx, pullback.condition]))
        ≫ μ[group.X]).left

end BirationalGroupLaw

end Langlands.AlgebraicGeometry
