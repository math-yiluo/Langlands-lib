import Langlands.AbelianScheme.WeakNeronMappingProperty
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Models of abelian varieties on which relative translations extend -/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open NeronModelInfra

/-- Let `R` be a discrete valuation ring with fraction field `K`, `X` a scheme over `Spec R`
and `e` an isomorphism from an abelian variety `B` over `K` to the generic fibre of `X`. The
translation extension property says: for every smooth `R`-scheme `Z` and every `K`-morphism
`a : Z_K ⟶ B`, the morphism `(z, x) ↦ a(z) · x` of the generic fibre of `Z ×_R X` to the
generic fibre of `X` extends to an `R`-morphism `t` on an open subscheme `V` of `Z ×_R X`
which contains the generic fibre and meets every irreducible component of the closed
fibre, such that `(z, x) ↦ (z, t(z, x))` is a flat morphism `V ⟶ Z ×_R X`. -/
def TranslationExtensionProperty (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : AbelianScheme (Spec (CommRingCat.of K)))
    (X : Over (Spec (CommRingCat.of R)))
    (e : B.X ≅ (Over.pullback (specGenericFibreInclusion R K)).obj X) : Prop :=
  ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)), Smooth z →
    ∀ a : (Over.pullback (specGenericFibreInclusion R K)).obj (Over.mk z) ⟶ B.X,
      ∃ (V : (pullback z X.hom).Opens)
        (t : SchemeHomOver (V.ι ≫ pullback.fst z X.hom ≫ z) X.hom),
        (∀ x : ↑(pullback z X.hom),
          (pullback.fst z X.hom ≫ z).base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
        (∀ C ∈ irreducibleComponents
            {x : ↑(pullback z X.hom) //
              (pullback.fst z X.hom ≫ z).base x = IsLocalRing.closedPoint R},
          ∃ x ∈ C, x.1 ∈ V) ∧
        Flat (pullback.lift (V.ι ≫ pullback.fst z X.hom) t.1
          (by rw [t.2, Category.assoc]) : V.toScheme ⟶ pullback z X.hom) ∧
        ∀ (S : Scheme.{u}) (k : S ⟶ Spec (CommRingCat.of K)) (p : S ⟶ V.toScheme)
          (hp : p ≫ V.ι ≫ pullback.fst z X.hom ≫ z = k ≫ specGenericFibreInclusion R K),
          p ≫ t.1 =
            (lift
                (Over.homMk (U := Over.mk k)
                    (V := (Over.pullback (specGenericFibreInclusion R K)).obj (Over.mk z))
                    (pullback.lift (p ≫ V.ι ≫ pullback.fst z X.hom) k
                      (by simpa only [Over.mk_hom, Category.assoc] using hp))
                    (pullback.lift_snd _ _ _) ≫ a)
                (Over.homMk (U := Over.mk k)
                    (V := (Over.pullback (specGenericFibreInclusion R K)).obj X)
                    (pullback.lift (p ≫ V.ι ≫ pullback.snd z X.hom) k
                      (by
                        simp only [Category.assoc]
                        rw [← pullback.condition]
                        simpa only [Category.assoc] using hp))
                    (pullback.lift_snd _ _ _) ≫ e.inv)
              ≫ μ[B.X] ≫ e.hom).left ≫ pullback.fst X.hom (specGenericFibreInclusion R K)

/-- Let `B` be an abelian variety over the fraction field `K` of a discrete valuation ring
`R` with a smooth separated model `W` of finite type which has the weak Néron mapping
property. Then `B` has a smooth separated faithfully flat model `X` of finite type with
the translation extension property. -/
def TranslationExtensionModelStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) (W : Over (Spec (CommRingCat.of R))),
    Smooth W.hom → IsSeparated W.hom → LocallyOfFiniteType W.hom → QuasiCompact W.hom →
    Nonempty (B.X ≅ (Over.pullback (specGenericFibreInclusion R K)).obj W) →
    WeakNeronMappingProperty R K W.hom →
    ∃ (X : Over (Spec (CommRingCat.of R)))
      (e : B.X ≅ (Over.pullback (specGenericFibreInclusion R K)).obj X),
      Smooth X.hom ∧ IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
      Surjective X.hom ∧ TranslationExtensionProperty R K B X e

end Langlands.AbelianScheme
