import Langlands.AbelianScheme.TranslationExtensionModelStatement

/-! # The open part of a weak Néron model on which extended translations are flat -/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open NeronModelInfra

/-- Let `R` be a discrete valuation ring with fraction field `K`, `B` an abelian variety over
`K`, and `W` a smooth, separated, quasi-compact `R`-scheme of finite type with the weak Néron
mapping property and an isomorphism `e : B ≅ W_K` over `K`. Then `W` has an open subscheme
`U` which contains the generic fibre of `W` and meets the closed fibre, such that for every
smooth `R`-scheme `Z`, every `K`-morphism `a : Z_K ⟶ B`, every open subscheme `V` of
`Z ×_R U` and every `R`-morphism `v : V ⟶ W` whose restriction to the generic fibre is
`(z, x) ↦ e (a(z) · e⁻¹(x))`, the morphism `v` takes values in `U` and
`(z, x) ↦ (z, v(z, x))` is a flat morphism `V ⟶ Z ×_R W`. -/
def OmegaMinimalOpenStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) (W : Over (Spec (CommRingCat.of R))),
    Smooth W.hom → IsSeparated W.hom → LocallyOfFiniteType W.hom → QuasiCompact W.hom →
    ∀ e : B.X ≅ (Over.pullback (specGenericFibreInclusion R K)).obj W,
    WeakNeronMappingProperty R K W.hom →
    ∃ U : W.left.Opens,
      (∀ w : W.left, W.hom.base w ≠ IsLocalRing.closedPoint R → w ∈ U) ∧
      (∃ w ∈ U, W.hom.base w = IsLocalRing.closedPoint R) ∧
      ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)), Smooth z →
        ∀ (a : (Over.pullback (specGenericFibreInclusion R K)).obj (Over.mk z) ⟶ B.X)
          (V : (pullback z (U.ι ≫ W.hom)).Opens)
          (v : SchemeHomOver (V.ι ≫ pullback.fst z (U.ι ≫ W.hom) ≫ z) W.hom),
          (∀ (S : Scheme.{u}) (k : S ⟶ Spec (CommRingCat.of K)) (p : S ⟶ V.toScheme)
            (hp : p ≫ V.ι ≫ pullback.fst z (U.ι ≫ W.hom) ≫ z =
              k ≫ specGenericFibreInclusion R K),
            p ≫ v.1 =
              (lift
                  (Over.homMk (U := Over.mk k)
                      (V := (Over.pullback (specGenericFibreInclusion R K)).obj (Over.mk z))
                      (pullback.lift (p ≫ V.ι ≫ pullback.fst z (U.ι ≫ W.hom)) k
                        (by simpa only [Over.mk_hom, Category.assoc] using hp))
                      (pullback.lift_snd _ _ _) ≫ a)
                  (Over.homMk (U := Over.mk k)
                      (V := (Over.pullback (specGenericFibreInclusion R K)).obj W)
                      (pullback.lift (p ≫ V.ι ≫ pullback.snd z (U.ι ≫ W.hom) ≫ U.ι) k
                        (by
                          simp only [Category.assoc]
                          rw [← pullback.condition]
                          simpa only [Category.assoc] using hp))
                      (pullback.lift_snd _ _ _) ≫ e.inv)
                ≫ μ[B.X] ≫ e.hom).left ≫ pullback.fst W.hom (specGenericFibreInclusion R K)) →
          (∀ y : V.toScheme, v.1.base y ∈ U) ∧
            Flat (pullback.lift (V.ι ≫ pullback.fst z (U.ι ≫ W.hom)) v.1
              (by rw [v.2, Category.assoc]) : V.toScheme ⟶ pullback z W.hom)

end Langlands.AbelianScheme
