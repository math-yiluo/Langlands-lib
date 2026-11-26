import Langlands.AbelianScheme.Basic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

/-! # The weak Néron mapping property -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open NeronModelInfra

/-- A scheme `w : W ⟶ Spec R` over a discrete valuation ring has the weak Néron mapping
property when every morphism of generic fibres from a smooth `R`-scheme `T` extends to an
`R`-morphism on an open subscheme of `T` which contains the generic fibre and meets every
irreducible component of the closed fibre. -/
def WeakNeronMappingProperty (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra R K] {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t →
    ∀ uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
        (pullback.snd w (specGenericFibreInclusion R K)),
      ∃ (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) w),
        (∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
        (∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R},
          ∃ x ∈ Z, x.1 ∈ V) ∧
        (genericFibreRestrict R K w (V.ι ≫ t) v).1 =
          pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t
              (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
              ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1

/-- Every abelian variety over the fraction field of a discrete valuation ring has a
smooth separated model of finite type with the weak Néron mapping property. -/
def WeakNeronModelExistenceStatement : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (B : AbelianScheme (Spec (CommRingCat.of K))),
    ∃ W : Over (Spec (CommRingCat.of V)),
      Smooth W.hom ∧ IsSeparated W.hom ∧ LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom ∧
      Nonempty (B.X ≅ (Over.pullback (specGenericFibreInclusion V K)).obj W) ∧
      WeakNeronMappingProperty V K W.hom

end Langlands.AbelianScheme
