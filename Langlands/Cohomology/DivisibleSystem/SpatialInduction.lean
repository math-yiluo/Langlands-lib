import Langlands.Cohomology.DivisibleSystem
import Langlands.Sheaf.Equivariant.SmoothSpatialLocallyConstant

/-!
# `ℓ`-divisible systems under equivalences and spatial induction

Harris 1999, §2 works with `ℓ`-divisible systems of smooth `S(ẽ)`-modules over `U(ẽ)`, where
the compact open subgroup `S(ẽ) ⊂ GJ` stabilizes `U(ẽ)`. This module transports
`ℓ`-divisible systems along equivalences of abelian categories, and specializes to the
Library's equivalence between smooth sheaves on an induced space `G ×ᴴ X` and on `X`.

* `isoMk`: an isomorphism of `ℓ`-divisible systems from an isomorphism of the underlying
  inverse systems commuting with the maps `i`.
* `mapFunctor_map_tower`: the components of the parent module's `mapFunctor C ℓ F` on a
  morphism of systems are those of `F`.
* `equivalence_functor_additive`: the functor of an equivalence of abelian categories is
  additive (the inverse is then additive by Mathlib's `Equivalence.inverse_additive`).
* `mapEquivalence ℓ e`: an equivalence `e : C ≌ D` of abelian categories induces an
  equivalence of the categories of `ℓ`-divisible systems, levelwise `e.functor` and
  `e.inverse`, with unit and counit levelwise those of `e`.
* `smoothRestrictionSystemEquivalence R H hH X ℓ`: for an open subgroup `H` of `G` and an
  `H`-space `X` with stable neighbourhoods, `ℓ`-divisible systems of `G`-equivariant smooth
  sheaves on `G ×ᴴ X` are equivalent to `ℓ`-divisible systems of `H`-equivariant smooth
  sheaves on `X`, by restriction to the unit chart and smooth spatial induction.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

section Equivalence

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {ℓ : ℕ}

/-- An isomorphism of `ℓ`-divisible systems from an isomorphism of the underlying inverse
systems commuting with the maps `i`. -/
@[simps]
def isoMk {T T' : DivisibleSystem C ℓ} (e : T.tower ≅ T'.tower)
    (he : ∀ {m' m : ℕ} (h : m' < m),
      T.inclusion h ≫ e.hom.app (op m) = e.hom.app (op m') ≫ T'.inclusion h) :
    T ≅ T' where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, fun h => by
    rw [← cancel_mono (e.hom.app (op _)), Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, Category.assoc, he, Iso.inv_hom_id_app_assoc]⟩
  hom_inv_id := hom_ext e.hom_inv_id
  inv_hom_id := hom_ext e.inv_hom_id

@[simp]
lemma mapFunctor_map_tower (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {T T' : DivisibleSystem C ℓ} (f : T ⟶ T') :
    ((mapFunctor C ℓ F).map f).tower = Functor.whiskerRight f.tower F :=
  rfl

/-- The functor of an equivalence of abelian categories is additive. -/
instance equivalence_functor_additive (e : C ≌ D) : e.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

variable (ℓ) in
/-- An equivalence of abelian categories induces an equivalence of the categories of
`ℓ`-divisible systems, levelwise. -/
@[simps functor inverse]
def mapEquivalence (e : C ≌ D) : DivisibleSystem C ℓ ≌ DivisibleSystem D ℓ where
  functor := mapFunctor C ℓ e.functor
  inverse := mapFunctor D ℓ e.inverse
  unitIso := NatIso.ofComponents
    (fun T => isoMk (Functor.isoWhiskerLeft T.tower e.unitIso)
      (fun h => e.unit.naturality (T.inclusion h)))
    (fun f => hom_ext (by ext m; exact e.unit.naturality (f.tower.app m)))
  counitIso := NatIso.ofComponents
    (fun T => isoMk (Functor.isoWhiskerLeft T.tower e.counitIso)
      (fun h => e.counit.naturality (T.inclusion h)))
    (fun f => hom_ext (by ext m; exact e.counit.naturality (f.tower.app m)))
  functor_unitIso_comp T := hom_ext (by ext m; exact e.functor_unit_comp (T.tower.obj m))

@[simp]
lemma mapEquivalence_unitIso_hom_app_tower_app (e : C ≌ D) (T : DivisibleSystem C ℓ)
    (m : ℕᵒᵖ) :
    ((mapEquivalence ℓ e).unitIso.hom.app T).tower.app m = e.unitIso.hom.app (T.tower.obj m) :=
  rfl

@[simp]
lemma mapEquivalence_unitIso_inv_app_tower_app (e : C ≌ D) (T : DivisibleSystem C ℓ)
    (m : ℕᵒᵖ) :
    ((mapEquivalence ℓ e).unitIso.inv.app T).tower.app m = e.unitIso.inv.app (T.tower.obj m) :=
  rfl

@[simp]
lemma mapEquivalence_counitIso_hom_app_tower_app (e : C ≌ D) (T : DivisibleSystem D ℓ)
    (m : ℕᵒᵖ) :
    ((mapEquivalence ℓ e).counitIso.hom.app T).tower.app m =
      e.counitIso.hom.app (T.tower.obj m) :=
  rfl

@[simp]
lemma mapEquivalence_counitIso_inv_app_tower_app (e : C ≌ D) (T : DivisibleSystem D ℓ)
    (m : ℕᵒᵖ) :
    ((mapEquivalence ℓ e).counitIso.inv.app T).tower.app m =
      e.counitIso.inv.app (T.tower.obj m) :=
  rfl

end Equivalence

section SpatialInduction

open Langlands.Sheaf.Equivariant Langlands.TopologicalInduction

variable (R : Type u) [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))
  (X : Type u) [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]
  [HasStableNeighbourhoods H X] (ℓ : ℕ)

/-- Restriction to the unit chart is an equivalence between `ℓ`-divisible systems of
`G`-equivariant smooth sheaves on the induced space `G ×ᴴ X` and `ℓ`-divisible systems of
`H`-equivariant smooth sheaves on `X`; the inverse is smooth spatial induction, levelwise. -/
def smoothRestrictionSystemEquivalence :
    (letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
     SmoothSheafDivisibleSystem R G (Space H X) ℓ) ≌ SmoothSheafDivisibleSystem R H X ℓ :=
  letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
  mapEquivalence ℓ (SpatialInduction.smoothRestrictionEquivalence R H hH X)

@[simp]
lemma smoothRestrictionSystemEquivalence_functor_obj_tower
    (T : letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
      SmoothSheafDivisibleSystem R G (Space H X) ℓ) :
    letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
    ((smoothRestrictionSystemEquivalence R H hH X ℓ).functor.obj T).tower =
      T.tower ⋙ SpatialInduction.smoothRestrict R H hH X :=
  rfl

@[simp]
lemma smoothRestrictionSystemEquivalence_inverse_obj_tower
    (T : SmoothSheafDivisibleSystem R H X ℓ) :
    letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
    ((smoothRestrictionSystemEquivalence R H hH X ℓ).inverse.obj T).tower =
      T.tower ⋙ SpatialInduction.smoothInduce R H hH X :=
  rfl

end SpatialInduction

end Langlands.Cohomology.DivisibleSystem
