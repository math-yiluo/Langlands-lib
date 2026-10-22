import Langlands.Cohomology.Tate.Reindex

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]
variable {K H : Subgroup G} (h : K ≤ H)

/-- Identity on coefficients, with the two subgroup coordinates made explicit. -/
def towerCoefficientIso (A : Rep.{u} R G) :
    Rep.res (Subgroup.subgroupOfEquivOfLe h).toMonoidHom (Rep.res K.subtype A) ≅
      Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype A) :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl R A) (fun _ => rfl))

/-- The coefficient identification applies to all terms of a short complex. -/
def towerSequenceMap (S : ShortComplex (Rep.{u} R G)) :
    (S.map (Rep.resFunctor K.subtype)).map
        (Rep.resFunctor (Subgroup.subgroupOfEquivOfLe h).toMonoidHom) ⟶
      (S.map (Rep.resFunctor H.subtype)).map (Rep.resFunctor (K.subgroupOf H).subtype) where
  τ₁ := (towerCoefficientIso h S.X₁).hom
  τ₂ := (towerCoefficientIso h S.X₂).hom
  τ₃ := (towerCoefficientIso h S.X₃).hom
  comm₁₂ := by ext a; rfl
  comm₂₃ := by ext a; rfl

variable [Fintype G] [Fintype K] [Fintype H] [Fintype (K.subgroupOf H)]

/-- The canonical group identification acts on actual Tate cohomology by a proved chain map. -/
def towerReindex (A : Rep.{u} R G) (n : ℤ) :
    tateCohomology (Rep.res K.subtype A) n ≅
      tateCohomology (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype A)) n :=
  reindexIso (Subgroup.subgroupOfEquivOfLe h).symm (towerCoefficientIso h A) n

end Langlands.Tate
