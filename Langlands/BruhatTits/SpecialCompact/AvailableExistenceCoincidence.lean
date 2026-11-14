import Langlands.BruhatTits.SpecialCompact.AvailableExistenceStatement

/-!
# Torus coincidences forced by `AvailableSpecialMaximalCompactExistence`

`AvailableSpecialMaximalCompactExistence` uses one assignment `𝔅` for `G` and for every actual
standard Levi `Standard.leviScheme i ν J`, and prescribes the torus inclusion of the datum of
`𝔅` at each of these groups. The datum of an assignment depends only on the field and on the
group term. This module proves that the target therefore forces the prescribed torus inclusions
to agree whenever two of these group terms are equal.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- The data of an assignment at two equal group terms have heterogeneously equal torus
inclusions, whatever the instance and reductivity proofs. -/
theorem heq_datum_base_i_of_eq (𝔅 : KPBuildingAssignment.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G₁.X.hom]
    [IsAffineHom G₂.X.hom] (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (h : G₁ = G₂) :
    HEq (𝔅.datum F G₁ hG₁).base.i (𝔅.datum F G₂ hG₂).base.i := by
  subst h
  rfl

/-- `AvailableSpecialMaximalCompactExistence` implies: if two actual standard Levi subgroups
`Standard.leviScheme i ν J₁` and `Standard.leviScheme i ν J₂` are equal as terms, then their
torus inclusions `Standard.leviTorusHom i ν J₁` and `Standard.leviTorusHom i ν J₂` are
heterogeneously equal. -/
theorem heq_leviTorusHom_of_availableSpecialMaximalCompactExistence
    (h : AvailableSpecialMaximalCompactExistence.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ J₁ ⊆ simpleRelativeRoots i ν, ∀ J₂ ⊆ simpleRelativeRoots i ν,
        Standard.leviScheme i ν J₁ = Standard.leviScheme i ν J₂ →
          HEq (Standard.leviTorusHom i ν J₁) (Standard.leviTorusHom i ν J₂) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro hν J₁ hJ₁ J₂ hJ₂ hM
  obtain ⟨𝔅, D, -, -, -, -, x, -, -, hL⟩ := h F G hG S i hi ν hν
  obtain ⟨hM₁, -, -, -, hi₁, -⟩ := hL J₁ hJ₁
  obtain ⟨hM₂, -, -, -, hi₂, -⟩ := hL J₂ hJ₂
  have : IsAffineHom (Standard.leviScheme i ν J₁).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J₁).isAffineHom
  have : IsAffineHom (Standard.leviScheme i ν J₂).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J₂).isAffineHom
  exact hi₁.symm.trans ((heq_datum_base_i_of_eq 𝔅 F hM₁ hM₂ hM).trans hi₂)

/-- `AvailableSpecialMaximalCompactExistence` implies: if `G` is equal as a term to an actual
standard Levi `Standard.leviScheme i ν J`, then `i` and `Standard.leviTorusHom i ν J` are
heterogeneously equal. -/
theorem heq_torusHom_of_eq_leviScheme_of_availableSpecialMaximalCompactExistence
    (h : AvailableSpecialMaximalCompactExistence.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ J ⊆ simpleRelativeRoots i ν,
        G = Standard.leviScheme i ν J → HEq i (Standard.leviTorusHom i ν J) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro hν J hJ hGM
  obtain ⟨𝔅, D, -, -, hiG, -, x, -, -, hL⟩ := h F G hG S i hi ν hν
  obtain ⟨hM, -, -, -, hiM, -⟩ := hL J hJ
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  exact hiG.symm.trans ((heq_datum_base_i_of_eq 𝔅 F hG hM hGM).trans hiM)

end Langlands.BruhatTits.SpecialCompact
