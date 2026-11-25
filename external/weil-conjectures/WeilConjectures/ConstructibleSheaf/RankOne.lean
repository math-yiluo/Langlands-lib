/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.ConstructibleSheaf.InternalHom

/-!
# Automorphisms of a locally constant sheaf of rank one

Let `Λ` be a commutative ring and let `L` be a locally constant sheaf of `Λ`-modules on the small
étale site of a scheme `X`, of rank one: its stalk at every geometric point is isomorphic to `Λ`
(`AlgebraicGeometry.Scheme.HasRankOneStalks`). Then (blueprint `lemma-section-normal-bundle--1`):

1. the canonical map `Λ_X ⟶ [L, L]` (`CategoryTheory.MonoidalClosed.id`, the adjoint of the right
   unitor, "`1 ↦ id_L`") is an isomorphism
   (`AlgebraicGeometry.Scheme.isIso_id_of_hasRankOneStalks`): on a trivialising cover, pullback
   commuting with internal homs, it is the canonical map `Λ ⟶ [Λ, Λ]`. Hence every endomorphism
   of `L` is the multiplication by a unique endomorphism of `Λ_X`, that is by a unique global
   section of `Λ_X`, a locally constant function `X → Λ`
   (`AlgebraicGeometry.Scheme.unitEndRingEquivOfHasRankOneStalks`), and the automorphisms of `L`
   are the units of `End Λ_X`
   (`AlgebraicGeometry.Scheme.unitsUnitEndMulEquivAutOfHasRankOneStalks`);
2. two isomorphisms `φ ψ : L ≅ M` of such sheaves differ by a unique unit of `End Λ_X`
   (`AlgebraicGeometry.Scheme.existsUnique_hom_eq_comp_unitEndAction_of_hasRankOneStalks`); for a
   unit `v` of `Λ`, the constant unit, `v • φ` is an isomorphism whose stalks are `v` times those
   of `φ` (`AlgebraicGeometry.Scheme.exists_iso_hom_eq_smul`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Functor.LaxMonoidal

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- A sheaf of `Λ`-modules on `X_ét` *has rank one stalks* if its stalk at every geometric point
of `X` is isomorphic to `Λ`. -/
def HasRankOneStalks (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
    Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)

/-- A constant sheaf on a nonempty scheme whose stalks are `Λ` is isomorphic to `Λ_Y`. -/
lemma nonempty_constantSheaf_iso_unit_of_hasRankOneStalks {Y : Scheme.{u}} [Nonempty Y]
    (P : ModuleCat.{u + 1} Λ)
    (hP : HasRankOneStalks ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj P)) :
    Nonempty ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj P ≅
      𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let y : Y := Classical.arbitrary _
  let s : Spec (.of (SeparableClosure (Y.residueField y))) ⟶ Y :=
    (SpecToEquivOfField (SeparableClosure (Y.residueField y)) _).2
      ⟨y, CommRingCat.ofHom (algebraMap (Y.residueField y) _)⟩
  obtain ⟨e⟩ := hP _ s
  exact ⟨(constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
    (((pointSmallEtale s).sheafFiberConstantSheafIso P).symm ≪≫ e) ≪≫
      (Functor.Monoidal.εIso (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm⟩

/-- Rank one stalks are preserved by pullback. -/
lemma HasRankOneStalks.upperStar {Y : Scheme.{u}} (g : Y ⟶ X)
    {L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hL : HasRankOneStalks L) :
    HasRankOneStalks ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj L) := fun Ω _ _ t ↦
  let ⟨e⟩ := hL Ω (t ≫ g)
  ⟨(Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g t).app L ≪≫ e⟩

/-- Rank one stalks are invariant under isomorphism. -/
lemma HasRankOneStalks.of_iso {L L' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (i : L ≅ L') (hL : HasRankOneStalks L) : HasRankOneStalks L' := fun Ω _ _ s ↦
  let ⟨e⟩ := hL Ω s
  ⟨(pointSmallEtale s).sheafFiber.mapIso i.symm ≪≫ e⟩

variable (L M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- Blueprint `lemma-section-normal-bundle--1`: Automorphisms of a rank-one finite locally constant
sheaf

Clause (1): for a locally constant sheaf `L` of rank one, the canonical map
`Λ_X ⟶ [L, L]`, `1 ↦ id_L` (`CategoryTheory.MonoidalClosed.id`), is an isomorphism. On a
trivialising cover with nonempty members, `L` is a constant sheaf with stalks `Λ`, hence
isomorphic to `Λ`, for which the canonical map is an isomorphism; and the pullback, which is
strong monoidal and commutes with internal homs, carries the canonical map of `L` to the
canonical map of its pullback. -/
theorem isIso_id_of_hasRankOneStalks [IsLocallyConstantSheaf L] (hL : HasRankOneStalks L) :
    IsIso (MonoidalClosed.id L) := by
  obtain ⟨⟨𝒰₀, h𝒰₀⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := L)
  refine Etale.isIso_of_isIso_upperStar_map_of_cover 𝒰₀.nonemptyMembers _ fun i ↦ ?_
  set g := 𝒰₀.nonemptyMembers.f i
  have : Etale g := 𝒰₀.map_prop i.1
  have hc : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj L).IsConstant
      (𝒰₀.nonemptyMembers.X i).smallEtaleTopology :=
    (isConstant_over_iff_upperStar _ (𝒰₀.etalePrecoverageToEtale i.1) L).1 (h𝒰₀ i.1)
  obtain ⟨P, ⟨eP⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj L).mem_essImage_of_isConstant
  obtain ⟨e⟩ := nonempty_constantSheaf_iso_unit_of_hasRankOneStalks P
    ((hL.upperStar g).of_iso eP.symm)
  have := isIso_id_of_iso (e.symm ≪≫ eP)
  have := Etale.isIso_ihomComparison_upperStar (ModuleCat.{u + 1} Λ) g L
  exact isIso_map_id _ L

variable {L M}

/-- Blueprint `lemma-section-normal-bundle--1`: Automorphisms of a rank-one finite locally constant
sheaf

Clause (1), endomorphisms: every endomorphism of a locally constant sheaf `L` of rank one is the
multiplication (`CategoryTheory.MonoidalCategory.unitEndAction`) by a unique endomorphism of
`Λ_X`, that is by a unique global section of `Λ_X`, a locally constant function `X → Λ`: the
action `End Λ_X → End L` is a ring isomorphism. -/
noncomputable def unitEndRingEquivOfHasRankOneStalks [IsLocallyConstantSheaf L]
    (hL : HasRankOneStalks L) :
    End (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ≃+* End L :=
  have := isIso_id_of_hasRankOneStalks L hL
  have := MonoidalClosed.monoidalPreadditive_of_braided
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  unitEndRingEquiv L

/-- Blueprint `lemma-section-normal-bundle--1`: Automorphisms of a rank-one finite locally constant
sheaf

Clause (1), automorphisms: the automorphisms of a locally constant sheaf `L` of rank one are the
multiplications by the units of `End Λ_X`, the locally constant functions `X → Λˣ`. -/
noncomputable def unitsUnitEndMulEquivAutOfHasRankOneStalks [IsLocallyConstantSheaf L]
    (hL : HasRankOneStalks L) :
    (End (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))ˣ ≃* Aut L :=
  have := isIso_id_of_hasRankOneStalks L hL
  unitsUnitEndMulEquivAut L

/-- Blueprint `lemma-section-normal-bundle--1`: Automorphisms of a rank-one finite locally constant
sheaf

Clause (2): two isomorphisms `φ ψ : L ≅ M` between locally constant sheaves of rank one differ
by a unique unit `u` of `End Λ_X`, a locally constant function `X → Λˣ`: `ψ = u • φ`. -/
theorem existsUnique_hom_eq_comp_unitEndAction_of_hasRankOneStalks [IsLocallyConstantSheaf M]
    (hM : HasRankOneStalks M) (φ ψ : L ≅ M) :
    ∃! u : (End (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))ˣ,
      ψ.hom = φ.hom ≫ (unitEndAction M u).asHom :=
  have := isIso_id_of_hasRankOneStalks M hM
  existsUnique_hom_eq_comp_unitEndAction φ ψ

/-- Blueprint `lemma-section-normal-bundle--1`: Automorphisms of a rank-one finite locally constant
sheaf

The final assertion of clause (2): for an isomorphism `φ : L ≅ M` and a unit `v` of `Λ`, the
multiple `v • φ` by the constant unit `v` is an isomorphism, whose stalk at every geometric point
is `v` times the stalk of `φ`. -/
theorem exists_iso_hom_eq_smul (φ : L ≅ M) (v : Λˣ) :
    ∃ ψ : L ≅ M, ψ.hom = (v : Λ) • φ.hom ∧
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        (pointSmallEtale s).sheafFiber.map ψ.hom =
          (v : Λ) • (pointSmallEtale s).sheafFiber.map φ.hom := by
  refine ⟨⟨(v : Λ) • φ.hom, ((v⁻¹ : Λˣ) : Λ) • φ.inv, ?_, ?_⟩, rfl, fun Ω _ _ s ↦ ?_⟩
  · rw [Linear.smul_comp, Linear.comp_smul, φ.hom_inv_id, smul_smul, Units.mul_inv, one_smul]
  · rw [Linear.smul_comp, Linear.comp_smul, φ.inv_hom_id, smul_smul, Units.inv_mul, one_smul]
  · exact (pointSmallEtale s).sheafFiber_map_smul (v : Λ) φ.hom

end AlgebraicGeometry.Scheme
