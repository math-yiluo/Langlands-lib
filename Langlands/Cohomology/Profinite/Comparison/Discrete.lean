import Langlands.Cohomology.Profinite.Functoriality

/-!
# Comparison with the cohomology of an abstract group

The inclusion of locally constant cochains into all inhomogeneous cochains induces
`toGroupCohomology A n : cohomology A n ⟶ groupCohomology A n`, natural in the group and the
coefficients (`map_comp_toGroupCohomology`, with the special cases for restriction and
inflation). When `G` is discrete every cochain is locally constant, so the inclusion of
complexes is an isomorphism and `isoGroupCohomology A n : cohomology A n ≅ groupCohomology A n`.
-/

namespace Langlands.ProfiniteCohomology

open CategoryTheory groupCohomology

universe u

variable {k G H : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

section Comparison


variable (A : Rep.{u} k G) [IsSmoothRep A]

noncomputable def toGroupCohomology (n : ℕ) : cohomology A n ⟶ groupCohomology A n :=
  HomologicalComplex.homologyMap (cochainsι A) n

instance isIso_cochainsι [DiscreteTopology G] : IsIso (cochainsι A) := by
  have : ∀ n, IsIso ((cochainsι A).f n) := fun n => by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨Subtype.val_injective, fun c => ⟨⟨c, IsLocallyConstant.of_discrete c⟩, rfl⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

noncomputable def isoGroupCohomology [DiscreteTopology G] (n : ℕ) :
    cohomology A n ≅ groupCohomology A n :=
  HomologicalComplex.homologyMapIso (asIso (cochainsι A)) n

theorem isoGroupCohomology_hom [DiscreteTopology G] (n : ℕ) :
    (isoGroupCohomology A n).hom = toGroupCohomology A n :=
  rfl

end Comparison

section Naturality

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsSmoothRep A] [IsSmoothRep B]
  (φ : H →ₜ* G) (f : Rep.res (φ : H →* G) A ⟶ B)

/-- The comparison with `groupCohomology` is natural in the group and the coefficients. -/
@[reassoc]
theorem map_comp_toGroupCohomology (n : ℕ) :
    map φ f n ≫ toGroupCohomology B n =
      toGroupCohomology A n ≫ groupCohomology.map (φ : H →* G) f n := by
  have h := congrArg (fun ψ => HomologicalComplex.homologyMap ψ n)
    (cochainsMap_comp_cochainsι φ f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

omit [IsSmoothRep A] [IsSmoothRep B] in
@[reassoc]
theorem map_id_comp_toGroupCohomology {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (f : A ⟶ B) (n : ℕ) :
    map (.id G) f n ≫ toGroupCohomology B n =
      toGroupCohomology A n ≫ groupCohomology.map (MonoidHom.id G) f n :=
  map_comp_toGroupCohomology (.id G) f n

variable (A)

@[reassoc]
theorem res_comp_toGroupCohomology (S : Subgroup G) (n : ℕ) :
    res A S n ≫ toGroupCohomology (Rep.res S.subtype A) n =
      toGroupCohomology A n ≫ groupCohomology.map S.subtype (𝟙 _) n :=
  map_comp_toGroupCohomology _ _ n

@[reassoc]
theorem infl_comp_toGroupCohomology (N : Subgroup G) [N.Normal] (n : ℕ) :
    infl A N n ≫ toGroupCohomology A n =
      toGroupCohomology (A.quotientToInvariants N) n ≫
        groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n :=
  map_comp_toGroupCohomology _ _ n

end Naturality

end Langlands.ProfiniteCohomology
