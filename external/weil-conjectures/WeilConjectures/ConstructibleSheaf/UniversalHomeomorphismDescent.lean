/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.ConstructibleSheaf.StalkCardinality

/-!
# Constructibility descends along universal homeomorphisms

Let `u : Y' ⟶ Y` be a universal homeomorphism and `G` a sheaf of `Λ`-modules on `Y_ét`. If the
pullback `u^* G` is constructible, so is `G`
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_upperStar_of_isUniversalHomeomorphism`).

A stratification of `Y'` trivialising `u^* G` is carried by the homeomorphism `u` to a
stratification of `Y`, whose strata are realised by immersions into `Y`
(`AlgebraicGeometry.Scheme.exists_isImmersion_range_eq_of_isLocallyClosed'`: an open subscheme
followed by a reduced closed subscheme). Over each stratum `Z ⟶ Y`, the base change
`Z ×_Y Y' ⟶ Z` is again a universal homeomorphism, the pullback of `u^* G` to `Z ×_Y Y'` is
finite locally constant, its image being the corresponding stratum of `Y'`
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset`), and finite
local constancy descends along universal homeomorphisms
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_upperStar_of_isUniversalHomeomorphism`):
local constancy by `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_upperStar`, and the
stalks of a locally constant sheaf over a point all agree with the stalk at a geometric point
which lifts along `u`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

namespace Scheme

/-- **Locally closed subsets are realised by immersions**: every locally closed subset `C` of a
scheme `X` is the range of an immersion, namely the reduced closed subscheme structure on `C`
inside an open subscheme of `X` in which `C` is closed. -/
lemma exists_isImmersion_range_eq_of_isLocallyClosed' (X : Scheme.{u}) {C : Set X}
    (hC : IsLocallyClosed C) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsImmersion i ∧ Set.range i = C := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hC
  let V : X.Opens := ⟨U, hU⟩
  let W : TopologicalSpace.Closeds V := ⟨V.ι ⁻¹' Z, hZ.preimage V.ι.continuous⟩
  let I := IdealSheafData.vanishingIdeal W
  refine ⟨I.subscheme, I.subschemeι ≫ V.ι, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, IdealSheafData.range_subschemeι,
    IdealSheafData.coe_support_vanishingIdeal]
  change V.ι '' (V.ι ⁻¹' Z) = U ∩ Z
  rw [Set.image_preimage_eq_inter_range, Opens.range_ι]
  exact Set.inter_comm _ _

variable {Λ : Type (u + 1)} [Ring Λ]
variable {Y Y' : Scheme.{u}} (u : Y' ⟶ Y) [IsUniversalHomeomorphism u]

/-- **Finite local constancy descends along a universal homeomorphism** `u : Y' ⟶ Y`: local
constancy descends by `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_upperStar`, and the
stalk of the locally constant sheaf `G` at a geometric point over `y ∈ Y` is its stalk at the
geometric point `Spec κ(y')‾ ⟶ Y' ⟶ Y` for any `y'` over `y`, which is the stalk of `u^* G` at
`Spec κ(y')‾ ⟶ Y'`. -/
theorem IsFiniteLocallyConstantSheaf.of_upperStar_of_isUniversalHomeomorphism
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [hG : IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (u)).obj G)] :
    IsFiniteLocallyConstantSheaf G := by
  have : IsLocallyConstantSheaf G := IsLocallyConstantSheaf.of_upperStar u G
  refine { toIsLocallyConstantSheaf := this, toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ ?_⟩ }
  obtain ⟨y', hy'⟩ := u.surjective (s.base (IsLocalRing.closedPoint Ω))
  let t' := Y'.algClosurePoint y'
  have h₁ := hG.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber
    (AlgebraicClosure (Y'.residueField y')) t'
  have h₂ := h₁.of_iso ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) u t').app G)
  obtain ⟨e⟩ := Etale.nonempty_sheafFiber_iso_of_isLocallyConstantSheaf G s (t' ≫ u) (by
    rw [Scheme.Hom.comp_base, TopCat.comp_app, algClosurePoint_base, hy'])
  exact h₂.of_iso e.symm

/-- **Constructibility descends along a universal homeomorphism** `u : Y' ⟶ Y`: if `u^* G` is
constructible, so is `G`. The image under the homeomorphism `u` of a stratification of `Y'`
trivialising `u^* G` is a stratification of `Y` trivialising `G`. -/
theorem IsConstructibleSheaf.of_upperStar_of_isUniversalHomeomorphism
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [hG : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (u)).obj G)] :
    IsConstructibleSheaf G := by
  obtain ⟨S', hS'⟩ := hG.exists_stratification
  let h : Y' ≃ₜ Y := IsUniversalHomeomorphism.homeomorph u
  have hh : ∀ y', h y' = u y' := fun _ ↦ rfl
  have himage : ∀ s : Set Y', (u '' s) = h.symm ⁻¹' s := fun s ↦ by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    exact ⟨fun ⟨x, hx, hxy⟩ ↦ by rwa [← hxy, ← hh, Homeomorph.symm_apply_apply],
      fun hy ↦ ⟨h.symm y, hy, by rw [← hh, Homeomorph.apply_symm_apply]⟩⟩
  have hlc : ∀ i, IsLocallyClosed (u '' S'.stratum i) := fun i ↦ by
    rw [himage]
    exact (S'.isLocallyClosed_stratum i).preimage h.symm.continuous
  choose Z ι hι hrange using fun i ↦ exists_isImmersion_range_eq_of_isLocallyClosed' Y (hlc i)
  let S : Stratification Y :=
    { n := S'.n
      stratum i := u '' S'.stratum i
      isLocallyClosed_stratum := hlc
      isConstructible_stratum i := by
        rw [himage]
        exact (S'.isConstructible_stratum i).preimage_of_isOpenEmbedding
          h.symm.isOpenEmbedding
      iUnion_stratum_eq_univ := by
        rw [← Set.image_iUnion, S'.iUnion_stratum_eq_univ, Set.image_univ_of_surjective
          u.surjective]
      pairwise_disjoint_stratum i j hij := by
        change Disjoint (u '' S'.stratum i) (u '' S'.stratum j)
        rw [himage, himage]
        exact (S'.pairwise_disjoint_stratum hij).preimage _
      domain := Z
      immersion := ι
      isImmersion := hι
      range_immersion := hrange }
  refine ⟨⟨S, fun i ↦ ?_⟩⟩
  have : IsImmersion (ι i) := hι i
  -- the base change of `u` along the stratum `ι i` is a universal homeomorphism
  let p := pullback.fst (ι i) u
  let q := pullback.snd (ι i) u
  have hq : Set.range q ⊆ Set.range (S'.immersion i) := by
    rintro _ ⟨x, rfl⟩
    rw [S'.range_immersion]
    have : u (q x) ∈ Set.range (ι i) := ⟨p x, by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]⟩
    rw [hrange] at this
    obtain ⟨y', hy', hyy'⟩ := this
    rwa [← h.injective (hyy'.trans rfl : h y' = h (q x))]
  have : IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S'.immersion i)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (u)).obj G)) := hS' i
  have : IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (q)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (u)).obj G)) :=
    IsFiniteLocallyConstantSheaf.upperStar_of_range_subset q (S'.immersion i) hq _
  have : IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (p)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (ι i)).obj G)) :=
    IsFiniteLocallyConstantSheaf.of_iso (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) u).obj G))
      (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) q u).app G).symm ≪≫
        eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj G)
          pullback.condition.symm) ≪≫
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) p (ι i)).app G)
  exact IsFiniteLocallyConstantSheaf.of_upperStar_of_isUniversalHomeomorphism p _

end Scheme

end AlgebraicGeometry
