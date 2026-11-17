import Langlands.Sheaf.Equivariant.TwistedFreeRepresentableFinite
import Langlands.Cohomology.SiteCech.EquivariantThreeTermModel

/-! # Signed finite boundaries and equivariant cochain models -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Cohomology.SiteCech
open scoped BigOperators

universe u v z w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type z} [Group G] [TopologicalSpace G]
variable {ρ : G →* Aut X}
variable (J : GrothendieckTopology (P.Over ⊤ X))
variable [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [LocallySmall.{w} (P.Over ⊤ X)]
variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]
variable (S : LocalActionSystem (TwistedOver P ρ) G)
variable [S.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable (hS : S.IsLiftSystem)

local instance (m : ℕ) :
    HasColimitsOfShape (Discrete (Fin m)) (Sheaf J (ModuleCat.{w} R)) :=
  Sheaf.instHasColimitsOfShape

/-- The finite coproduct of the ordinary free representable sheaves. -/
abbrev ordinaryFreeSheafSum {m : ℕ}
    (L : Fin m → GlobalLift (P := P) (ρ := ρ)) : Sheaf J (ModuleCat.{w} R) :=
  ∐ (fun i => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (L i).obj))

/-- Finite integer coefficients and whole-group equivariant arrows specify
a signed boundary between two finite families of lifted objects. -/
structure SignedBoundary {m k : ℕ}
    (L : Fin m → GlobalLift (P := P) (ρ := ρ))
    (M : Fin k → GlobalLift (P := P) (ρ := ρ)) where
  length : ℕ
  coefficient : Fin length → ℤ
  indexMap : Fin length → Fin m → Fin k
  arrow : ∀ t i, (L i).obj ⟶ (M (indexMap t i)).obj
  equivariant : ∀ t i, IsEquivariant (L := L i)
    (M := M (indexMap t i)) (arrow t i)

variable {m k : ℕ}
variable {L : Fin m → GlobalLift (P := P) (ρ := ρ)}
variable {M : Fin k → GlobalLift (P := P) (ρ := ρ)}

/-- The ordinary free-sheaf boundary with the specified integer coefficients. -/
def SignedBoundary.ordinaryMap (b : SignedBoundary L M) :
    (∐ (fun i => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (L i).obj))) ⟶
      ∐ (fun j => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (M j).obj)) :=
  ∑ t, b.coefficient t • Sigma.map' (b.indexMap t)
    (fun i => (freeSheafFunctor J R).map (shrinkYoneda.{w}.map (b.arrow t i)))

/-- The same signed boundary in the actual discrete sheaf category. -/
def SignedBoundary.discreteMap (b : SignedBoundary L M)
    (hL : ∀ i, (L i).EventuallyEquivariant S)
    (hM : ∀ j, (M j).EventuallyEquivariant S) :
    discreteFreeSheafSum J R S hS L hL ⟶ discreteFreeSheafSum J R S hS M hM :=
  ∑ t, b.coefficient t • discreteFreeSheafSumMap J R S hS L M hL hM
    (b.indexMap t) (b.arrow t) (b.equivariant t)

/-- Additive restriction carries the signed boundary to the specified ordinary
boundary, with the previously fixed finite-sum comparison isomorphisms. -/
theorem SignedBoundary.discreteMap_restriction (b : SignedBoundary L M)
    (hL : ∀ i, (L i).EventuallyEquivariant S)
    (hM : ∀ j, (M j).EventuallyEquivariant S) :
    (discreteFreeSheafSumRestrictionIso J R S hS L hL).inv ≫
        (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
          restriction ρ J (ModuleCat.{w} R)).map (b.discreteMap J R S hS hL hM) =
      b.ordinaryMap J R ≫ (discreteFreeSheafSumRestrictionIso J R S hS M hM).inv := by
  dsimp only [SignedBoundary.discreteMap, SignedBoundary.ordinaryMap]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro t _
  rw [discreteFreeSheafSumMap_restriction]

/-- The signed restriction square in the forward comparison direction. -/
theorem SignedBoundary.discreteMap_restriction_hom (b : SignedBoundary L M)
    (hL : ∀ i, (L i).EventuallyEquivariant S)
    (hM : ∀ j, (M j).EventuallyEquivariant S) :
    (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)).map (b.discreteMap J R S hS hL hM) ≫
        (discreteFreeSheafSumRestrictionIso J R S hS M hM).hom =
      (discreteFreeSheafSumRestrictionIso J R S hS L hL).hom ≫ b.ordinaryMap J R := by
  apply (cancel_epi (discreteFreeSheafSumRestrictionIso J R S hS L hL).inv).1
  rw [← Category.assoc, b.discreteMap_restriction J R S hS hL hM, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- A fixed family representing a given ordinary finite cochain lifts that
precise cochain through ordinary restriction. -/
theorem discreteFreeSheafSumLift_restricts_cochain
    (hL : ∀ i, (L i).EventuallyEquivariant S)
    (F : S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (x : (∐ (fun i => (freeSheafFunctor J R).obj
      (shrinkYoneda.{w}.obj (L i).obj))) ⟶
        (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
          restriction ρ J (ModuleCat.{w} R)).obj F)
    (s : ∀ i, (L i).FixedSections (F.obj.obj ⋙ forget (ModuleCat.{w} R)))
    (hs : ∀ i, (s i).val = freeRepresentableHomEquiv J R (L i).obj
      ((S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)).obj F)
      (Sigma.ι (fun j => (freeSheafFunctor J R).obj
        (shrinkYoneda.{w}.obj (L j).obj)) i ≫ x)) :
    (discreteFreeSheafSumRestrictionIso J R S hS L hL).inv ≫
        (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
          restriction ρ J (ModuleCat.{w} R)).map
          (discreteFreeSheafSumLift J R S hS L hL F s) = x := by
  rw [discreteFreeSheafSumLift_restricts]
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc, hs i, Equiv.symm_apply_apply]

/-- Three finite lifted families whose specified ordinary signed boundaries
agree with the two differentials of the chosen ordinary chain segment. -/
structure FiniteFreeThreeTermModel
    (Q : ChainComplex (Sheaf J (ModuleCat.{w} R)) ℕ) (n : ℕ) where
  upperSize : ℕ
  middleSize : ℕ
  lowerSize : ℕ
  upper : Fin upperSize → GlobalLift (P := P) (ρ := ρ)
  middle : Fin middleSize → GlobalLift (P := P) (ρ := ρ)
  lower : Fin lowerSize → GlobalLift (P := P) (ρ := ρ)
  upper_eventuallyEquivariant : ∀ i, (upper i).EventuallyEquivariant S
  middle_eventuallyEquivariant : ∀ i, (middle i).EventuallyEquivariant S
  lower_eventuallyEquivariant : ∀ i, (lower i).EventuallyEquivariant S
  upperBoundary : SignedBoundary upper middle
  lowerBoundary : SignedBoundary middle lower
  upperIso : ordinaryFreeSheafSum J R upper ≅ Q.X (n + 2)
  middleIso : ordinaryFreeSheafSum J R middle ≅ Q.X (n + 1)
  lowerIso : ordinaryFreeSheafSum J R lower ≅ Q.X n
  upper_square : upperBoundary.ordinaryMap J R ≫ middleIso.hom =
    upperIso.hom ≫ Q.d (n + 2) (n + 1)
  lower_square : lowerBoundary.ordinaryMap J R ≫ lowerIso.hom =
    middleIso.hom ≫ Q.d (n + 1) n

variable {Q : ChainComplex (Sheaf J (ModuleCat.{w} R)) ℕ} {n : ℕ}

/-- Signed restriction squares assemble the actual equivariant three-term
model, without an additional equivariant exactness hypothesis. -/
def FiniteFreeThreeTermModel.equivariantModel
    (M : FiniteFreeThreeTermModel J R S Q n) :
    EquivariantThreeTermModel
      (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)) (Q.sc' (n + 2) (n + 1) n) where
  upper := discreteFreeSheafSum J R S hS M.upper M.upper_eventuallyEquivariant
  middle := discreteFreeSheafSum J R S hS M.middle M.middle_eventuallyEquivariant
  lower := discreteFreeSheafSum J R S hS M.lower M.lower_eventuallyEquivariant
  f := M.upperBoundary.discreteMap J R S hS
    M.upper_eventuallyEquivariant M.middle_eventuallyEquivariant
  g := M.lowerBoundary.discreteMap J R S hS
    M.middle_eventuallyEquivariant M.lower_eventuallyEquivariant
  upperIso := discreteFreeSheafSumRestrictionIso J R S hS
    M.upper M.upper_eventuallyEquivariant ≪≫ M.upperIso
  middleIso := discreteFreeSheafSumRestrictionIso J R S hS
    M.middle M.middle_eventuallyEquivariant ≪≫ M.middleIso
  lowerIso := discreteFreeSheafSumRestrictionIso J R S hS
    M.lower M.lower_eventuallyEquivariant ≪≫ M.lowerIso
  upper_square := by
    change (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
      restriction ρ J (ModuleCat.{w} R)).map
        (M.upperBoundary.discreteMap J R S hS M.upper_eventuallyEquivariant
          M.middle_eventuallyEquivariant) ≫
        ((discreteFreeSheafSumRestrictionIso J R S hS
          M.middle M.middle_eventuallyEquivariant).hom ≫ M.middleIso.hom) =
      ((discreteFreeSheafSumRestrictionIso J R S hS
        M.upper M.upper_eventuallyEquivariant).hom ≫ M.upperIso.hom) ≫
          Q.d (n + 2) (n + 1)
    rw [← Category.assoc, SignedBoundary.discreteMap_restriction_hom,
      Category.assoc, M.upper_square, Category.assoc]
  lower_square := by
    change (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
      restriction ρ J (ModuleCat.{w} R)).map
        (M.lowerBoundary.discreteMap J R S hS M.middle_eventuallyEquivariant
          M.lower_eventuallyEquivariant) ≫
        ((discreteFreeSheafSumRestrictionIso J R S hS
          M.lower M.lower_eventuallyEquivariant).hom ≫ M.lowerIso.hom) =
      ((discreteFreeSheafSumRestrictionIso J R S hS
        M.middle M.middle_eventuallyEquivariant).hom ≫ M.middleIso.hom) ≫
          Q.d (n + 1) n
    rw [← Category.assoc, SignedBoundary.discreteMap_restriction_hom,
      Category.assoc, M.lower_square, Category.assoc]

/-- A finite signed model with exact ordinary chain segment and fixed middle
sections representing the given cochain yields an exact equivariant lift. -/
def FiniteFreeThreeTermModel.cochainLift
    (M : FiniteFreeThreeTermModel J R S Q n) (hQ : Q.ExactAt (n + 1))
    (I : S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (F : Sheaf J (ModuleCat.{w} R))
    (e : (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
      restriction ρ J (ModuleCat.{w} R)).obj I ≅ F)
    (x : Q.X (n + 1) ⟶ F)
    (s : ∀ i, (M.middle i).FixedSections (I.obj.obj ⋙ forget (ModuleCat.{w} R)))
    (hs : ∀ i, (s i).val = freeRepresentableHomEquiv J R (M.middle i).obj
      ((S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)).obj I)
      (Sigma.ι (fun j => (freeSheafFunctor J R).obj
        (shrinkYoneda.{w}.obj (M.middle j).obj)) i ≫ M.middleIso.hom ≫ x ≫ e.inv)) :
    EquivariantCochainLift
      (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)) Q I F e n x := by
  refine EquivariantThreeTermModel.cochainLift Q n
    (M.equivariantModel J R S hS) hQ I F e x
    (discreteFreeSheafSumLift J R S hS M.middle M.middle_eventuallyEquivariant I s) ?_
  let V := S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)
  let a := discreteFreeSheafSumRestrictionIso J R S hS
    M.middle M.middle_eventuallyEquivariant
  change V.map (discreteFreeSheafSumLift J R S hS
    M.middle M.middle_eventuallyEquivariant I s) ≫ e.hom =
      (a.hom ≫ M.middleIso.hom) ≫ x
  apply (cancel_epi a.inv).1
  have hlift := discreteFreeSheafSumLift_restricts_cochain J R S hS
    M.middle_eventuallyEquivariant I (M.middleIso.hom ≫ x ≫ e.inv) s hs
  change a.inv ≫ V.map (discreteFreeSheafSumLift J R S hS
    M.middle M.middle_eventuallyEquivariant I s) = M.middleIso.hom ≫ x ≫ e.inv at hlift
  rw [← Category.assoc, hlift, Category.assoc, Category.assoc,
    e.inv_hom_id, Category.comp_id]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift
