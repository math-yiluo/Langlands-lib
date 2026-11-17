import Langlands.Sheaf.Equivariant.TwistedFreeRepresentableMaps
import Langlands.Sheaf.Equivariant.TwistedCompactComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Finite sums of discrete lifted free representables -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Cohomology.SiteCech

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

/-- The actual finite coproduct in the discrete sheaf category. -/
def discreteFreeSheafSum {m : ℕ} (L : Fin m → GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).EventuallyEquivariant S) :
    S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) :=
  ∐ (fun i => (L i).discreteFreeSheaf S J R hS (hL i))

/-- Ordinary restriction compares the finite coproduct with the coproduct of
the actual ordinary free representable sheaves. -/
def discreteFreeSheafSumRestrictionIso {m : ℕ}
    (L : Fin m → GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).EventuallyEquivariant S) :
    (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)).obj (discreteFreeSheafSum J R S hS L hL) ≅
      ∐ (fun i => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (L i).obj)) :=
  PreservesCoproduct.iso (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)) (fun i => (L i).discreteFreeSheaf S J R hS (hL i)) ≪≫
    Sigma.mapIso (fun i => (L i).freeSheafRestrictionIso J R)

@[reassoc]
theorem discreteFreeSheafSumRestrictionIso_ι_inv {m : ℕ}
    (L : Fin m → GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).EventuallyEquivariant S) (i : Fin m) :
    Sigma.ι (fun j => (freeSheafFunctor J R).obj
        (shrinkYoneda.{w}.obj (L j).obj)) i ≫
        (discreteFreeSheafSumRestrictionIso J R S hS L hL).inv =
      ((L i).freeSheafRestrictionIso J R).inv ≫
        (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)).map (Sigma.ι (fun j => (L j).discreteFreeSheaf S J R hS (hL j)) i) := by
  let V := S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)
  let A := fun j => (L j).discreteFreeSheaf S J R hS (hL j)
  let e : ∀ j, V.obj (A j) ≅
      (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (L j).obj) :=
    fun j => (L j).freeSheafRestrictionIso J R
  change Sigma.ι _ i ≫ ((Sigma.mapIso e).inv ≫ (PreservesCoproduct.iso V A).inv) =
    (e i).inv ≫ V.map (Sigma.ι A i)
  rw [Sigma.ι_mapIso_inv_assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

/-- A family of equivariant ordinary arrows and an index map induce a map
between the actual finite coproducts of discrete free sheaves. -/
def discreteFreeSheafSumMap {m k : ℕ}
    (L : Fin m → GlobalLift (P := P) (ρ := ρ))
    (M : Fin k → GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).EventuallyEquivariant S)
    (hM : ∀ j, (M j).EventuallyEquivariant S)
    (a : Fin m → Fin k) (p : ∀ i, (L i).obj ⟶ (M (a i)).obj)
    (hp : ∀ i, IsEquivariant (L := L i) (M := M (a i)) (p i)) :
    discreteFreeSheafSum J R S hS L hL ⟶ discreteFreeSheafSum J R S hS M hM :=
  Sigma.map' a (fun i => discreteFreeSheafMap J R S hS (hL i) (hM (a i)) (p i) (hp i))

/-- The finite coproduct map restricts to the actual ordinary free map on each
summand, through the specified finite-sum comparison isomorphisms. -/
theorem discreteFreeSheafSumMap_restriction {m k : ℕ}
    (L : Fin m → GlobalLift (P := P) (ρ := ρ))
    (M : Fin k → GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).EventuallyEquivariant S)
    (hM : ∀ j, (M j).EventuallyEquivariant S)
    (a : Fin m → Fin k) (p : ∀ i, (L i).obj ⟶ (M (a i)).obj)
    (hp : ∀ i, IsEquivariant (L := L i) (M := M (a i)) (p i)) :
    (discreteFreeSheafSumRestrictionIso J R S hS L hL).inv ≫
        (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)).map (discreteFreeSheafSumMap J R S hS L M hL hM a p hp) =
      Sigma.map' a (fun i => (freeSheafFunctor J R).map (shrinkYoneda.{w}.map (p i))) ≫
        (discreteFreeSheafSumRestrictionIso J R S hS M hM).inv := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, discreteFreeSheafSumRestrictionIso_ι_inv]
  let V := S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)
  let e : ∀ j, V.obj ((L j).discreteFreeSheaf S J R hS (hL j)) ≅
      (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (L j).obj) :=
    fun j => (L j).freeSheafRestrictionIso J R
  change ((e i).inv ≫ V.map
      (Sigma.ι (fun j => (L j).discreteFreeSheaf S J R hS (hL j)) i)) ≫
    V.map (discreteFreeSheafSumMap J R S hS L M hL hM a p hp) = _
  dsimp only [discreteFreeSheafSumMap, discreteFreeSheafSum]
  rw [Category.assoc, ← V.map_comp]
  simp only [Sigma.ι_comp_map', Functor.map_comp]
  let eM : V.obj ((M (a i)).discreteFreeSheaf S J R hS (hM (a i))) ≅
      (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (M (a i)).obj) :=
    (M (a i)).freeSheafRestrictionIso J R
  let b : V.obj (∐ (fun j => (M j).discreteFreeSheaf S J R hS (hM j))) ≅
      ∐ (fun j => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (M j).obj)) :=
    discreteFreeSheafSumRestrictionIso J R S hS M hM
  change (e i).inv ≫ V.map (discreteFreeSheafMap J R S hS (hL i) (hM (a i))
      (p i) (hp i)) ≫ V.map (Sigma.ι
        (fun j => (M j).discreteFreeSheaf S J R hS (hM j)) (a i)) =
    Sigma.ι (fun j => (freeSheafFunctor J R).obj
      (shrinkYoneda.{w}.obj (L j).obj)) i ≫
      Sigma.map' a (fun j => (freeSheafFunctor J R).map (shrinkYoneda.{w}.map (p j))) ≫ b.inv
  have he : (e i).inv ≫ V.map (discreteFreeSheafMap J R S hS (hL i) (hM (a i))
      (p i) (hp i)) =
      (freeSheafFunctor J R).map (shrinkYoneda.{w}.map (p i)) ≫ eM.inv :=
    freeSheafMap_restriction J R (p i) (hp i)
  rw [← Category.assoc, he, Category.assoc, Sigma.ι_comp_map'_assoc]
  have hj : Sigma.ι (fun j => (freeSheafFunctor J R).obj
        (shrinkYoneda.{w}.obj (M j).obj)) (a i) ≫ b.inv =
      eM.inv ≫ V.map (Sigma.ι
        (fun j => (M j).discreteFreeSheaf S J R hS (hM j)) (a i)) :=
    discreteFreeSheafSumRestrictionIso_ι_inv J R S hS M hM (a i)
  rw [hj]

/-- Lift a finite family of sections fixed under the supplied whole-group
actions to a morphism from the discrete coproduct. -/
def discreteFreeSheafSumLift {m : ℕ}
    (L : Fin m → GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).EventuallyEquivariant S)
    (F : S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (s : ∀ i, (L i).FixedSections (F.obj.obj ⋙ forget (ModuleCat.{w} R))) :
    discreteFreeSheafSum J R S hS L hL ⟶ F :=
  Sigma.desc (fun i =>
    ((L i).discreteFreeSheafHomEquivFixedSections S J R hS (hL i) F).symm (s i))

/-- Ordinary restriction recovers the ordinary cochain represented by the
given family, including its precise coproduct comparison. -/
theorem discreteFreeSheafSumLift_restricts {m : ℕ}
    (L : Fin m → GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).EventuallyEquivariant S)
    (F : S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (s : ∀ i, (L i).FixedSections (F.obj.obj ⋙ forget (ModuleCat.{w} R))) :
    (discreteFreeSheafSumRestrictionIso J R S hS L hL).inv ≫
        (S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)).map (discreteFreeSheafSumLift J R S hS L hL F s) =
      Sigma.desc (fun i => (freeRepresentableHomEquiv J R (L i).obj ((S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)).obj F)).symm
        (s i).val) := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, discreteFreeSheafSumRestrictionIso_ι_inv]
  let V := S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)
  let e : ∀ j, V.obj ((L j).discreteFreeSheaf S J R hS (hL j)) ≅
      (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (L j).obj) :=
    fun j => (L j).freeSheafRestrictionIso J R
  change ((e i).inv ≫ V.map
      (Sigma.ι (fun j => (L j).discreteFreeSheaf S J R hS (hL j)) i)) ≫
    V.map (discreteFreeSheafSumLift J R S hS L hL F s) = _
  dsimp only [discreteFreeSheafSumLift, discreteFreeSheafSum]
  rw [Category.assoc, ← V.map_comp]
  simp only [Sigma.ι_comp_desc]
  apply (freeRepresentableHomEquiv J R (L i).obj ((S.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)).obj F)).injective
  exact ((L i).fixedSectionLift_restricts S J R hS (hL i) F (s i)).trans
    ((freeRepresentableHomEquiv J R (L i).obj (V.obj F)).apply_symm_apply
      (s i).val).symm

end Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift
