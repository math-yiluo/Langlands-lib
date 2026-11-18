import Langlands.Cohomology.SiteCech.FiniteCechDifferentials
import Langlands.Sheaf.Equivariant.TwistedFreeRepresentableCochain

/-! # Finite equivariant models from lifted tuple cones -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial BigOperators

universe u v z w a

namespace Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type z} [Group G] {ρ : G →* Aut X}

/-- Specify the underlying object definitionally, using a supplied equality.
The result is propositionally the original global lift. -/
def withObject (L : GlobalLift (P := P) (ρ := ρ))
    (U : P.Over ⊤ X) (h : L.obj = U) : GlobalLift (P := P) (ρ := ρ) where
  obj := U
  action := h ▸ L.action
  twist := by
    subst U
    exact L.twist

@[simp]
theorem withObject_eq (L : GlobalLift (P := P) (ρ := ρ))
    (U : P.Over ⊤ X) (h : L.obj = U) : L.withObject U h = L := by
  subst U
  rfl

end Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift

namespace Langlands.Cohomology.SiteCech

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
variable {X : C} {G : Type z} [Group G]
variable {ρ : G →* Aut X}
variable [LocallySmall.{w} (P.Over ⊤ X)]
variable (J : GrothendieckTopology (P.Over ⊤ X))
variable {ι : Type a} (B : ι → P.Over ⊤ X)
variable {U : P.Over ⊤ X} (s : FiniteBasisCover J B U)
variable (b : ∀ n, (Fin (n + 1) → Fin s.size) → ι)
variable (c : ∀ n (α : Fin (n + 1) → Fin s.size),
  WidePullbackCone (fun j => s.arrow (α j)))
variable (hc : ∀ n α, IsLimit (c n α))
variable (e : ∀ n α, (c n α).pt ≅ B (b n α))

/-- Normalize a supplied lifted family to the basis objects in one tuple degree. -/
def FiniteBasisCover.tupleLiftFamily (k : ℕ)
    (L : Fin (Fintype.card (Fin (k + 1) → Fin s.size)) →
      GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).obj = B (b k ((Fintype.equivFin _).symm i))) :
    Fin (Fintype.card (Fin (k + 1) → Fin s.size)) →
      GlobalLift (P := P) (ρ := ρ) :=
  fun i => (L i).withObject (B (b k ((Fintype.equivFin _).symm i))) (hL i)

omit [LocallySmall.{w} (P.Over ⊤ X)] in
@[simp]
theorem FiniteBasisCover.tupleLiftFamily_eq (k : ℕ)
    (L : Fin (Fintype.card (Fin (k + 1) → Fin s.size)) →
      GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).obj = B (b k ((Fintype.equivFin _).symm i))) :
    s.tupleLiftFamily J B b k L hL = L := by
  funext i
  exact withObject_eq _ _ _

/-- Alternating face maps between supplied tuple lifts, assuming the face
arrows intertwine their full actions. -/
def FiniteBasisCover.tupleSignedBoundary (n : ℕ)
    (L : Fin (Fintype.card (Fin (n + 2) → Fin s.size)) →
      GlobalLift (P := P) (ρ := ρ))
    (M : Fin (Fintype.card (Fin (n + 1) → Fin s.size)) →
      GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).obj = B (b (n + 1) ((Fintype.equivFin _).symm i)))
    (hM : ∀ i, (M i).obj = B (b n ((Fintype.equivFin _).symm i)))
    (heq : ∀ (j : Fin (n + 2)) i,
      IsEquivariant
        (L := s.tupleLiftFamily J B b (n + 1) L hL i)
        (M := s.tupleLiftFamily J B b n M hM
          (cechTupleIndexMap (SimplexCategory.δ j) i))
        (s.tupleMapArrow J B b c hc e (SimplexCategory.δ j) i)) :
    SignedBoundary (s.tupleLiftFamily J B b (n + 1) L hL)
      (s.tupleLiftFamily J B b n M hM) where
  length := n + 2
  coefficient j := (-1 : ℤ) ^ (j : ℕ)
  indexMap j := cechTupleIndexMap (SimplexCategory.δ j)
  arrow j i := s.tupleMapArrow J B b c hc e (SimplexCategory.δ j) i
  equivariant := heq

variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]

/-- Forgetting the lifted actions recovers the actual finite tuple boundary. -/
theorem FiniteBasisCover.tupleSignedBoundary_ordinaryMap (n : ℕ)
    (L : Fin (Fintype.card (Fin (n + 2) → Fin s.size)) →
      GlobalLift (P := P) (ρ := ρ))
    (M : Fin (Fintype.card (Fin (n + 1) → Fin s.size)) →
      GlobalLift (P := P) (ρ := ρ))
    (hL : ∀ i, (L i).obj = B (b (n + 1) ((Fintype.equivFin _).symm i)))
    (hM : ∀ i, (M i).obj = B (b n ((Fintype.equivFin _).symm i)))
    (heq : ∀ (j : Fin (n + 2)) i,
      IsEquivariant
        (L := s.tupleLiftFamily J B b (n + 1) L hL i)
        (M := s.tupleLiftFamily J B b n M hM
          (cechTupleIndexMap (SimplexCategory.δ j) i))
        (s.tupleMapArrow J B b c hc e (SimplexCategory.δ j) i)) :
    (s.tupleSignedBoundary J B b c hc e n L M hL hM heq).ordinaryMap J R =
      s.tupleFreeBoundary J B b c hc e R n := rfl

section ThreeTerm

variable [TopologicalSpace G]
variable (S : LocalActionSystem (TwistedOver P ρ) G)
variable (n : ℕ)
variable (upper : Fin (Fintype.card (Fin (n + 3) → Fin s.size)) →
  GlobalLift (P := P) (ρ := ρ))
variable (middle : Fin (Fintype.card (Fin (n + 2) → Fin s.size)) →
  GlobalLift (P := P) (ρ := ρ))
variable (lower : Fin (Fintype.card (Fin (n + 1) → Fin s.size)) →
  GlobalLift (P := P) (ρ := ρ))
variable (hupper : ∀ i, (upper i).obj = B (b (n + 2) ((Fintype.equivFin _).symm i)))
variable (hmiddle : ∀ i, (middle i).obj = B (b (n + 1) ((Fintype.equivFin _).symm i)))
variable (hlower : ∀ i, (lower i).obj = B (b n ((Fintype.equivFin _).symm i)))
variable (hupper_eventually : ∀ i, (upper i).EventuallyEquivariant S)
variable (hmiddle_eventually : ∀ i, (middle i).EventuallyEquivariant S)
variable (hlower_eventually : ∀ i, (lower i).EventuallyEquivariant S)
variable (hupper_face : ∀ (j : Fin (n + 3)) i,
  IsEquivariant
    (L := s.tupleLiftFamily J B b (n + 2) upper hupper i)
    (M := s.tupleLiftFamily J B b (n + 1) middle hmiddle
      (cechTupleIndexMap (SimplexCategory.δ j) i))
    (s.tupleMapArrow J B b c hc e (SimplexCategory.δ j) i))
variable (hlower_face : ∀ (j : Fin (n + 2)) i,
  IsEquivariant
    (L := s.tupleLiftFamily J B b (n + 1) middle hmiddle i)
    (M := s.tupleLiftFamily J B b n lower hlower
      (cechTupleIndexMap (SimplexCategory.δ j) i))
    (s.tupleMapArrow J B b c hc e (SimplexCategory.δ j) i))

/-- Three supplied lifted tuple degrees, with eventual equivariance and
full-action equivariance of all faces, give the actual finite free model.
The ordinary differential squares follow from the canonical tuple-cone
presentation, rather than being further inputs. -/
def FiniteBasisCover.finiteFreeThreeTermModelOfCones :
    FiniteFreeThreeTermModel J R S
      (freeCechChainComplex J R (s.presheafArrow J B)) n where
  upperSize := Fintype.card (Fin (n + 3) → Fin s.size)
  middleSize := Fintype.card (Fin (n + 2) → Fin s.size)
  lowerSize := Fintype.card (Fin (n + 1) → Fin s.size)
  upper := s.tupleLiftFamily J B b (n + 2) upper hupper
  middle := s.tupleLiftFamily J B b (n + 1) middle hmiddle
  lower := s.tupleLiftFamily J B b n lower hlower
  upper_eventuallyEquivariant := by
    rw [s.tupleLiftFamily_eq J B b]
    exact hupper_eventually
  middle_eventuallyEquivariant := by
    rw [s.tupleLiftFamily_eq J B b]
    exact hmiddle_eventually
  lower_eventuallyEquivariant := by
    rw [s.tupleLiftFamily_eq J B b]
    exact hlower_eventually
  upperBoundary := s.tupleSignedBoundary J B b c hc e (n + 1)
    upper middle hupper hmiddle hupper_face
  lowerBoundary := s.tupleSignedBoundary J B b c hc e n
    middle lower hmiddle hlower hlower_face
  upperIso := ((s.cechPresentationOfCones J B b c hc e).freeTermIso J B R (n + 2)).symm
  middleIso := ((s.cechPresentationOfCones J B b c hc e).freeTermIso J B R (n + 1)).symm
  lowerIso := ((s.cechPresentationOfCones J B b c hc e).freeTermIso J B R n).symm
  upper_square := (s.cechPresentationOfCones_free_inv_d J B b c hc e R (n + 1)).symm
  lower_square := (s.cechPresentationOfCones_free_inv_d J B b c hc e R n).symm

/-- The middle family is the supplied lift family, up to the normalization
that makes its underlying basis objects definitionally exact. -/
@[simp]
theorem FiniteBasisCover.finiteFreeThreeTermModelOfCones_middle :
    (s.finiteFreeThreeTermModelOfCones J B b c hc e R S n
      upper middle lower hupper hmiddle hlower
      hupper_eventually hmiddle_eventually hlower_eventually
      hupper_face hlower_face).middle = middle := by
  exact s.tupleLiftFamily_eq J B b (n + 1) middle hmiddle

end ThreeTerm

end Langlands.Cohomology.SiteCech
