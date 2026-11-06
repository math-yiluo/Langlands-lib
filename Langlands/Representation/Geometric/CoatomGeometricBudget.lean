import Langlands.Representation.Geometric.RepresentedCuspidalLengthBudget
import Langlands.Group.RelativeWeylCoatomSurvivors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Counting actual represented geometric survivors through Coxeter labels -/

noncomputable section

universe u v uB uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open Classical GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hl : IsRationalLeviSubgroup l}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hmul : IsIso (subgroupMultiplication l r)}
  {n : ℕ} {Q L U : Fin n → GroupScheme (Spec (CommRingCat.of k))}
  {q : ∀ a, Q a ⟶ G} {lQ : ∀ a, L a ⟶ Q a} {rQ : ∀ a, U a ⟶ Q a}
  {hq : ∀ a, IsParabolicSubgroup (q a)}
  {hlQ : ∀ a, IsRationalLeviSubgroup (lQ a)}
  {hrQ : ∀ a, LeviSubgroup.IsGeometricUnipotentRadical (rQ a)}
  {hmulQ : ∀ a, IsIso (subgroupMultiplication (lQ a) (rQ a))}
  {m : Fin n → ℕ} {z : ∀ a, Fin (m a) → rationalPoints G}
  (D : ∀ a j, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    (q a) (lQ a) (rQ a) (hq a) (hrQ a) (hlQ a) (hmulQ a) (z a j))
  {B : Type uB} {W : Type uW} [Group W] [Fintype B] [Fintype W]
  {C : CoxeterMatrix B} (cs : CoxeterSystem C W) (b : B)
  (I : Fin n → Finset B) (w : ∀ a, Fin (m a) → W)

/-- An intrinsic coatom bound applies to all actual surviving indices when
their target and representative labels distinguish those indices. -/
def CoatomGeometricBudgetStatement : Prop :=
  Function.Injective I →
  (∀ a, Function.Injective (w a)) →
  (∀ a, (I a).card = (Finset.univ.erase b).card) →
  (∀ a j, IsIso (D a j).p' → IsMinimal cs (I a) (Finset.univ.erase b) (w a j)) →
  (∀ a j, IsIso (D a j).p' →
    intersectionSubset cs (I a) (Finset.univ.erase b) (w a j) = Finset.univ.erase b) →
  (∑ a, (fullSourceIndices (D a)).card) ≤ 2

/-- The finite sigma of all surviving actual indices injects into the full
intrinsic pair finset. No survivor multiplicity is discarded. -/
theorem coatomGeometricBudget : CoatomGeometricBudgetStatement D cs b I w := by
  classical
  intro hI hw hcard hmin hfull
  let S : Finset (Σ a : Fin n, Fin (m a)) :=
    Finset.univ.sigma (fun a => fullSourceIndices (D a))
  let f : (Σ a : Fin n, Fin (m a)) → Finset B × W :=
    fun x => (I x.1, w x.1 x.2)
  have hmap : Set.MapsTo f S (fullIntersectionPairs cs (Finset.univ.erase b)) := by
    rintro ⟨a, j⟩ hj
    have hj' : IsIso (D a j).p' :=
      (mem_fullSourceIndices (D a) j).mp (Finset.mem_sigma.mp hj).2
    change (I a, w a j) ∈ fullIntersectionPairs cs (Finset.univ.erase b)
    simp only [fullIntersectionPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcard a, hmin a j hj', hfull a j hj'⟩
  have hinj : (S : Set (Σ a : Fin n, Fin (m a))).InjOn f := by
    rintro ⟨a, j⟩ _ ⟨a', j'⟩ _ he
    have haa : a = a' := hI (congrArg Prod.fst he)
    subst a'
    have hjj : j = j' := hw a (congrArg Prod.snd he)
    subst j'
    rfl
  have hcount := Finset.card_le_card_of_injOn f hmap hinj
  have hS : S.card = ∑ a, (fullSourceIndices (D a)).card := by
    simp [S, Finset.card_sigma]
  rw [hS] at hcount
  exact hcount.trans (card_fullIntersectionPairs_coatom_le_two cs b)

omit D cs b I [TopologicalSpace k] [Group W] [Fintype W] in
/-- Coordinates in the literal actual double-coset quotient distinguish all
geometric indices. A chosen lift need not itself be injective. -/
theorem geometric_labels_injective_of_doubleCoset_coordinates
    (c : ∀ a, Fin (m a) ≃ DoubleCoset.Quotient
      (pointImage p : Set (rationalPoints G)) (pointImage (q a) : Set (rationalPoints G)))
    (lift : Fin n → W → rationalPoints G)
    (hc : ∀ a j, DoubleCoset.mk (pointImage p) (pointImage (q a))
      (lift a (w a j)) = c a j) :
    ∀ a, Function.Injective (w a) := by
  intro a j j' he
  apply (c a).injective
  calc
    c a j = DoubleCoset.mk (pointImage p) (pointImage (q a)) (lift a (w a j)) :=
      (hc a j).symm
    _ = DoubleCoset.mk (pointImage p) (pointImage (q a)) (lift a (w a j')) := by rw [he]
    _ = c a j' := hc a j'

section Length

variable [T2Space k] [IsAffineHom G.X.hom]

local instance coatomGeometricBudgetPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
  (hρ : letI := leviPointTopology l hl; ρ.IsIrreducible)
  (hcusp : haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : N' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
  (E : ∀ a, M ≅ L a)
  (hglue : ∀ a, IsGluedFrom
    (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
      (q a) (lQ a) (rQ a) (hq a) (hrQ a) (hlQ a) (hmulQ a))
    (fun j => (D a j).pieceFunctor))
  (hI : Function.Injective I)
  (c : ∀ a, Fin (m a) ≃ DoubleCoset.Quotient
    (pointImage p : Set (rationalPoints G)) (pointImage (q a) : Set (rationalPoints G)))
  (lift : Fin n → W → rationalPoints G)
  (hcoord : ∀ a j, DoubleCoset.mk (pointImage p) (pointImage (q a))
    (lift a (w a j)) = c a j)
  (hcard : ∀ a, (I a).card = (Finset.univ.erase b).card)
  (hmin : ∀ a j, IsIso (D a j).p' →
    IsMinimal cs (I a) (Finset.univ.erase b) (w a j))
  (hfull : ∀ a j, IsIso (D a j).p' →
    intersectionSubset cs (I a) (Finset.univ.erase b) (w a j) = Finset.univ.erase b)
  (hdetect : ∀ A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
    A.IsIrreducible →
    SmoothRep.IsSubquotient A ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
    ∃ a, letI := leviPointTopology (lQ a) (hlQ a)
      Nontrivial ((leviJacquetFunctor (q a) (lQ a) (rQ a)
        (hq a) (hrQ a) (hlQ a) (hmulQ a)).obj A))

include hρ hcusp E hglue hI hcoord hcard hmin hfull hdetect

/-- Actual orbit coordinates and the coatom classification supply the numeric
budget of the represented detecting-Jacquet witness. -/
theorem hasRepresentedJacquetLengthWitness_of_coatom_coordinates :
    HasRepresentedJacquetLengthWitness
      ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) 2 := by
  apply hasRepresentedJacquetLengthWitness_of_geometricBudget
    ρ hρ hcusp E D hglue
  · exact coatomGeometricBudget D cs b I w hI
      (geometric_labels_injective_of_doubleCoset_coordinates w c lift hcoord)
      hcard hmin hfull
  · exact hdetect

/-- The actual induction has composition length at most two under the stated
geometric-coordinate and every-subquotient detection inputs. -/
theorem induced_repLength_le_two_of_coatom_coordinates :
    repLength ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation ≤
      (2 : ℕ∞) :=
  repLength_le_of_hasRepresentedJacquetLengthWitness _
    (hasRepresentedJacquetLengthWitness_of_coatom_coordinates
      D cs b I w ρ hρ hcusp E hglue hI c lift hcoord hcard hmin hfull hdetect)

end Length

end Langlands.Aubert.General.RepresentedParabolic
