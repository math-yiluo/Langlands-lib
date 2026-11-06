import Langlands.Representation.Geometric.RepresentedCuspidalLength
import Langlands.Representation.Geometric.FullIntersectionIrreducible
import Langlands.Representation.Exponents.RepresentedJacquetLengthWitnessReduction
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups

/-! # Actual Jacquet length budgets from supplied represented geometric filtrations -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M N : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance geometricBudgetPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

section OneTarget

variable {Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {m : ℕ} {z : Fin m → rationalPoints G}
  (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ (z i))

/-- For isomorphic outer Levis, irreducible cuspidal input makes the length of a
supplied actual geometric gluing equal the number of full-source indices. -/
def IsomorphicLeviCuspidalLengthStatement : Prop :=
  (letI := leviPointTopology l hl; ρ.IsIrreducible) →
  (haveI := hl.isConnectedReductive.isAffineHom;
    letI := leviPointTopology l hl;
    haveI := leviPoints_locallyCompactSpace p l hp hl;
    haveI := leviPoints_nonarchimedeanGroup p l hp hl;
    ∀ (P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : N' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
  Nonempty (M ≅ L) →
  IsGluedFrom
    (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
    (fun i => (D i).pieceFunctor) →
  repLength ((leviJacquetInductionFunctor.{u, v}
    p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj ρ).ρ =
    ((fullSourceIndices D).card : ℕ∞)

/-- Full-source pieces are irreducible by the outer-Levi isomorphism; proper
source pieces vanish by the original proper-Jacquet condition. -/
theorem isomorphicLeviCuspidalLength : IsomorphicLeviCuspidalLengthStatement ρ D := by
  intro hρ hc ⟨E⟩ hglue
  apply representedJacquetInduction_repLength_eq_card_fullSource ρ hc D hglue
  intro i hi
  let : IsIso (D i).p' := hi
  exact (D i).pieceFunctor_isIrreducible_of_isIso_source_of_iso ρ E hρ

end OneTarget

section Family

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hρ : letI := leviPointTopology l hl; ρ.IsIrreducible)
  (hc : haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : N' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
  {n : ℕ} {Q L U : Fin n → GroupScheme (Spec (CommRingCat.of k))}
  {q : ∀ i, Q i ⟶ G} {lQ : ∀ i, L i ⟶ Q i} {rQ : ∀ i, U i ⟶ Q i}
  {hq : ∀ i, IsParabolicSubgroup (q i)}
  {hrQ : ∀ i, LeviSubgroup.IsGeometricUnipotentRadical (rQ i)}
  {hlQ : ∀ i, IsRationalLeviSubgroup (lQ i)}
  {hmulQ : ∀ i, IsIso (subgroupMultiplication (lQ i) (rQ i))}
  (E : ∀ i, M ≅ L i)
  {m : Fin n → ℕ} {z : ∀ i, Fin (m i) → rationalPoints G}
  (D : ∀ i j, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    (q i) (lQ i) (rQ i) (hq i) (hrQ i) (hlQ i) (hmulQ i) (z i j))
  (hglue : ∀ i, IsGluedFrom
    (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
      (q i) (lQ i) (rQ i) (hq i) (hrQ i) (hlQ i) (hmulQ i))
    (fun j => (D i j).pieceFunctor))
  {bound : ℕ}
  (hbudget : (∑ i, (fullSourceIndices (D i)).card) ≤ bound)
  (hdetect : ∀ A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
    A.IsIrreducible →
    SmoothRep.IsSubquotient A ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
    ∃ i, letI := leviPointTopology (lQ i) (hlQ i)
      Nontrivial ((leviJacquetFunctor (q i) (lQ i) (rQ i)
        (hq i) (hrQ i) (hlQ i) (hmulQ i)).obj A))

include hρ hc E hglue hbudget hdetect

/-- A finite family of supplied geometric gluings, a total surviving-index
budget, and detection give the actual Jacquet witness. Radical compactness is
supplied by the proved local-field unipotent-radical theorem. -/
theorem hasRepresentedJacquetLengthWitness_of_geometricBudget :
    HasRepresentedJacquetLengthWitness
      ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) bound := by
  refine ⟨n, Q, L, U, q, lQ, rQ, hq, hlQ, hrQ, hmulQ, ?_,
    (fun i => (fullSourceIndices (D i)).card), hbudget, ?_, hdetect⟩
  · intro i
    exact isLimitOfCompactSubgroups_pointImage_radical
      (q i) (rQ i) (hq i).isClosedSubgroup (hrQ i).1
  · intro i
    change repLength ((leviJacquetInductionFunctor.{u, v}
      p l r hp hr hl hmul (q i) (lQ i) (rQ i) (hq i) (hrQ i) (hlQ i) (hmulQ i)).obj ρ).ρ ≤ _
    exact le_of_eq (isomorphicLeviCuspidalLength ρ (D i) hρ hc ⟨E i⟩ (hglue i))

/-- The same geometric budget bounds actual composition length without assuming
that the induction already has finite length. -/
theorem induced_repLength_le_of_geometricBudget :
    repLength ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation ≤
      (bound : ℕ∞) :=
  repLength_le_of_hasRepresentedJacquetLengthWitness _
    (hasRepresentedJacquetLengthWitness_of_geometricBudget
      ρ hρ hc E D hglue hbudget hdetect)

end Family

end Langlands.Aubert.General.RepresentedParabolic
