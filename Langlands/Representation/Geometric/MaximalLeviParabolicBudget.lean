import Langlands.GroupScheme.Rational.MaximalLeviParabolicCountCore
import Langlands.Representation.Geometric.ConjugatedParabolicIndexing
import Langlands.Representation.Geometric.RepresentedCuspidalLengthBudget
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # A geometric survivor bound through actual parabolics sharing a maximal Levi -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hl : IsRationalLeviSubgroup l}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hmul : IsIso (subgroupMultiplication l r)}

namespace GeometricLemmaIntersectionDatum

variable {Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hlQ : IsRationalLeviSubgroup lQ}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- A full source intersection between isomorphic outer Levis identifies the
conjugated target Levi with the original embedded Levi. -/
theorem exists_leviIso_conjugate_comp
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z) (E : M ≅ L) [IsIso D.p'] :
    ∃ e : M ≅ L, e.hom ≫ lQ ≫ q ≫ (G.innerIso z).hom = l ≫ p := by
  have := D.isIso_l'_of_isIso_p'
  have := D.isIso_lQ'_comp_q'_of_isIso_p'_of_iso E
  let f : D.L' ⟶ M := D.φ.hom ≫ D.l' ≫ D.p'
  let e : M ≅ L := (asIso f).symm ≪≫ asIso (D.lQ' ≫ D.q')
  refine ⟨e, ?_⟩
  calc
    e.hom ≫ lQ ≫ q ≫ (G.innerIso z).hom =
        inv f ≫ (D.lQ' ≫ D.q' ≫ lQ ≫ q ≫ (G.innerIso z).hom) := by
      simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc]
    _ = inv f ≫ (D.φ.hom ≫ D.l' ≫ D.p' ≫ l ≫ p) := by rw [D.φ_comp]
    _ = inv f ≫ f ≫ l ≫ p := by simp only [f, Category.assoc]
    _ = l ≫ p := by simp

end GeometricLemmaIntersectionDatum

variable {n : ℕ} {Q L U : Fin n → GroupScheme (Spec (CommRingCat.of k))}
  {q : ∀ a, Q a ⟶ G} {lQ : ∀ a, L a ⟶ Q a} {rQ : ∀ a, U a ⟶ Q a}
  {hq : ∀ a, IsParabolicSubgroup (q a)} {hlQ : ∀ a, IsRationalLeviSubgroup (lQ a)}
  {hrQ : ∀ a, LeviSubgroup.IsGeometricUnipotentRadical (rQ a)}
  {hmulQ : ∀ a, IsIso (subgroupMultiplication (lQ a) (rQ a))}
  {m : Fin n → ℕ} {z : ∀ a, Fin (m a) → rationalPoints G}
  (D : ∀ a j, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    (q a) (lQ a) (rQ a) (hq a) (hrQ a) (hlQ a) (hmulQ a) (z a j))

/-- The source-full geometric indices inject into the actual parabolics with
the common maximal Levi. Only pairwise nonconjugacy of target parabolics and
literal double-coset coordinates are needed for the count. -/
theorem sum_fullSourceIndices_le_two_of_maximal
    (hG : IsConnectedReductive G) (hproper : ¬ IsIso p)
    (hmax : ∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
      IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q')
    (E : ∀ a, M ≅ L a)
    (hsep : ∀ a b, (SubgroupFunctor.range (q a)).IsRationallyConjugate
      (SubgroupFunctor.range (q b)) → a = b)
    (c : ∀ a, Fin (m a) ≃ DoubleCoset.Quotient
      (pointImage p : Set (rationalPoints G)) (pointImage (q a) : Set (rationalPoints G)))
    (hc : ∀ a j, DoubleCoset.mk (pointImage p) (pointImage (q a)) (z a j) = c a j) :
    (∑ a, (fullSourceIndices (D a)).card) ≤ 2 := by
  classical
  let S := Σ a : Fin n, {j // j ∈ fullSourceIndices (D a)}
  let Qs (s : S) := Q s.1
  let qs (s : S) : Qs s ⟶ G := q s.1 ≫ (G.innerIso (z s.1 s.2.1)).hom
  have he (s : S) : ∃ e : M ≅ L s.1,
      e.hom ≫ lQ s.1 ≫ q s.1 ≫ (G.innerIso (z s.1 s.2.1)).hom = l ≫ p := by
    let : IsIso (D s.1 s.2.1).p' := (mem_fullSourceIndices (D s.1) s.2.1).mp s.2.2
    exact (D s.1 s.2.1).exists_leviIso_conjugate_comp (E s.1)
  let es (s : S) : M ≅ L s.1 := (he s).choose
  let ls (s : S) : M ⟶ Qs s := (es s).hom ≫ lQ s.1
  have hqs (s : S) : IsParabolicSubgroup (qs s) :=
    (hq s.1).comp_iso (G.innerIso (z s.1 s.2.1))
  have hls (s : S) : IsRationalLeviSubgroup (ls s) :=
    (hlQ s.1).iso_comp (es s)
  have hcomp (s : S) : ls s ≫ qs s = l ≫ p := by
    exact (he s).choose_spec
  have hinj : Function.Injective (fun s : S => SubgroupFunctor.range (qs s)) := by
    rintro ⟨a, j, hj⟩ ⟨b, j', hj'⟩ heq
    have hab : a = b := hsep a b
      (rationallyConjugate_of_conjugate_range_eq (q a) (q b) (z a j) (z b j') heq)
    subst b
    have hjj : j = j' := by
      apply (c a).injective
      rw [← hc a j, ← hc a j']
      exact doubleCoset_eq_of_conjugate_parabolic_eq hG (pointImage p)
        (q a) (hq a) (z a j) (z a j') heq
    subst j'
    rfl
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hcount := maximalLeviParabolicCount_core k G hG P M p l hp hl hproper hmax
    (Fintype.card S) (fun i => Qs (e i)) (fun i => qs (e i)) (fun i => ls (e i))
    (fun i => hqs (e i)) (fun i => hls (e i)) (fun i => hcomp (e i))
    (hinj.comp e.injective)
  have hcard : Fintype.card S = ∑ a, (fullSourceIndices (D a)).card := by
    simp only [S, Fintype.card_sigma, Fintype.card_coe]
  rw [hcard] at hcount
  exact hcount

section Length

variable [T2Space k] [IsAffineHom G.X.hom]

local instance maximalParabolicBudgetPointTopology : TopologicalSpace (rationalPoints G) :=
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
  (hG : IsConnectedReductive G) (hproper : ¬ IsIso p)
  (hmax : ∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
    IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q')
  (E : ∀ a, M ≅ L a)
  (hsep : ∀ a b, (SubgroupFunctor.range (q a)).IsRationallyConjugate
    (SubgroupFunctor.range (q b)) → a = b)
  (c : ∀ a, Fin (m a) ≃ DoubleCoset.Quotient
    (pointImage p : Set (rationalPoints G)) (pointImage (q a) : Set (rationalPoints G)))
  (hc : ∀ a j, DoubleCoset.mk (pointImage p) (pointImage (q a)) (z a j) = c a j)
  (hglue : ∀ a, IsGluedFrom
    (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
      (q a) (lQ a) (rQ a) (hq a) (hrQ a) (hlQ a) (hmulQ a))
    (fun j => (D a j).pieceFunctor))
  (hdetect : ∀ A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
    A.IsIrreducible →
    SmoothRep.IsSubquotient A ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
    ∃ a, letI := leviPointTopology (lQ a) (hlQ a)
      Nontrivial ((leviJacquetFunctor (q a) (lQ a) (rQ a)
        (hq a) (hrQ a) (hlQ a) (hmulQ a)).obj A))

include hρ hcusp hG hproper hmax E hsep hc hglue hdetect

/-- The actual-parabolic count supplies a length witness once the separated
finite family has geometric filtrations and detects every subquotient. -/
theorem hasRepresentedJacquetLengthWitness_of_separated_geometric_family :
    HasRepresentedJacquetLengthWitness
      ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) 2 :=
  hasRepresentedJacquetLengthWitness_of_geometricBudget ρ hρ hcusp E D hglue
    (sum_fullSourceIndices_le_two_of_maximal D hG hproper hmax E hsep c hc) hdetect

/-- The detecting separated geometric family bounds induction length by two,
without a supplied Coxeter coordinate system or a finite-length premise. -/
theorem induced_repLength_le_two_of_separated_geometric_family :
    repLength ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation ≤
      (2 : ℕ∞) :=
  repLength_le_of_hasRepresentedJacquetLengthWitness _
    (hasRepresentedJacquetLengthWitness_of_separated_geometric_family
      D ρ hρ hcusp hG hproper hmax E hsep c hc hglue hdetect)

end Length

end Langlands.Aubert.General.RepresentedParabolic
