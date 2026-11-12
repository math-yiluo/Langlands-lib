import Langlands.Global.AdelicClosedSubgroupHeightChain
import Langlands.Global.AdelicLineCharacterHeight

/-! # Successive height minima over preceding stabilizer intersections -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Rational points lying in every preceding actual subgroup-scheme range.
The empty prefix is the full rational group. -/
def closedPrefixRationalSubgroup
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G)
    (l : ℕ) : Subgroup (RationalGroupPoints F G) :=
  ⨅ i, ⨅ (_ : i < l), closedChainRationalSubgroup F G H z i

omit [NumberField F] in
@[simp] theorem mem_closedPrefixRationalSubgroup
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G)
    (l : ℕ) (q : RationalGroupPoints F G) :
    q ∈ closedPrefixRationalSubgroup F G H z l ↔
      ∀ i, i < l → q ∈ closedChainRationalSubgroup F G H z i := by
  simp only [closedPrefixRationalSubgroup, Subgroup.mem_iInf]

omit [NumberField F] in
@[simp] theorem closedPrefixRationalSubgroup_zero
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G) :
    closedPrefixRationalSubgroup F G H z 0 = ⊤ := by
  ext q
  simp

omit [NumberField F] in
theorem closedPrefixRationalSubgroup_succ
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G)
    (l : ℕ) :
    closedPrefixRationalSubgroup F G H z (l + 1) =
      closedPrefixRationalSubgroup F G H z l ⊓
        closedChainRationalSubgroup F G H z l := by
  ext q
  simp only [mem_closedPrefixRationalSubgroup, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h l (Nat.lt_succ_self l)⟩
  · rintro ⟨h, hl⟩ i hi
    obtain hi | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    · exact h i hi
    · exact hl

omit [NumberField F] in
/-- Preceding intersections descend without a nesting condition on the
individual stabilizers. -/
theorem closedPrefixRationalSubgroup_antitone
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G) :
    Antitone (closedPrefixRationalSubgroup F G H z) := by
  intro a b hab q hq
  exact (mem_closedPrefixRationalSubgroup F G H z a q).2
    (fun i hi => (mem_closedPrefixRationalSubgroup F G H z b q).1 hq i
      (lt_of_lt_of_le hi hab))

/-- A prescribed representation adapted to each individual subgroup can be
minimized over the intersection of preceding subgroups. -/
theorem exists_mul_rational_mem_closedPrefix_minima
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G)
    (d : ℕ → ℕ) (j : (i : ℕ) → Fin (d i))
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (hρ : ∀ i (A : CommAlgCat.{u} (CommRingCat.of F))
      (x : (algSpec (CommRingCat.of F)).obj (op A) ⟶ G.X),
      x ∈ (SubgroupFunctor.range (z i)).carrier ((algSpec _).obj (op A)) →
        ∃ a : Aˣ, ((ρ i).affineMatrix A x : Matrix (Fin (d i)) (Fin (d i)) A) *ᵥ
          Pi.single (j i) 1 = (a : A) • (Pi.single (j i) 1 : Fin (d i) → A))
    (r : ℕ) (g : normOneSubgroup F G) :
    ∃ q : RationalGroupPoints F G,
      g * rationalNormOne F G q ∈
        chainHeightMinimalSet F G r d ρ (fun i => Pi.single (j i) 1)
          (closedPrefixRationalSubgroup F G H z) 1 := by
  obtain ⟨q, hq⟩ := exists_mul_rational_mem_chainHeightMinimalSet F G r d ρ
    (fun i => Pi.single (j i) 1) (by
      intro i _ hzero
      have hi := congrFun hzero (j i)
      simp at hi)
    (closedPrefixRationalSubgroup F G H z)
    (closedPrefixRationalSubgroup_antitone F G H z) (by
      intro i l hil _ q
      exact hρ i (CommAlgCat.of F F) q
        ((mem_closedPrefixRationalSubgroup F G H z l q).1 q.property i hil)) g
  exact ⟨q.val, hq⟩

/-- An arbitrary family of actual closed subgroups admits representations with
the individual subgroups as exact all-test line stabilizers, and simultaneous
finite-prefix minima over intersections of preceding rational stabilizers. -/
theorem exists_adapted_closedPrefix_minima
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G)
    (hc : ∀ i, IsClosedSubgroup (z i)) :
    ∃ (d : ℕ → ℕ) (j : (i : ℕ) → Fin (d i + 1))
      (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i + 1))),
      (∀ i (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ G.X),
        x ∈ (SubgroupFunctor.range (z i)).carrier T ↔
          ∃ a : Γ(T.left, ⊤)ˣ,
            ((ρ i).pointMatrix T x :
              Matrix (Fin (d i + 1)) (Fin (d i + 1)) Γ(T.left, ⊤)) *ᵥ
                Pi.single (j i) 1 =
              (a : Γ(T.left, ⊤)) • (Pi.single (j i) 1 :
                Fin (d i + 1) → Γ(T.left, ⊤))) ∧
      (∀ i, ((ρ i).restrict (z i)).PreservesCoordinateLine (j i)) ∧
      ∀ (r : ℕ) (g : normOneSubgroup F G),
        ∃ q : RationalGroupPoints F G,
          g * rationalNormOne F G q ∈
            chainHeightMinimalSet F G r (fun i => d i + 1) ρ
              (fun i => Pi.single (j i) 1) (closedPrefixRationalSubgroup F G H z) 1 := by
  choose d j ρ hρ using fun i =>
    Chevalley.exists_line_stabilizer F G (H i) (z i) (hc i)
  refine ⟨d, j, ρ, hρ, ?_, ?_⟩
  · intro i T x
    simpa only [MatrixRepresentation.pointMatrix_restrict] using
      (hρ i T (x ≫ (z i).hom.hom)).1 ⟨x, rfl⟩
  · apply exists_mul_rational_mem_closedPrefix_minima F G H z (fun i => d i + 1) j ρ
    intro i A x hx
    exact ((ρ i).affine_coordinateLine_scalar_iff A x (j i)).1
      ((hρ i _ x).1 hx)

/-- The construction applies to any family of canonical standard parabolics,
including the individual maximal parabolics obtained by deleting simple roots.
No descending order on the family is needed. -/
theorem exists_adapted_standardParabolicPrefix_minima
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (J : ℕ → Set (characterLattice T)) :
    ∃ (d : ℕ → ℕ) (j : (l : ℕ) → Fin (d l + 1))
      (ρ : (l : ℕ) → MatrixRepresentation G (Fin (d l + 1))),
      (∀ l (Q : Over (Spec (CommRingCat.of F))) (x : Q ⟶ G.X),
        x ∈ (standardParabolic i ν (J l)).carrier Q ↔
          ∃ a : Γ(Q.left, ⊤)ˣ,
            ((ρ l).pointMatrix Q x :
              Matrix (Fin (d l + 1)) (Fin (d l + 1)) Γ(Q.left, ⊤)) *ᵥ
                Pi.single (j l) 1 =
              (a : Γ(Q.left, ⊤)) • (Pi.single (j l) 1 :
                Fin (d l + 1) → Γ(Q.left, ⊤))) ∧
      (∀ l, ((ρ l).restrict (Standard.parabolicHom i ν (J l))).PreservesCoordinateLine
        (j l)) ∧
      ∀ (r : ℕ) (g : normOneSubgroup F G),
        ∃ q : RationalGroupPoints F G,
          g * rationalNormOne F G q ∈
            chainHeightMinimalSet F G r (fun l => d l + 1) ρ
              (fun l => Pi.single (j l) 1)
              (closedPrefixRationalSubgroup F G
                (fun l => Standard.parabolicScheme i ν (J l))
                (fun l => Standard.parabolicHom i ν (J l))) 1 := by
  obtain ⟨d, j, ρ, hρ, hline, hmin⟩ := exists_adapted_closedPrefix_minima F G
    (fun l => Standard.parabolicScheme i ν (J l))
    (fun l => Standard.parabolicHom i ν (J l))
    (fun l => Standard.isClosedSubgroup_parabolicHom i ν (J l))
  refine ⟨d, j, ρ, ?_, hline, hmin⟩
  intro l Q x
  rw [← (Standard.isRepresentedBy_parabolicHom i ν (J l)).2]
  exact hρ l Q x

end Langlands.Global.RepresentationGrowth
