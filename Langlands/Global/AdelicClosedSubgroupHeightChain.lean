import Langlands.Global.AdelicHeightChain
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof

/-! # Actual closed subgroup chains and simultaneous adelic height minima -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Unit-scalar action on a coordinate line agrees in global-section and affine
coordinates, through the canonical section-algebra isomorphism. -/
theorem affine_coordinateLine_scalar_iff (ρ : MatrixRepresentation G n)
    (A : CommAlgCat.{u} R) (x : (algSpec R).obj (op A) ⟶ G.X) (j : n) :
    (∃ a : Γ(((algSpec R).obj (op A)).left, ⊤)ˣ,
      (ρ.pointMatrix ((algSpec R).obj (op A)) x :
          Matrix n n Γ(((algSpec R).obj (op A)).left, ⊤)) *ᵥ
          Pi.single j 1 =
        (a : Γ(((algSpec R).obj (op A)).left, ⊤)) •
          (Pi.single j 1 : n → Γ(((algSpec R).obj (op A)).left, ⊤))) ↔
    ∃ a : Aˣ, (ρ.affineMatrix A x : Matrix n n A) *ᵥ Pi.single j 1 =
      (a : A) • (Pi.single j 1 : n → A) := by
  let e := Corepresented.affineSectionsAlgEquiv A
  have hM (i l : n) :
      (ρ.pointMatrix ((algSpec R).obj (op A)) x) i l =
        e.symm ((ρ.affineMatrix A x) i l) := by
    rw [pointMatrix_eq_affineMatrix]
    rfl
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨Units.map e.toMonoidHom a, ?_⟩
    funext i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply,
      Pi.smul_apply, smul_eq_mul] at ha ⊢
    have hi := congrArg e (congrFun ha i)
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [hM, e.apply_symm_apply, map_mul] at hi
    have hs : e ((Pi.single j 1 : n → Γ(((algSpec R).obj (op A)).left, ⊤)) i) =
        (Pi.single j 1 : n → A) i := by
      by_cases hij : i = j <;> simp [hij]
    rw [hs] at hi
    exact hi
  · rintro ⟨a, ha⟩
    refine ⟨Units.map e.symm.toMonoidHom a, ?_⟩
    funext i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply,
      Pi.smul_apply, smul_eq_mul] at ha ⊢
    rw [hM]
    have hi := congrArg e.symm (congrFun ha i)
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [map_mul] at hi
    have hs : e.symm ((Pi.single j 1 : n → A) i) =
        (Pi.single j 1 : n → Γ(((algSpec R).obj (op A)).left, ⊤)) i := by
      by_cases hij : i = j <;> simp [hij]
    rw [hs] at hi
    exact hi

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Chevalley

/-- Chevalley's actual line stabilizer, expressed over every test algebra rather
than its canonically isomorphic ring of global sections. -/
theorem exists_affine_line_stabilizer
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (z : H ⟶ G)
    (hc : IsClosedSubgroup z) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
        (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X),
        x ∈ (SubgroupFunctor.range z).carrier ((algSpec _).obj (op A)) ↔
          ∃ a : Aˣ, (ρ.affineMatrix A x : Matrix (Fin (n + 1)) (Fin (n + 1)) A) *ᵥ
            Pi.single j 1 = (a : A) • (Pi.single j 1 : Fin (n + 1) → A) := by
  obtain ⟨n, j, ρ, hρ⟩ := exists_line_stabilizer k G H z hc
  refine ⟨n, j, ρ, fun A x => ?_⟩
  exact (hρ _ x).trans (ρ.affine_coordinateLine_scalar_iff A x j)

end Langlands.GroupScheme.Chevalley

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual rational subgroup in a specified chain of subgroup-scheme ranges.
The index is the minimizing subgroup, preceding the next adapted stabilizer. -/
def closedChainRationalSubgroup
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G)
    (i : ℕ) : Subgroup (RationalGroupPoints F G) :=
  (SubgroupFunctor.range (z i)).carrier
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))

omit [NumberField F] in
/-- A descending chain of actual subgroup functors gives a descending chain of
their rational point subgroups. -/
theorem closedChainRationalSubgroup_antitone
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G)
    (hz : Antitone (fun i => SubgroupFunctor.range (z i))) :
    Antitone (closedChainRationalSubgroup F G H z) :=
  fun _ _ hij => hz hij _

/-- Every descending chain of actual closed subgroups has adapted actual
representations whose finite-prefix minima coexist at a rational translate.
The representation at index `i` is adapted to `H (i+1)` and minimized over `H i`. -/
theorem exists_adapted_closedChain_minima
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (H : ℕ → GroupScheme (Spec (CommRingCat.of F))) (z : (i : ℕ) → H i ⟶ G)
    (hc : ∀ i, IsClosedSubgroup (z i))
    (hz : Antitone (fun i => SubgroupFunctor.range (z i))) :
    ∃ (d : ℕ → ℕ) (j : (i : ℕ) → Fin (d i + 1))
      (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i + 1))),
      (∀ i (A : CommAlgCat.{u} (CommRingCat.of F))
        (x : (algSpec (CommRingCat.of F)).obj (op A) ⟶ G.X),
        x ∈ (SubgroupFunctor.range (z (i + 1))).carrier ((algSpec _).obj (op A)) ↔
          ∃ a : Aˣ, ((ρ i).affineMatrix A x : Matrix (Fin (d i + 1)) (Fin (d i + 1)) A) *ᵥ
            Pi.single (j i) 1 = (a : A) • (Pi.single (j i) 1 : Fin (d i + 1) → A)) ∧
      ∀ (r : ℕ) (g : normOneSubgroup F G),
        ∃ q : closedChainRationalSubgroup F G H z 0,
          g * rationalNormOne F G q ∈
            chainHeightMinimalSet F G r (fun i => d i + 1) ρ
              (fun i => Pi.single (j i) 1) (closedChainRationalSubgroup F G H z) 1 := by
  choose d j ρ hρ using fun i =>
    Chevalley.exists_affine_line_stabilizer F G (H (i + 1)) (z (i + 1)) (hc (i + 1))
  refine ⟨d, j, ρ, hρ, ?_⟩
  intro r g
  apply exists_mul_rational_mem_chainHeightMinimalSet F G r (fun i => d i + 1) ρ
    (fun i => Pi.single (j i) 1) ?_ (closedChainRationalSubgroup F G H z)
    (closedChainRationalSubgroup_antitone F G H z hz) ?_ g
  · intro i _ hzero
    have hi := congrFun hzero (j i)
    simp at hi
  · intro i l hil _ q
    exact (hρ i (CommAlgCat.of F F) q).1
      (hz (Nat.succ_le_of_lt hil) _ q.property)

/-- The actual standard parabolics of a descending chain of simple-root subsets
admit adapted representations and simultaneous finite-prefix height minima.
No line-action or rational-subgroup nesting assumption is added. -/
theorem exists_adapted_standardParabolicChain_minima
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν)
    (J : ℕ → Set (characterLattice T))
    (hJ : ∀ l, J l ⊆ simpleRelativeRoots i ν) (hmono : Antitone J) :
    ∃ (d : ℕ → ℕ) (j : (l : ℕ) → Fin (d l + 1))
      (ρ : (l : ℕ) → MatrixRepresentation G (Fin (d l + 1))),
      (∀ l (A : CommAlgCat.{u} (CommRingCat.of F))
        (x : (algSpec (CommRingCat.of F)).obj (op A) ⟶ G.X),
        x ∈ (standardParabolic i ν (J (l + 1))).carrier ((algSpec _).obj (op A)) ↔
          ∃ a : Aˣ, ((ρ l).affineMatrix A x : Matrix (Fin (d l + 1)) (Fin (d l + 1)) A) *ᵥ
            Pi.single (j l) 1 = (a : A) • (Pi.single (j l) 1 : Fin (d l + 1) → A)) ∧
      ∀ (r : ℕ) (g : normOneSubgroup F G),
        ∃ q : (standardParabolic i ν (J 0)).carrier
            ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))),
          g * rationalNormOne F G q ∈
            chainHeightMinimalSet F G r (fun l => d l + 1) ρ
              (fun l => Pi.single (j l) 1)
              (fun l => (standardParabolic i ν (J l)).carrier
                ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))) 1 := by
  have he (l : ℕ) :
      SubgroupFunctor.range (Standard.parabolicHom i ν (J l)) =
        standardParabolic i ν (J l) :=
    (Standard.isRepresentedBy_parabolicHom i ν (J l)).2
  have hz : Antitone (fun l => SubgroupFunctor.range (Standard.parabolicHom i ν (J l))) := by
    intro a b hab
    change SubgroupFunctor.range (Standard.parabolicHom i ν (J b)) ≤
      SubgroupFunctor.range (Standard.parabolicHom i ν (J a))
    rw [he, he]
    exact ((standardParabolicOrder F G hG T i hi ν hν).1
      (J b) (J a) (hJ b) (hJ a)).1.mp (hmono hab)
  obtain ⟨d, j, ρ, hρ, hmin⟩ := exists_adapted_closedChain_minima F G
    (fun l => Standard.parabolicScheme i ν (J l))
    (fun l => Standard.parabolicHom i ν (J l))
    (fun l => Standard.isClosedSubgroup_parabolicHom i ν (J l)) hz
  have hQ : closedChainRationalSubgroup F G
      (fun l => Standard.parabolicScheme i ν (J l))
      (fun l => Standard.parabolicHom i ν (J l)) =
      (fun l => (standardParabolic i ν (J l)).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))) := by
    funext l
    exact congrArg (fun S : SubgroupFunctor G =>
      S.carrier ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))) (he l)
  refine ⟨d, j, ρ, ?_, ?_⟩
  · simpa only [he] using hρ
  · intro r g
    obtain ⟨q, hq⟩ := hmin r g
    refine ⟨⟨q.val, ?_⟩, ?_⟩
    · rw [← he 0]
      exact q.property
    · simpa only [hQ] using hq

end Langlands.Global.RepresentationGrowth
