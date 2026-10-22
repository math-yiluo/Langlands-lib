import Langlands.Shimura.Coefficients.CompactCoefficient
import Langlands.Shimura.Coefficients.FiniteReduction

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open Langlands.Global CategoryTheory Opposite
open scoped TensorProduct

section Tower

variable {R : Type v} [CommRing R] {G : Type w} [Group G]
variable (I : Ideal R) (M : Action (ModuleCat.{u} R) G)

/-- The natural map between two congruence quotients of an integral representation. -/
def torsionCongruenceTransition {i j : ℕ} (h : i ≤ j) :
    G ⧸ congruenceKernel I M j →* G ⧸ congruenceKernel I M i :=
  QuotientGroup.map _ _ (MonoidHom.id G) (congruenceKernel_antitone I M h)

@[simp] theorem torsionCongruenceTransition_mk {i j : ℕ} (h : i ≤ j) (g : G) :
    torsionCongruenceTransition I M h (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

theorem torsionCongruenceTransition_surjective {i j : ℕ} (h : i ≤ j) :
    Function.Surjective (torsionCongruenceTransition I M h) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (congruenceKernel I M i) x
  exact ⟨QuotientGroup.mk g, rfl⟩

@[simp] theorem torsionCongruenceTransition_refl (n : ℕ) :
    torsionCongruenceTransition I M (le_refl n) = MonoidHom.id _ :=
  QuotientGroup.map_id _ _

@[simp] theorem torsionCongruenceTransition_comp {i j k : ℕ} (h : i ≤ j) (h' : j ≤ k) :
    (torsionCongruenceTransition I M h).comp (torsionCongruenceTransition I M h') =
      torsionCongruenceTransition I M (h.trans h') := by
  simpa only [torsionCongruenceTransition, MonoidHom.id_comp] using
    (QuotientGroup.map_comp_map (congruenceKernel I M k) (congruenceKernel I M j)
      (congruenceKernel I M i) (MonoidHom.id G) (MonoidHom.id G)
      (congruenceKernel_antitone I M h') (congruenceKernel_antitone I M h))

/-- Congruence quotients form a genuine inverse system of groups. -/
def torsionCongruenceGroups : ℕᵒᵖ ⥤ GrpCat.{w} where
  obj n := GrpCat.of (G ⧸ congruenceKernel I M n.unop)
  map f := GrpCat.ofHom (torsionCongruenceTransition I M (leOfHom f.unop))
  map_id n := by
    apply GrpCat.hom_ext
    exact torsionCongruenceTransition_refl I M n.unop
  map_comp f g := by
    apply GrpCat.hom_ext
    exact (torsionCongruenceTransition_comp I M (leOfHom g.unop) (leOfHom f.unop)).symm

end Tower

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W]
variable {σ : AlgebraInvolution ℚ A} {ρ : (σ.baseChange L).AlgebraicRepresentation W}
variable {p : FinitePlace ℚ} {l : FinitePlace L} [l.asIdeal.LiesOver p.asIdeal]
variable {U : Subgroup σ.FiniteAdelicPoints}

namespace StableCoefficientLattice

variable (Λ : StableCoefficientLattice ρ p l U) (m : ℕ)

/-- The actual image quotient of the integral level action modulo `(m)^n`. -/
abbrev RationalCongruenceGroup (n : ℕ) :=
  U ⧸ congruenceKernel (coefficientScalarIdeal l m) Λ.action n

/-- Changing from integral scalars to quotient-ring scalars leaves the action kernel unchanged. -/
theorem rationalTorsionAction_ker (n : ℕ) :
    (Λ.rationalTorsionAction l m n).ρ.ker =
      congruenceKernel (coefficientScalarIdeal l m) Λ.action n := by
  ext g
  change (Λ.rationalTorsionAction l m n).ρ g = 1 ↔
    (torsionAction (coefficientScalarIdeal l m) Λ.action n).ρ g = 1
  constructor
  · intro h
    apply ModuleCat.hom_ext
    ext x
    exact congrArg (fun f : End (Λ.rationalTorsionAction l m n).V => f.hom x) h
  · intro h
    apply ModuleCat.hom_ext
    ext x
    exact congrArg (fun f : End (torsionAction (coefficientScalarIdeal l m) Λ.action n).V =>
      f.hom x) h

/-- The coefficient action over the actual quotient ring, factored through its congruence group. -/
def rationalCongruenceAction (n : ℕ) :
    Action (ModuleCat.{u} (CoefficientReductionRing l m n))
      (Λ.RationalCongruenceGroup m n) where
  V := (Λ.rationalTorsionAction l m n).V
  ρ := QuotientGroup.lift _ (Λ.rationalTorsionAction l m n).ρ
    (by rw [Λ.rationalTorsionAction_ker])

@[simp] theorem rationalCongruenceAction_mk (n : ℕ) (g : U) :
    (Λ.rationalCongruenceAction m n).ρ (QuotientGroup.mk g) =
      (Λ.rationalTorsionAction l m n).ρ g := rfl

/-- The resulting quotient-group action is faithful. -/
theorem rationalCongruenceAction_injective (n : ℕ) :
    Function.Injective (Λ.rationalCongruenceAction m n).ρ := by
  unfold rationalCongruenceAction
  exact (QuotientGroup.injective_lift_iff _ _
    (by rw [Λ.rationalTorsionAction_ker])).mpr (Λ.rationalTorsionAction_ker m n).symm

/-- Each representation has a finite underlying coefficient module for nonzero `m`. -/
theorem rationalCongruenceAction_finite (hm : m ≠ 0) (n : ℕ) :
    Finite (Λ.rationalCongruenceAction m n).V :=
  Λ.rationalTorsionAction_finite l m hm n

/-- Higher rational congruence quotients map to lower ones by the identity on representatives. -/
abbrev rationalCongruenceTransition {i j : ℕ} (h : i ≤ j) :
    Λ.RationalCongruenceGroup m j →* Λ.RationalCongruenceGroup m i :=
  torsionCongruenceTransition (coefficientScalarIdeal l m) Λ.action h

/-- The actual inverse system of rational congruence quotient groups. -/
abbrev rationalCongruenceGroups : ℕᵒᵖ ⥤ GrpCat.{u} :=
  torsionCongruenceGroups (coefficientScalarIdeal l m) Λ.action

/-- Coefficient transitions intertwine the two quotient-group actions along the group transition.
The coefficient map retains integral scalars because its source and target quotient rings differ. -/
theorem rationalCongruenceTransition_equivariant {i j : ℕ} (h : i ≤ j)
    (g : Λ.RationalCongruenceGroup m j) (x : (Λ.rationalCongruenceAction m j).V) :
    ((Λ.rationalTorsionSystem l m).map (homOfLE h).op).hom.hom
        (((Λ.rationalCongruenceAction m j).ρ g).hom x) =
      ((Λ.rationalCongruenceAction m i).ρ (Λ.rationalCongruenceTransition m h g)).hom
        (((Λ.rationalTorsionSystem l m).map (homOfLE h).op).hom.hom x) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

end StableCoefficientLattice

section Compact

variable [Module.Finite L W] (ρ) (p l)
variable (U : CompactOpenLevel σ.FiniteAdelicPoints)

local instance : TopologicalSpace (FiniteCompletion L l ⊗[L] W) := coefficientTopology L l W

variable (hρ : ∀ x : FiniteCompletion L l ⊗[L] W,
  Continuous (fun g : (σ.baseChange L).Points (FiniteCompletion L l) =>
    ρ.act (FiniteCompletion L l) g x))

/-- The finite quotient-ring action built from the orbit-saturated compact-level lattice. -/
def compactFiniteCoefficientAction (m n : ℕ) :
    Action (ModuleCat.{u} (CoefficientReductionRing l m n))
      ((compactStableCoefficientLattice ρ p l U hρ).RationalCongruenceGroup m n) :=
  (compactStableCoefficientLattice ρ p l U hρ).rationalCongruenceAction m n

/-- Nonzero scalar reductions have both finite acting group and finite module. -/
theorem compactFiniteCoefficientAction_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite ((compactStableCoefficientLattice ρ p l U hρ).RationalCongruenceGroup m n) ∧
    Finite (compactFiniteCoefficientAction ρ p l U hρ m n).V :=
  ⟨(compactCoefficient_congruenceKernel ρ p l U hρ m hm n).2,
    (compactStableCoefficientLattice ρ p l U hρ).rationalCongruenceAction_finite m hm n⟩

end Compact

end Langlands.Shimura.Coefficients
