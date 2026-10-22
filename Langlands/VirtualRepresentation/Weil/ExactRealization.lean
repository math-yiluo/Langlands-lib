import Langlands.VirtualRepresentation.Weil.Local
import Langlands.VirtualRepresentation.Exact

/-!
# Canonical realization of the irreducible lattice in exact K0

Forget irreducibility on genuine continuous representation classes, then extend
into the actual exact-sequence quotient. This constructs only the forward map.
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- Genuine classes of all finite-dimensional continuous complex representations. -/
abbrev ContinuousClasses :=
  IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)

/-- The actual exact-sequence quotient for all continuous complex representations. -/
abbrev ContinuousExactGroup :=
  ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)

/-- Forget only irreducibility. The same actual invertible intertwiner proves
compatibility with the source and target isomorphism relations. -/
def forgetIrreducibleClass :
    IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous ∧ A.IsIrreducible) →
      ContinuousClasses.{uG, uV} G :=
  Quotient.map (fun A => ⟨A.val, A.property.1⟩) (fun _ _ h => h)

/-- Forgetting irreducibility leaves the underlying representation class unchanged. -/
@[simp]
theorem forgetProperty_forgetIrreducibleClass
    (c : IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous ∧ A.IsIrreducible)) :
    forgetPropertyClass _ (forgetIrreducibleClass G c) = forgetPropertyClass _ c := by
  refine Quotient.inductionOn c ?_
  intro A
  rfl

/-- Forget the positive rank label and irreducibility, retaining continuity. -/
def basisContinuousClass (b : IrreducibleBasis.{uG, uV} G) : ContinuousClasses.{uG, uV} G :=
  forgetIrreducibleClass G b.2.val

@[simp]
theorem forgetProperty_basisContinuousClass (b : IrreducibleBasis.{uG, uV} G) :
    forgetPropertyClass _ (basisContinuousClass G b) = underlyingClass G b :=
  forgetProperty_forgetIrreducibleClass G b.2.val

/-- The retained continuous class has the dimension specified by the basis rank. -/
@[simp]
theorem classDegree_basisContinuousClass (b : IrreducibleBasis.{uG, uV} G) :
    ExactGrothendieckGroup.classDegree _ (basisContinuousClass G b) = (b.1 : ℕ) := by
  unfold ExactGrothendieckGroup.classDegree
  rw [forgetProperty_basisContinuousClass]
  exact congrArg (fun n : ℕ => (n : ℤ)) b.2.property

/-- Canonical integral extension into the genuine exact Grothendieck group.
No inverse, surjectivity or injectivity is included. -/
def realizeExact : IrreducibleLattice.{uG, uV} G →ₗ[ℤ] ContinuousExactGroup.{uG, uV} G :=
  extend (fun b => ExactGrothendieckGroup.ofClass _ (basisContinuousClass G b))

@[simp]
theorem realizeExact_generator (b : IrreducibleBasis.{uG, uV} G) :
    realizeExact G (generator b) = ExactGrothendieckGroup.ofClass _ (basisContinuousClass G b) := by
  simp [realizeExact, extend, generator]

@[simp]
theorem realizeExact_zero : realizeExact.{uG, uV} G 0 = 0 := (realizeExact G).map_zero

@[simp]
theorem realizeExact_add (v w : IrreducibleLattice.{uG, uV} G) :
    realizeExact G (v + w) = realizeExact G v + realizeExact G w := (realizeExact G).map_add v w

@[simp]
theorem realizeExact_smul (z : ℤ) (v : IrreducibleLattice.{uG, uV} G) :
    realizeExact G (z • v) = z • realizeExact G v := (realizeExact G).map_smul z v

variable {G}

/-- The quotient forgetful map evaluates on the supplied actual object. -/
@[simp]
theorem basisContinuousClass_basisClass (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    basisContinuousClass G (basisClass A hc hi n hn) = exactClassOf _ ⟨A, hc⟩ := rfl

/-- A genuine irreducible object maps to its own exact class. -/
@[simp]
theorem realizeExact_ofRepresentation (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    realizeExact G (ofRepresentation A hc hi n hn) =
      ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩ := by
  simpa only [ofRepresentation, basisContinuousClass_basisClass,
    ExactGrothendieckGroup.ofRepresentation] using
    realizeExact_generator G (basisClass A hc hi n hn)

variable (G)

/-- The rank-weighted lattice degree agrees with the exact degree as linear maps. -/
theorem degree_comp_realizeExact :
    (ExactGrothendieckGroup.degree _).comp (realizeExact.{uG, uV} G) = degree G := by
  apply Finsupp.lhom_ext
  intro b z
  have hs : Finsupp.single b z = z • generator b := by simp [generator]
  rw [hs, LinearMap.map_smul, LinearMap.map_smul]
  congr 1
  change ExactGrothendieckGroup.degree _ (realizeExact G (generator b)) = degree G (generator b)
  rw [realizeExact_generator]
  change ExactGrothendieckGroup.lift _ _ _ _ = _
  rw [ExactGrothendieckGroup.lift_ofClass, classDegree_basisContinuousClass]
  simp [degree, rankedDegree, VirtualRepresentation.degree, extend, generator]

@[simp]
theorem degree_realizeExact (v : IrreducibleLattice.{uG, uV} G) :
    ExactGrothendieckGroup.degree _ (realizeExact G v) = degree G v :=
  LinearMap.congr_fun (degree_comp_realizeExact G) v

/-- A specified finite irreducible combination expands an exact class precisely
when its canonical image equals that class. Existence and uniqueness are separate. -/
def ExactExpansion (x : ContinuousExactGroup.{uG, uV} G)
    (v : IrreducibleLattice.{uG, uV} G) : Prop := realizeExact G v = x

@[simp]
theorem exactExpansion_iff (x : ContinuousExactGroup.{uG, uV} G)
    (v : IrreducibleLattice.{uG, uV} G) :
    ExactExpansion G x v ↔ realizeExact G v = x := Iff.rfl

/-- Every supplied combination expands its own image. -/
theorem exactExpansion_realizeExact (v : IrreducibleLattice.{uG, uV} G) :
    ExactExpansion G (realizeExact G v) v := rfl

@[simp]
theorem exactExpansion_generator_iff (x : ContinuousExactGroup.{uG, uV} G)
    (b : IrreducibleBasis.{uG, uV} G) :
    ExactExpansion G x (generator b) ↔
      ExactGrothendieckGroup.ofClass _ (basisContinuousClass G b) = x := by
  rw [exactExpansion_iff, realizeExact_generator]

@[simp]
theorem exactExpansion_zero_iff (x : ContinuousExactGroup.{uG, uV} G) :
    ExactExpansion G x 0 ↔ x = 0 := by
  rw [exactExpansion_iff, realizeExact_zero, eq_comm]

/-- An asserted expansion has the correct genuine virtual dimension. -/
theorem ExactExpansion.degree_eq {x : ContinuousExactGroup.{uG, uV} G}
    {v : IrreducibleLattice.{uG, uV} G} (h : ExactExpansion G x v) :
    ExactGrothendieckGroup.degree _ x = degree G v := by
  rw [← h, degree_realizeExact]

variable {G}

@[simp]
theorem exactExpansion_ofRepresentation_iff (x : ContinuousExactGroup.{uG, uV} G)
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hc : A.IsContinuous)
    (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    ExactExpansion G x (ofRepresentation A hc hi n hn) ↔
      ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩ = x := by
  rw [exactExpansion_iff, realizeExact_ofRepresentation]

end Langlands.VirtualRepresentation.Weil

namespace Langlands.VirtualRepresentation.LocalWeil

universe uF uW

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Exact K0 of all continuous representations of the actual local Weil group. -/
abbrev ContinuousExactGroup := Weil.ContinuousExactGroup.{uF, uW} (localWeilGroup F)

/-- The generic forward map on the existing actual local irreducible lattice. -/
abbrev realizeExact : Lattice.{uF, uW} F →ₗ[ℤ] ContinuousExactGroup.{uF, uW} F :=
  Weil.realizeExact (localWeilGroup F)

/-- Expansion in the existing local lattice, using the actual local Weil group. -/
abbrev ExactExpansion (x : ContinuousExactGroup.{uF, uW} F) (v : Lattice.{uF, uW} F) : Prop :=
  Weil.ExactExpansion (localWeilGroup F) x v

@[simp]
theorem realizeExact_generator (b : Basis.{uF, uW} F) :
    realizeExact F (generator b) =
      ExactGrothendieckGroup.ofClass _ (Weil.basisContinuousClass (localWeilGroup F) b) :=
  Weil.realizeExact_generator (localWeilGroup F) b

@[simp]
theorem degree_realizeExact (v : Lattice.{uF, uW} F) :
    ExactGrothendieckGroup.degree _ (realizeExact F v) = degree F v :=
  Weil.degree_realizeExact (localWeilGroup F) v

@[simp]
theorem exactExpansion_iff (x : ContinuousExactGroup.{uF, uW} F) (v : Lattice.{uF, uW} F) :
    ExactExpansion F x v ↔ realizeExact F v = x := Iff.rfl

variable {F}

@[simp]
theorem realizeExact_ofRepresentation
    (A : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F))
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    realizeExact F (ofRepresentation A hc hi n hn) =
      ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩ :=
  Weil.realizeExact_ofRepresentation A hc hi n hn

end Langlands.VirtualRepresentation.LocalWeil
