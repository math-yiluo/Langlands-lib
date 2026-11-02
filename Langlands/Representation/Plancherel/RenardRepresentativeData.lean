import Langlands.Representation.Plancherel.RenardUniformizerSection

/-! # Finite representatives in the actual character-valuation image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- The actual image of the split-torus points inside the actual character-
valuation image of the ambient algebraic group. -/
def splitValuationImage (s : T.toGrp ⟶ Z) :
    Subgroup (rationalCharacterValuationImage Z) :=
  (((rationalCharacterValuation Z).rangeRestrict).comp (rationalPoints.map s)).range

/-- The residue class in the actual quotient `Λ(Z)/image(Λ(S))`. -/
def latticeResidue (s : T.toGrp ⟶ Z) :
    rationalPoints Z →*
      (rationalCharacterValuationImage Z ⧸ splitValuationImage s) :=
  (QuotientGroup.mk' (splitValuationImage s)).comp
    (rationalCharacterValuation Z).rangeRestrict

/-- A finite set with exactly one representative in each full lattice coset.
This property alone does not impose chamber compatibility. -/
def IsFiniteLatticeTransversal (s : T.toGrp ⟶ Z) (F0 : Set (rationalPoints Z)) : Prop :=
  F0.Finite ∧ Function.Bijective (fun f : F0 => latticeResidue s f.val)

/-- The full representative set `C_0 F_0` of Renard V.3.23. -/
def tildeC0 (s : T.toGrp ⟶ Z) (F0 : Set (rationalPoints Z)) :
    Set (rationalPoints Z) :=
  (C0 T s : Set (rationalPoints Z)) * F0

/-- The dominant intersection `(C_0 F_0) ∩ Z_dom`.
The intended `dominant` is supplied by the actual centralizer valuation. -/
def tildeC0Plus (s : T.toGrp ⟶ Z) (F0 dominant : Set (rationalPoints Z)) :
    Set (rationalPoints Z) :=
  tildeC0 s F0 ∩ dominant

/-- Exactly one actual point for each value in the full actual valuation image. -/
def IsValuationSection (A : Set (rationalPoints Z)) : Prop :=
  Function.Bijective (fun a : A => (rationalCharacterValuation Z).rangeRestrict a.val)

/-- Exactly one point for each dominant actual valuation value, with all
representatives themselves in the supplied dominant set. -/
def IsDominantValuationSection (dominant A : Set (rationalPoints Z)) : Prop :=
  A ⊆ dominant ∧ Set.BijOn (rationalCharacterValuation Z).rangeRestrict A
    ((rationalCharacterValuation Z).rangeRestrict '' dominant)

/-- The additional rectangular condition used in Renard V.3.23.
It is separate from finite index and from positivity of the representatives. -/
def IsChamberCompatibleTransversal (s : T.toGrp ⟶ Z)
    (positiveRoots : Set (characterLattice T))
    (dominant F0 : Set (rationalPoints Z)) : Prop :=
  IsFiniteLatticeTransversal s F0 ∧ F0 ⊆ dominant ∧
    tildeC0Plus s F0 dominant = C0Plus T s positiveRoots * F0

/-- A finite positive product covering, which can use several representatives
in the same full lattice coset and can repeat valuation classes. -/
def IsFinitePositiveProductCover (s : T.toGrp ⟶ Z)
    (positiveRoots : Set (characterLattice T))
    (dominant Fcover : Set (rationalPoints Z)) : Prop :=
  Fcover.Finite ∧ Fcover ⊆ dominant ∧
    C0Plus T s positiveRoots * Fcover ⊆ dominant ∧
    Set.SurjOn (rationalCharacterValuation Z).rangeRestrict
      (C0Plus T s positiveRoots * Fcover)
      ((rationalCharacterValuation Z).rangeRestrict '' dominant)

/-- The distinct additional requirement that the product pairs give
nonrepeating valuation classes. -/
def HasNonrepeatingPositiveProducts (s : T.toGrp ⟶ Z)
    (positiveRoots : Set (characterLattice T)) (F0 : Set (rationalPoints Z)) : Prop :=
  Function.Injective (fun cf : C0Plus T s positiveRoots × F0 =>
    rationalCharacterValuation Z (cf.1.val * cf.2.val))

theorem mem_tildeC0 (s : T.toGrp ⟶ Z) (F0 : Set (rationalPoints Z))
    (z : rationalPoints Z) :
    z ∈ tildeC0 s F0 ↔ ∃ c ∈ C0 T s, ∃ f ∈ F0, c * f = z :=
  Set.mem_mul

theorem mem_tildeC0Plus (s : T.toGrp ⟶ Z) (F0 dominant : Set (rationalPoints Z))
    (z : rationalPoints Z) :
    z ∈ tildeC0Plus s F0 dominant ↔ z ∈ tildeC0 s F0 ∧ z ∈ dominant :=
  Iff.rfl

end Langlands.Plancherel.RenardCartan
