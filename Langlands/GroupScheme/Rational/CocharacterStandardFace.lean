import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement

/-! # The standard face of a dominant cocharacter

A cocharacter of the maximal split torus pairing nonnegatively with every simple
relative root is standard for the simple roots it annihilates. Under the actual
root-sign criterion for inclusions of dynamic parabolics, its dynamic parabolic is
the standard parabolic of that face, and every dynamic parabolic of a cocharacter of
the torus containing the generic one arises this way.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

section Face

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The simple relative roots annihilated by a cocharacter. -/
def simpleRootFace (xi : cocharacterLattice T) : Set (characterLattice T) :=
  {α | α ∈ simpleRelativeRoots i ν ∧ latticePairing T α xi = 0}

theorem simpleRootFace_subset (xi : cocharacterLattice T) :
    simpleRootFace i ν xi ⊆ simpleRelativeRoots i ν :=
  fun _ hα => hα.1

/-- A cocharacter pairing nonnegatively with every simple relative root is standard
for the face of simple roots it annihilates. -/
theorem isStandardCocharacter_simpleRootFace {xi : cocharacterLattice T}
    (hxi : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing T α xi) :
    IsStandardCocharacter i ν (simpleRootFace i ν xi) xi := by
  refine ⟨simpleRootFace_subset i ν xi, fun α hα => hα.2, fun α hα hαJ => ?_⟩
  rcases (hxi α hα).lt_or_eq with h | h
  · exact h
  · exact absurd ⟨hα, h.symm⟩ hαJ

/-- A standard cocharacter for a face is the only face it is standard for. -/
theorem IsStandardCocharacter.eq_simpleRootFace {J : Set (characterLattice T)}
    {xi : cocharacterLattice T} (hxi : IsStandardCocharacter i ν J xi) :
    J = simpleRootFace i ν xi := by
  ext α
  constructor
  · intro hα
    exact ⟨hxi.1 hα, hxi.2.1 α hα⟩
  · intro hα
    by_contra hαJ
    have := hxi.2.2 α hα.1 hαJ
    rw [hα.2] at this
    exact lt_irrefl 0 this

/-- If root-sign inclusion of nonnegative supports gives inclusion of dynamic
parabolics, then the dynamic parabolic of a standard cocharacter for `J` equals
the standard parabolic of `J`, on every test scheme. -/
theorem dynamicParabolic_eq_standardParabolic_of_isStandardCocharacter
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hparabolic : ∀ zeta eta : cocharacterLattice T,
      (∀ α ∈ relativeRoots i,
        0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta) →
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i))
    {J : Set (characterLattice T)} {xi : cocharacterLattice T}
    (hxi : IsStandardCocharacter i ν J xi) :
    Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i) = standardParabolic i ν J := by
  apply le_antisymm
  · intro U g hg
    rw [mem_standardParabolic]
    intro eta heta
    exact hparabolic xi eta (fun α hα hnonneg =>
      (hxi.root_pairing_implications_of_subset i ν hν hneg heta (Set.Subset.refl J) hα).1
        hnonneg) U hg
  · exact standardParabolic_le_dynamicParabolic i ν hxi

/-- If a dynamic parabolic of a cocharacter of the torus contains the generic
one, that cocharacter pairs nonnegatively with every positive relative root. -/
theorem pairing_nonneg_of_parabolic_le
    (hparabolic : ∀ zeta eta : cocharacterLattice T,
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) →
        ∀ α ∈ relativeRoots i,
          0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta)
    {xi : cocharacterLattice T}
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i))
    {α : characterLattice T} (hα : α ∈ positiveRelativeRoots i ν) :
    0 ≤ latticePairing T α xi :=
  hparabolic ν xi hle α hα.1 hα.2.le

/-- Under the root-sign criterion, a dynamic parabolic of a cocharacter of the
torus containing the generic one is the standard parabolic of the face of that
cocharacter. -/
theorem dynamicParabolic_eq_standardParabolic_simpleRootFace_of_le
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hparabolic : ∀ zeta eta : cocharacterLattice T,
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ↔
        ∀ α ∈ relativeRoots i,
          0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta)
    {xi : cocharacterLattice T}
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i)) :
    Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i) =
      standardParabolic i ν (simpleRootFace i ν xi) :=
  dynamicParabolic_eq_standardParabolic_of_isStandardCocharacter i ν hν hneg
    (fun zeta eta => (hparabolic zeta eta).2)
    (isStandardCocharacter_simpleRootFace i ν (fun _ hα =>
      pairing_nonneg_of_parabolic_le i ν (fun zeta eta => (hparabolic zeta eta).1) hle
        (simpleRelativeRoots_subset_positive i ν hα)))

/-- Existence form: some subset of the simple relative roots indexes the
standard parabolic equal to the given dynamic parabolic. -/
theorem exists_standardParabolic_eq_of_parabolic_le
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hparabolic : ∀ zeta eta : cocharacterLattice T,
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ↔
        ∀ α ∈ relativeRoots i,
          0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta)
    {xi : cocharacterLattice T}
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i)) :
    ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
      Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i) = standardParabolic i ν J :=
  ⟨simpleRootFace i ν xi, simpleRootFace_subset i ν xi,
    dynamicParabolic_eq_standardParabolic_simpleRootFace_of_le i ν hν hneg hparabolic hle⟩

end Face

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The published root-sign inclusion and root negation statements give the face
description for every connected reductive group, at their full field and universe
scope. -/
theorem dynamicParabolic_eq_standardParabolic_simpleRootFace_of_statements
    (hsigns : RelativeRootSignInclusionsStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ xi : cocharacterLattice T,
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
            Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i) →
          Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i) =
            standardParabolic i ν (simpleRootFace i ν xi) := by
  let _ := hG.isAffineHom
  intro hν xi hle
  exact dynamicParabolic_eq_standardParabolic_simpleRootFace_of_le i ν hν
    (hnegation k G hG T i hi)
    (fun zeta eta => (hsigns k G hG T i hi zeta eta).1) hle

/-- Existence form of the statement-level face description. -/
theorem exists_standardParabolic_eq_of_parabolic_le_of_statements
    (hsigns : RelativeRootSignInclusionsStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ xi : cocharacterLattice T,
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
            Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i) →
          ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
            Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i) =
              standardParabolic i ν J := by
  let _ := hG.isAffineHom
  intro hν xi hle
  exact ⟨simpleRootFace i ν xi, simpleRootFace_subset i ν xi,
    dynamicParabolic_eq_standardParabolic_simpleRootFace_of_statements
      hsigns hnegation hG T i hi ν hν xi hle⟩

end Langlands.GroupScheme
