import Langlands.VirtualRepresentation.Weil.Generic
import Langlands.Weil.Representation.DualClasses

/-!
# Duality on the genuine irreducible integral lattice

The involution extends the actual full algebraic dual on continuous irreducible
classes. It preserves rank, integral degree, coefficients and their pairing.
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Dualize each genuine irreducible class, retaining its positive rank. -/
def dualBasisEquiv :
    IrreducibleBasis.{uG, uV} G ≃ IrreducibleBasis.{uG, uV} G :=
  Equiv.sigmaCongrRight (fun n =>
    FiniteRepresentation.continuousIrreducibleDualEquiv (n : ℕ))

@[simp]
theorem dualBasisEquiv_rank (b : IrreducibleBasis.{uG, uV} G) :
    (dualBasisEquiv b).1 = b.1 := rfl

/-- Forgetting the certificates recovers the genuine dual isomorphism class. -/
@[simp]
theorem underlyingClass_dualBasisEquiv (b : IrreducibleBasis.{uG, uV} G) :
    underlyingClass G (dualBasisEquiv b) =
      FiniteRepresentation.dualClass (underlyingClass G b) :=
  FiniteRepresentation.forget_continuousIrreducibleDualEquiv _ b.2

@[simp]
theorem dualBasisEquiv_symm :
    (dualBasisEquiv.{uG, uV} (G := G)).symm = dualBasisEquiv := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  rfl

@[simp]
theorem dualBasisEquiv_apply_apply (b : IrreducibleBasis.{uG, uV} G) :
    dualBasisEquiv (dualBasisEquiv b) = b := by
  simpa only [dualBasisEquiv_symm] using
    (dualBasisEquiv (G := G)).symm_apply_apply b

@[simp]
theorem dualBasisEquiv_trans_self :
    (dualBasisEquiv.{uG, uV} (G := G)).trans dualBasisEquiv =
      Equiv.refl (IrreducibleBasis.{uG, uV} G) := by
  apply Equiv.ext
  exact dualBasisEquiv_apply_apply

/-- The actual full dual on representatives gives the basis involution. -/
theorem dualBasisEquiv_basisClass
    (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hc : A.IsContinuous) (hi : A.IsIrreducible)
    (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    dualBasisEquiv (basisClass A hc hi n hn) =
      basisClass (FiniteRepresentation.dual A)
        ((FiniteRepresentation.isContinuous_dual_iff A).mpr hc)
        ((FiniteRepresentation.isIrreducible_dual_iff A).mpr hi)
        n ((FiniteRepresentation.rank_dual A).trans hn) := rfl

/-- Extend the genuine dual-class involution by integral linearity. -/
def dualLatticeEquiv :
    IrreducibleLattice.{uG, uV} G ≃ₗ[ℤ] IrreducibleLattice.{uG, uV} G :=
  reindex dualBasisEquiv

@[simp]
theorem dualLatticeEquiv_single (b : IrreducibleBasis.{uG, uV} G) (m : ℤ) :
    dualLatticeEquiv (Finsupp.single b m) =
      Finsupp.single (dualBasisEquiv b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem dualLatticeEquiv_generator (b : IrreducibleBasis.{uG, uV} G) :
    dualLatticeEquiv (generator b) = generator (dualBasisEquiv b) :=
  dualLatticeEquiv_single b 1

/-- The coefficient of the dual class equals the original multiplicity. -/
@[simp]
theorem dualLatticeEquiv_coefficient (x : IrreducibleLattice.{uG, uV} G)
    (b : IrreducibleBasis.{uG, uV} G) :
    dualLatticeEquiv x (dualBasisEquiv b) = x b := by
  change x (dualBasisEquiv.symm (dualBasisEquiv b)) = x b
  exact congrArg x (dualBasisEquiv.symm_apply_apply b)

@[simp]
theorem dualLatticeEquiv_symm :
    (dualLatticeEquiv.{uG, uV} (G := G)).symm = dualLatticeEquiv := by
  simp [dualLatticeEquiv, reindex]

@[simp]
theorem dualLatticeEquiv_apply_apply (x : IrreducibleLattice.{uG, uV} G) :
    dualLatticeEquiv (dualLatticeEquiv x) = x := by
  simpa only [dualLatticeEquiv_symm] using
    (dualLatticeEquiv (G := G)).symm_apply_apply x

@[simp]
theorem dualLatticeEquiv_trans_self :
    (dualLatticeEquiv.{uG, uV} (G := G)).trans dualLatticeEquiv =
      LinearEquiv.refl ℤ (IrreducibleLattice.{uG, uV} G) := by
  simp only [dualLatticeEquiv, reindex, Finsupp.domLCongr_trans,
    dualBasisEquiv_trans_self, Finsupp.domLCongr_refl]

/-- Duality preserves the rank-weighted integer degree. -/
@[simp]
theorem degree_dualLatticeEquiv (x : IrreducibleLattice.{uG, uV} G) :
    degree G (dualLatticeEquiv x) = degree G x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    simp [degree, rankedDegree, VirtualRepresentation.degree, extend]

/-- Duality preserves the coefficient pairing on the genuine irreducible basis. -/
theorem multiplicityPairing_dualLatticeEquiv
    (x y : IrreducibleLattice.{uG, uV} G) :
    multiplicityPairing G (dualLatticeEquiv x) (dualLatticeEquiv y) =
      multiplicityPairing G x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m =>
    simp [multiplicityPairing, pairing, extend, coefficient]

/-- Duality preserves and reflects the effective cone. -/
theorem effective_dualLatticeEquiv_iff (x : IrreducibleLattice.{uG, uV} G) :
    dualLatticeEquiv x ∈ VirtualRepresentation.effective ↔
      x ∈ VirtualRepresentation.effective := by
  change (∀ b, 0 ≤ dualLatticeEquiv x b) ↔ ∀ b, 0 ≤ x b
  constructor
  · intro h b
    simpa using h (dualBasisEquiv b)
  · intro h b
    obtain ⟨a, rfl⟩ := (dualBasisEquiv (G := G)).surjective b
    simpa using h a

end Langlands.VirtualRepresentation.Weil
