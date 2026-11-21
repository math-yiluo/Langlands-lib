import Langlands.CommutativeAlgebra.StrictHenselianDvrExtension

/-! # A strictly Henselian DVR extension preserving a chosen uniformizer -/

noncomputable section

open IsLocalRing

set_option autoImplicit false

universe u

namespace Langlands.CommutativeAlgebra

/-- A strictly Henselian DVR inside the algebraic closure of the given fraction
field. The actual local map preserves the supplied uniformizer. -/
structure StrictHenselianDvrAt (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (π : R) where
  ring : Subalgebra R (AlgebraicClosure K)
  [dvr : IsDiscreteValuationRing ring]
  [henselian : HenselianLocalRing ring]
  [sepClosed : IsSepClosed (ResidueField ring)]
  localHom : IsLocalHom (algebraMap R ring)
  uniformizer : Irreducible (algebraMap R ring π)

attribute [instance] StrictHenselianDvrAt.dvr StrictHenselianDvrAt.henselian
  StrictHenselianDvrAt.sepClosed

/-- Choose a maximal fixed-uniformizer subalgebra of the algebraic closure of
the given fraction field. -/
def strictHenselianDvrAt (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π) : StrictHenselianDvrAt R K π := by
  let Ω := AlgebraicClosure K
  let : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr (by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K))
  let hex := FixedUniformizer.exists_maximal (Ω := Ω) hπ
  let S := Classical.choose hex
  have hS := Classical.choose_spec hex
  let : IsDiscreteValuationRing S := FixedUniformizer.isDiscreteValuationRing hπ.ne_zero hS.1
  exact
    { ring := S
      henselian := FixedUniformizer.henselianLocalRing hS
      sepClosed := FixedUniformizer.isSepClosed_residueField hS
      localHom := FixedUniformizer.isLocalHom hπ hS.1
      uniformizer := FixedUniformizer.irreducible hS.1 }

namespace StrictHenselianDvrAt

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R}

/-- The actual inclusion from the supplied fraction field into the fraction field
of the selected strictly Henselian DVR. -/
def fractionMap (T : StrictHenselianDvrAt R K π) : K →ₐ[R] FractionRing T.ring := by
  refine IsFractionRing.liftAlgHom (g := Algebra.ofId R (FractionRing T.ring)) ?_
  change Function.Injective (algebraMap R (FractionRing T.ring))
  rw [IsScalarTower.algebraMap_eq R T.ring (FractionRing T.ring)]
  apply (IsFractionRing.injective T.ring (FractionRing T.ring)).comp
  intro a b h
  apply (IsFractionRing.injective R K)
  apply (algebraMap K (AlgebraicClosure K)).injective
  exact (congrArg (fun x : T.ring => (x : AlgebraicClosure K)) h)

omit [IsDomain R] [IsFractionRing R K] in
/-- The local extension preserves residue characteristic zero. -/
theorem charZero_residue (T : StrictHenselianDvrAt R K π)
    [IsLocalRing R] [CharZero (ResidueField R)] : CharZero (ResidueField T.ring) := by
  let : IsLocalHom (algebraMap R T.ring) := T.localHom
  exact charZero_of_injective_ringHom
    (ResidueField.map (algebraMap R T.ring)).injective

end StrictHenselianDvrAt

end Langlands.CommutativeAlgebra
