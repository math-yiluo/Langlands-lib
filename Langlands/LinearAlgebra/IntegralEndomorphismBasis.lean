import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # An integral matrix for an endomorphism with integral characteristic coefficients -/

noncomputable section

namespace Langlands.LinearAlgebra

open Module Polynomial Set

variable {O F V : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  [Field F] [Algebra O F] [IsFractionRing O F]
  [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V] [FiniteDimensional F V]

/-- An endomorphism with characteristic coefficients in a principal domain has a
basis over its fraction field in which all matrix entries belong to the domain. -/
def IntegralEndomorphismBasisStatement (T : Module.End F V) : Prop :=
  (∀ i : ℕ, T.charpoly.coeff i ∈ range (algebraMap O F)) →
  ∃ b : Basis (Fin (finrank F V)) F V,
    ∀ i j, LinearMap.toMatrix b b T i j ∈ range (algebraMap O F)

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
theorem integralEndomorphismBasis (T : Module.End F V) :
    IntegralEndomorphismBasisStatement (O := O) T := by
  classical
  intro hcoeff
  let T₀ : Basis (Fin (finrank F V)) F V := Module.finBasis F V
  let C := Algebra.adjoin O {T}
  have hInt : IsIntegral O T := by
    obtain ⟨p, hp, _, hpm⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts T.charpoly).mpr hcoeff) (LinearMap.charpoly_monic T)
    refine ⟨p, hpm, ?_⟩
    change aeval T p = 0
    rw [aeval_eq_aeval_map (IsScalarTower.algebraMap_eq O F (Module.End F V)).symm, hp]
    exact LinearMap.aeval_self_charpoly T
  let : Module.Finite O C := Algebra.finite_adjoin_simple_of_isIntegral hInt
  let ev (i : Fin (finrank F V)) : C →ₗ[O] V :=
    (LinearMap.applyₗ' O (T₀ i)).comp C.val.toLinearMap
  let f : (Fin (finrank F V) → C) →ₗ[O] V :=
    { toFun := fun a => ∑ i, ev i (a i)
      map_add' := fun a b => by simp [Finset.sum_add_distrib]
      map_smul' := fun a b => by simp [Finset.smul_sum] }
  let L := f.range
  have hB (i : Fin (finrank F V)) : T₀ i ∈ L := by
    let a : Fin (finrank F V) → C := Pi.single i 1
    refine ⟨a, ?_⟩
    change ∑ j, ev j (a j) = _
    rw [Finset.sum_eq_single i]
    · simp only [a, Pi.single_eq_same]
      rfl
    · intro j _ hji
      rw [show a j = 0 from Pi.single_eq_of_ne hji _, map_zero]
    · simp
  let : Submodule.IsLattice F L := ⟨Submodule.fg_range f, by
    rw [eq_top_iff, ← T₀.span_eq]
    exact Submodule.span_mono fun _ ⟨i, hi⟩ => hi ▸ hB i⟩
  have hStable (x : V) (hx : x ∈ L) : T x ∈ L := by
    obtain ⟨a, rfl⟩ := hx
    let t : C := ⟨T, Algebra.subset_adjoin rfl⟩
    refine ⟨fun i => t * a i, ?_⟩
    change ∑ i, ev i (t * a i) = T (∑ i, ev i (a i))
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hdim : finrank O L = finrank F V :=
    congrArg Cardinal.toNat (Submodule.IsLattice.rank' F L)
  let bO := Module.finBasisOfFinrankEq O L hdim
  let b := bO.extendOfIsLattice F
  refine ⟨b, fun i j => ?_⟩
  let y : L := ⟨T (b j), hStable _ (by simpa only [b, Basis.extendOfIsLattice_apply] using (bO j).property)⟩
  have hsum : (∑ k, algebraMap O F (bO.repr y k) • b k) = T (b j) := by
    change (∑ k, algebraMap O F (bO.repr y k) • b k) = (y : V)
    have h := congrArg (fun z : L => (z : V)) (bO.sum_repr y)
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, algebraMap_smul, b,
      Basis.extendOfIsLattice_apply] using h
  refine ⟨bO.repr y i, ?_⟩
  rw [LinearMap.toMatrix_apply, ← hsum]
  exact (congrFun (b.repr_sum_self (fun k => algebraMap O F (bO.repr y k))) i).symm

end Langlands.LinearAlgebra
