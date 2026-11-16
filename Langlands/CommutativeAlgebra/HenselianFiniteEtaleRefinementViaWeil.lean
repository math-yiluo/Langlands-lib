import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinement
import Langlands.CommutativeAlgebra.HenselianFiniteEtaleResidueComparison
import Langlands.CommutativeAlgebra.HenselianWeilLifting

/-! # Finite étale local refinement via Weil restriction -/

universe u

open scoped TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinement

/-- A closed-fibre prime of an étale algebra over a Henselian local ring gives
an actual algebra map to a finite étale local algebra. -/
theorem exists_local_finite_etale_refinement_via_weil
    {R A : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R'),
      Algebra.Etale R R' ∧ Module.Finite R R' ∧ Nonempty (A →ₐ[R] R') := by
  let m := IsLocalRing.maximalIdeal R
  let K := q.ResidueField
  let := Localization.AtPrime.algebraOfLiesOver m q
  have : Module.Finite m.ResidueField K := inferInstance
  have : Module.Finite R K := Module.Finite.trans (R := R) m.ResidueField K
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) := inferInstance
  have : Algebra.FormallyUnramified R K :=
    Algebra.FormallyUnramified.comp R (Localization.AtPrime q) K
  have hker : RingHom.ker (algebraMap R K) = m := by
    ext r
    change algebraMap R K r = 0 ↔ r ∈ m
    rw [IsScalarTower.algebraMap_apply R A K, Ideal.algebraMap_residueField_eq_zero]
    change r ∈ q.under R ↔ r ∈ m
    rw [← q.over_def m]
  have : IsLocalHom (algebraMap R K) := by
    refine ⟨fun r hr => ?_⟩
    by_contra h
    have hz : algebraMap R K r = 0 := by
      apply RingHom.mem_ker.mp
      rw [hker]
      exact h
    exact hr.ne_zero hz
  obtain ⟨L, _, _, hloc, hfin, het, π, hπ⟩ :=
    Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal.exists_etaleCover
      (R := R) (B := K)
  let : IsLocalRing L := hloc
  let : Module.Finite R L := hfin
  let : Algebra.Etale R L := het
  let : Algebra L K := π.toRingHom.toAlgebra
  let : IsScalarTower R L K :=
    .of_algebraMap_eq fun r => (π.commutes r).symm
  have : IsLocalHom ((algebraMap L K).comp (algebraMap R L)) := by
    rw [← IsScalarTower.algebraMap_eq R L K]
    infer_instance
  have : IsLocalHom (algebraMap R L) :=
    isLocalHom_of_comp (algebraMap R L) (algebraMap L K)
  have : Module.Free R L := Module.free_of_flat_of_isLocalRing
  let φ : L ⊗[R] A →ₐ[L] K :=
    AlgHom.liftEquiv R L A K (IsScalarTower.toAlgHom R A K)
  let e : L ⊗[R] IsLocalRing.ResidueField R ≃ₐ[L] K :=
    HenselianFiniteEtaleResidueComparison.tensorResidueCoverEquiv
      (R := R) (L := L) hπ
  obtain ⟨σ, -⟩ := HenselianSections.exists_lift_of_finite_projective_smooth
    (R := R) (k := IsLocalRing.ResidueField R)
    IsLocalRing.residue_surjective (e.symm.toAlgHom.comp φ)
  exact ⟨L, inferInstance, hloc, inferInstance, het, hfin,
    ⟨(σ.restrictScalars R).comp Algebra.TensorProduct.includeRight⟩⟩

/-- Choose the finite étale local refinement obtained by Weil restriction. -/
noncomputable def refinementOfPrimeViaWeil
    {R A : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    RefinementData R A := by
  classical
  apply Classical.choice
  obtain ⟨L, _, _, _, het, hfin, ⟨φ⟩⟩ :=
    exists_local_finite_etale_refinement_via_weil (R := R) (A := A) q
  exact ⟨{
    Carrier := L
    commRing := inferInstance
    isLocalRing := inferInstance
    algebra := inferInstance
    etale := het
    finite := hfin
    map := φ }⟩

end Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinement
