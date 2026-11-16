import Langlands.CommutativeAlgebra.FiniteLocalHenselianStatement
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteEtaleCover

/-! # A finite étale local refinement conditional on Henselian inheritance -/

universe u

open scoped TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinement

/-- A local finite étale target for an algebra, together with the actual map. -/
structure RefinementData (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] where
  Carrier : Type u
  [commRing : CommRing Carrier]
  [isLocalRing : IsLocalRing Carrier]
  [algebra : Algebra R Carrier]
  etale : Algebra.Etale R Carrier
  finite : Module.Finite R Carrier
  map : A →ₐ[R] Carrier

attribute [instance] RefinementData.commRing RefinementData.isLocalRing RefinementData.algebra

/-- A prime above the closed point of an étale algebra gives a map to a finite
étale local algebra, assuming Henselianity passes to finite local algebras. -/
theorem exists_local_finite_etale_refinement
    (hH : FiniteLocalHenselianStatement.{u,u})
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
  let : HenselianLocalRing L := hH R L
  let : Algebra L K := π.toRingHom.toAlgebra
  let : IsScalarTower R L K :=
    .of_algebraMap_eq fun r => (π.commutes r).symm
  let φ : L ⊗[R] A →ₐ[L] K :=
    AlgHom.liftEquiv R L A K (IsScalarTower.toAlgHom R A K)
  have hsurj : Function.Surjective (algebraMap L K) := hπ
  obtain ⟨σ, -⟩ := HenselianSections.exists_lift_of_etale hsurj φ
  exact ⟨L, inferInstance, hloc, inferInstance, het, hfin,
    ⟨(σ.restrictScalars R).comp Algebra.TensorProduct.includeRight⟩⟩

/-- Choose the refinement constructed above. The only unproved input is the
explicit finite-local Henselian inheritance proposition. -/
noncomputable def refinementOfPrime
    (hH : FiniteLocalHenselianStatement.{u,u})
    {R A : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    RefinementData R A := by
  classical
  apply Classical.choice
  obtain ⟨L, _, _, _, het, hfin, ⟨φ⟩⟩ := exists_local_finite_etale_refinement hH (R := R) (A := A) q
  exact ⟨{
    Carrier := L
    commRing := inferInstance
    isLocalRing := inferInstance
    algebra := inferInstance
    etale := het
    finite := hfin
    map := φ }⟩

end Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinement
