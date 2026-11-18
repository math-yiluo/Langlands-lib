import Langlands.CommutativeAlgebra.EtaleResidueExtensions
import Langlands.CommutativeAlgebra.HenselianEtaleAlgebraLift
import Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof

/-! # Pointed separable residue extensions over strictly Henselian algebras -/

noncomputable section

universe u

namespace Langlands.CommutativeAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- Etale completion approximation holds at every prime of a finite-type
integer algebra. -/
theorem etaleCompletionApproximation_atPrime
    (T : Type u) [CommRing T] [Algebra.FiniteType ℤ T]
    (q : Ideal T) [q.IsPrime] :
    EtaleCompletionApproximation (Localization.AtPrime q) := by
  have : IsNoetherianRing T := (finiteTypeIntGRing T).isNoetherianRing
  exact etaleCompletionApproximation_of_regularAlgebra_completion
    (Localization.AtPrime q) ((finiteTypeIntGRing T).regularAlgebra_completion q)

/-- A finite separable residue extension can be realized by an etale algebra
mapping to a prescribed Henselian algebra with separably closed residue field. -/
theorem exists_pointed_etale_residue_extension
    {T A k K : Type u} [CommRing T] [CommRing A] [HenselianLocalRing A]
    [Algebra T A] [Field k] [IsSepClosed k] [Algebra A k] [Algebra T k]
    [IsScalarTower T A k] (hk : Function.Surjective (algebraMap A k))
    (q : Ideal T) [q.IsPrime] [Algebra q.ResidueField k]
    [IsScalarTower T q.ResidueField k]
    [Field K] [Algebra q.ResidueField K] [Algebra T K]
    [IsScalarTower T q.ResidueField K]
    [FiniteDimensional q.ResidueField K] [Algebra.IsSeparable q.ResidueField K] :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra T E), Algebra.Etale T E ∧
      ∃ (Q : PrimeSpectrum E) (e : Q.asIdeal.ResidueField ≃+* K) (σ : E →ₐ[T] A),
        Q.asIdeal.comap (algebraMap T E) = q ∧
        (∀ t : T, e (algebraMap E Q.asIdeal.ResidueField (algebraMap T E t)) =
          algebraMap T K t) ∧
        (IsLocalRing.maximalIdeal A).comap σ.toRingHom = Q.asIdeal ∧
        ∃ σloc : Localization.AtPrime Q.asIdeal →ₐ[T] A,
          σloc.comp (IsScalarTower.toAlgHom T E _) = σ ∧
            IsLocalHom σloc.toRingHom := by
  obtain ⟨E, _, _, hE, Q, e, hQ, he⟩ := exists_etale_residue_extension T q K
  let ι : K →ₐ[q.ResidueField] k := IsSepClosed.lift
  let ρ : E →ₐ[T] K :=
    { toRingHom := e.toRingHom.comp (algebraMap E Q.asIdeal.ResidueField)
      commutes' := he }
  let ιT : K →ₐ[T] k := ι.restrictScalars T
  let φ : E →ₐ[T] k := ιT.comp ρ
  have hker : RingHom.ker φ.toRingHom = Q.asIdeal := by
    change RingHom.ker (ι.toRingHom.comp
      (e.toRingHom.comp (algebraMap E Q.asIdeal.ResidueField))) = _
    rw [RingHom.ker_comp_of_injective _ ι.toRingHom.injective,
      RingHom.ker_comp_of_injective _ e.injective, Ideal.ker_algebraMap_residueField]
  obtain ⟨σ, hσ⟩ := HenselianEtaleAlgebraLift.exists_lift hk φ
  have hσQ : (IsLocalRing.maximalIdeal A).comap σ.toRingHom = Q.asIdeal := by
    rw [← IsLocalRing.ker_eq_maximalIdeal (algebraMap A k) hk, RingHom.comap_ker]
    change RingHom.ker
      (((Algebra.ofId A k).restrictScalars T).comp σ).toRingHom = _
    rw [hσ]
    exact hker
  have hu : ∀ y : Q.asIdeal.primeCompl, IsUnit (σ y) := by
    intro y
    apply HenselianSections.isUnit_of_algebraMap_ne_zero hk
    change (((Algebra.ofId A k).restrictScalars T).comp σ) y ≠ 0
    rw [hσ]
    intro hy
    apply y.2
    exact hker.le hy
  let σloc : Localization.AtPrime Q.asIdeal →ₐ[T] A := IsLocalization.liftAlgHom hu
  have hloc : σloc.comp (IsScalarTower.toAlgHom T E _) = σ := by
    ext x
    exact IsLocalization.lift_eq hu x
  let ψ : Q.asIdeal.ResidueField →+* k := ι.toRingHom.comp e.toRingHom
  have hψ : ψ.comp (algebraMap (Localization.AtPrime Q.asIdeal) Q.asIdeal.ResidueField) =
      (algebraMap A k).comp σloc.toRingHom := by
    apply IsLocalization.ringHom_ext Q.asIdeal.primeCompl
    ext x
    change ψ (algebraMap E Q.asIdeal.ResidueField x) =
      algebraMap A k (σloc (algebraMap E (Localization.AtPrime Q.asIdeal) x))
    have hlocx : σloc (algebraMap E (Localization.AtPrime Q.asIdeal) x) = σ x :=
      AlgHom.congr_fun hloc x
    rw [hlocx]
    exact (AlgHom.congr_fun hσ x).symm
  have hlocal : IsLocalHom σloc.toRingHom := by
    have hcomp : IsLocalHom ((algebraMap A k).comp σloc.toRingHom) := by
      rw [← hψ]
      have : IsLocalHom (algebraMap (Localization.AtPrime Q.asIdeal)
        Q.asIdeal.ResidueField) :=
        IsLocalHom.of_surjective _ IsLocalRing.residue_surjective
      infer_instance
    exact isLocalHom_of_comp σloc.toRingHom (algebraMap A k)
  exact ⟨E, inferInstance, inferInstance, hE, Q, e, σ, hQ, he, hσQ, σloc, hloc, hlocal⟩

end Langlands.CommutativeAlgebra
