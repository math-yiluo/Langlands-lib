import Langlands.AlgebraicGeometry.SmoothAlgClosedFactorialStalksStatement
import Langlands.CommutativeAlgebra.SmoothAlgClosedFactorialLocalizations
import Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion
import Langlands.CommutativeAlgebra.MvPowerSeriesFactorial
import Langlands.CommutativeAlgebra.MvPowerSeriesCoordinateChange

/-! # Factorial stalks of smooth schemes over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry

/-- Reduction to rings: if every prime localization of a smooth algebra over an algebraically
closed field is factorial, then so is every stalk of a smooth scheme over such a field. -/
theorem smoothAlgClosedFactorialStalks_of_localizations
    (hRing : ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : Type u) [CommRing A] [Algebra K A],
      Algebra.Smooth K A → ∀ (P : Ideal A) [P.IsPrime],
        UniqueFactorizationMonoid (Localization.AtPrime P)) :
    SmoothAlgClosedFactorialStalks.{u} := by
  intro K _ _ X p hp x
  let := hp
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let U := X.affineCover.X i
  let q := X.affineCover.f i ≫ p
  have : Smooth q := inferInstance
  let g : CommRingCat.of K ⟶ Γ(U, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop
  have hg : g.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appTop @Smooth q inferInstance)
  algebraize [g.hom]
  have : Algebra.Smooth K Γ(U, ⊤) := RingHom.smooth_algebraMap.mp hg
  let P := ((isAffineOpen_top U).primeIdealOf ⟨y, trivial⟩).asIdeal
  have hP : UniqueFactorizationMonoid (Localization.AtPrime P) := hRing K _ inferInstance P
  let := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, trivial⟩ : (⊤ : U.Opens))
  have := (isAffineOpen_top U).isLocalization_stalk ⟨y, trivial⟩
  have hU : UniqueFactorizationMonoid (U.presheaf.stalk y) :=
    (IsLocalization.algEquiv P.primeCompl (U.presheaf.stalk y)
      (Localization.AtPrime P)).toRingEquiv.toMulEquiv.symm.uniqueFactorizationMonoid hP
  exact (asIso ((X.affineCover.f i).stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv.symm
    |>.uniqueFactorizationMonoid hU

/-- Every stalk of a smooth scheme over an algebraically closed field is factorial, provided
power series rings in finitely many variables over such fields are factorial. -/
theorem smoothAlgClosedFactorialStalks_of_mvPowerSeries
    (hps : ∀ (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ),
      UniqueFactorizationMonoid (MvPowerSeries (Fin n) K)) :
    SmoothAlgClosedFactorialStalks.{u} :=
  smoothAlgClosedFactorialStalks_of_localizations fun K _ _ _ _ _ _ P _ =>
    Langlands.CommutativeAlgebra.uniqueFactorizationMonoid_localization_of_smooth
      (fun R _ _ _ _ _ hK =>
        let ⟨n, ⟨e⟩⟩ :=
          Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion.exists_algEquiv_mvPowerSeries
            (K := K) (R := R) hK
        ⟨n, ⟨e.toRingEquiv⟩⟩)
      (hps K) P

open Langlands.CommutativeAlgebra.MvPowerSeriesFactorial in
/-- **Every stalk of a scheme smooth over an algebraically closed field is a unique
factorization domain.** -/
theorem smoothAlgClosedFactorialStalks : SmoothAlgClosedFactorialStalks.{u} :=
  smoothAlgClosedFactorialStalks_of_mvPowerSeries fun K _ _ n =>
    uniqueFactorizationMonoid_of_coord K
      (fun _ _ hf => exists_algEquiv_coeff_single_zero_ne_zero hf) n

end Langlands.AlgebraicGeometry
