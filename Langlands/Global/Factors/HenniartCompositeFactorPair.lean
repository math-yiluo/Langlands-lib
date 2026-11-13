import Langlands.Global.Factors.HenniartCompositeFactorDeterminant
import Langlands.Global.Factors.UnitaryPairFactorTransport
import Langlands.LocalFactor.NonabelianSystemFieldTransportPairEpsilon
import Langlands.LocalFactor.Abelian.SelfDualTransport
import Langlands.Correspondence.RankOneArithmeticEpsilonData

/-!
# The pair-factor clause for Henniart's composite map

If an isometry `T` between the relative Weil and automorphic images at a finite
place `v` has the pair L- and epsilon-factor clauses at `F_v`, then Henniart's
composite map at a p-adic field `K ≅ F_v` has the pair-factor clause at `K`.
-/

noncomputable section

universe uF uK uW uP uE

namespace Langlands.Global.PoleComparison

open NumberField Langlands.Weil.Local
open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality
open Langlands.LocalFactor.NonabelianSystem.FieldTransport

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- Transport of the pair-factor clause: if `T` has the pair L- and epsilon-factor
clauses at `F_v` for every additive character of `F_v`, then the composite at `K`
has them for every additive character of `K`. -/
theorem pairFactorCompatibility_henniartCompositeMap
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v)
    (hT : ∀ ψ : Correspondence.NontrivialAdditiveCharacter (padicField v),
      RelativeIsometryPairFactorCompatibility.{uF, uW, uP, uE} F E c v T ψ)
    (ψ : Correspondence.NontrivialAdditiveCharacter K) :
    Correspondence.LatticeMap.PairFactorCompatibility.{uK, uW, uF, uE} K
      (henniartCompositeMap F E c v h K f T) ψ := by
  subst h
  let _ := (padicFieldAt v rfl).algebra
  let ψv : Correspondence.NontrivialAdditiveCharacter (padicField v) :=
    PadicField.ConductorTransport.additiveCharacter K (padicFieldAt v rfl) f ψ
  obtain ⟨-, hTv⟩ := hT ψv
  refine ⟨(Correspondence.existsUnique_localSelfDualMeasure K ψ).exists, ?_⟩
  rintro ν hν ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.mp hy
  have hνv : Correspondence.IsSelfDualMeasure (padicField v) ψv
      (PadicField.AbelianTransport.haarMeasure K (padicFieldAt v rfl) f ν) :=
    (PadicField.AbelianTransport.isSelfDual_iff K (padicFieldAt v rfl) f ψ ν).mpr hν
  obtain ⟨hL, hε⟩ := hTv _ hνv ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩
  have hΦx : (henniartCompositeMap F E c v rfl K f T ⟨_, hx⟩ :
      PadicSupercuspidal.UnitaryLattice K) =
        completionSupercuspidalLatticeEquiv v rfl K f (T ⟨x₀, hx₀⟩) :=
    henniartCompositeMap_apply F E c v rfl K f T ⟨x₀, hx₀⟩
  have hΦy : (henniartCompositeMap F E c v rfl K f T ⟨_, hy⟩ :
      PadicSupercuspidal.UnitaryLattice K) =
        completionSupercuspidalLatticeEquiv v rfl K f (T ⟨y₀, hy₀⟩) :=
    henniartCompositeMap_apply F E c v rfl K f T ⟨y₀, hy₀⟩
  have hΦ : completionWeilEquiv v rfl K f = weilEquiv (padicFieldAt v rfl) K f.symm :=
    ContinuousMulEquiv.ext fun _ => rfl
  refine ⟨?_, ?_⟩
  · rw [hΦx, hΦy]
    change PadicSupercuspidal.IsUnitaryPairLFactor K ψ ν
      (PadicSupercuspidal.unitaryLatticeEquiv K (padicFieldAt v rfl) f (T ⟨x₀, hx₀⟩).1)
      (PadicSupercuspidal.unitaryLatticeEquiv K (padicFieldAt v rfl) f (T ⟨y₀, hy₀⟩).1)
      (LocalWeil.unitaryPairLFactor K
        (Weil.restrictUnitaryLatticeEquiv (completionWeilEquiv v rfl K f) x₀)
        (Weil.restrictUnitaryLatticeEquiv (completionWeilEquiv v rfl K f) y₀))
    rw [LocalWeil.unitaryPairLFactor_restrictUnitaryLatticeEquiv (padicField v) K _
      (localDegreeInt_completionWeilEquiv v rfl K f)]
    exact (PadicSupercuspidal.isUnitaryPairLFactor_unitaryLatticeEquiv_iff_transport
      f ψ ν _ _ _).mpr hL
  · intro eC ε hεK
    obtain ⟨e, hWv, hSv⟩ := hε (transportFamily (padicFieldAt v rfl) K f.symm eC)
      (transportAssignment (padicFieldAt v rfl) K f.symm ε)
      (isSystem_transportAssignment (padicFieldAt v rfl) K f.symm hεK)
    refine ⟨e, ?_, ?_⟩
    · change LocalWeil.IsUnitaryPairEpsilonFactor K eC ε hεK ψ
        (Weil.restrictUnitaryLatticeEquiv (completionWeilEquiv v rfl K f) x₀)
        (Weil.restrictUnitaryLatticeEquiv (completionWeilEquiv v rfl K f) y₀) e
      rw [hΦ]
      exact isUnitaryPairEpsilonFactor_transport (padicFieldAt v rfl) K f.symm eC ε hεK _ ψv ψ
        (fun _ => rfl) x₀ y₀ e hWv
    · rw [hΦx, hΦy]
      exact (PadicSupercuspidal.isUnitaryPairEpsilonFactor_unitaryLatticeEquiv_iff_transport
        f ψ ν _ _ e).mpr hSv

end Langlands.Global.PoleComparison
