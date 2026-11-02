import Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingStatement
import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackAssembly
import Langlands.AbelianScheme.FieldMultiplicationPullbackOfCube
import Langlands.AbelianScheme.FieldMultiplicationFiniteEtale
import Langlands.AbelianScheme.AlgClosedPointDivisibility
import Langlands.AbelianScheme.MultiplicationSign
import Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.AmpleTensorProof
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingProof
import Langlands.AlgebraicGeometry.Modules.FiniteFlatCohomologyRetractProof

/-! # Ample higher-cohomology vanishing from the balanced cube identity -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules
open Langlands.Scheme.Modules

/-- Some natural number at least `n + 2` is nonzero in any field. -/
private theorem exists_ge_cast_ne_zero (K : Type u) [Field K] (n : ℕ) :
    ∃ k : ℕ, n + 2 ≤ k ∧ (k : K) ≠ 0 := by
  by_cases h : ((n + 2 : ℕ) : K) = 0
  · refine ⟨n + 3, by omega, ?_⟩
    have : ((n + 3 : ℕ) : K) = ((n + 2 : ℕ) : K) + 1 := by push_cast; ring
    rw [this, h, zero_add]
    exact one_ne_zero
  · exact ⟨n + 2, le_rfl, h⟩

/-- Both binomial exponents are at least `n` once `n + 2 ≤ k`. -/
private theorem le_choose_two {n k : ℕ} (hk : n + 2 ≤ k) : n ≤ Nat.choose k 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [Nat.choose_succ_succ, Nat.choose_one_right]
  omega

/-- The balanced cube identity implies the vanishing of the higher cohomology
of every ample line bundle on an abelian variety over an algebraically closed
field. Algebraic closure is used through `polarizedFiniteFlatRank`. Serre
vanishing and the finite flat retraction enter through their published
proofs. -/
theorem ampleLineBundleHigherCohomologyVanishing_of_cube
    (cube : GroupScheme.FieldCubePullbackStatement.{u}) :
    AmpleLineBundleHigherCohomologyVanishingStatement.{u} := by
  intro K _ _ A L hL i hi
  -- Inversion `σ = ψ₋₁` is an involutive automorphism of `A.X.left`.
  let σ := (GroupScheme.multiplication A.toGrp (-1)).hom.hom.left
  have hσσ : σ ≫ σ = 𝟙 _ := by
    have h := (GroupScheme.multiplicationNegOneIso A.toGrp).hom_inv_id
    exact congrArg (fun φ => φ.hom.hom.left) h
  have : IsIso σ := ⟨⟨σ, hσσ, hσσ⟩⟩
  let L' : LineBundle A.X.left := (LineBundle.pullback σ).obj L
  have hL' : L'.IsAmple := closedImmersionPullbackAmple _ _ σ L inferInstance hL
  -- The symmetric ample bundle `N = L ⊗ σ^*L`.
  let N : LineBundle A.X.left := LineBundle.tensor pullbackTensorComparisonIsIso L L'
  have hN : N.IsAmple := ampleTensor _ L L' N ⟨Iso.refl _⟩ hL hL'
  have hNsym : Nonempty ((Scheme.Modules.pullback σ).obj N.obj ≅ N.obj) := by
    refine ⟨pullbackTensorIso σ L.obj L'.obj ≪≫ ?_ ≪≫ tensorComm L'.obj L.obj⟩
    refine (tensorFunctor A.X.left).mapIso ((Iso.refl _).prod ?_)
    exact (Scheme.Modules.pullbackComp σ σ).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr hσσ).app L.obj ≪≫ (Scheme.Modules.pullbackId _).app L.obj
  -- A relative dimension `g`.
  have : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  obtain ⟨g, hg⟩ :=
    Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension _ _ A.X.hom inferInstance inferInstance
  -- Quadrant vanishing for `L` and `σ^*L`, and a large `k` invertible in `K`.
  have : (structureSheaf A.X.left).IsQuasicoherent :=
    (LineBundle.trivial A.X.left).property.isQuasicoherent
  obtain ⟨n₀, hn₀⟩ := properAmplePairSerreVanishing K A.X.left A.X.hom inferInstance
    (structureSheaf A.X.left) inferInstance
    (fun U => inferInstanceAs (Module.Finite Γ(A.X.left, U.1) Γ(A.X.left, U.1)))
    L L' hL hL'
  obtain ⟨k, hk, hkK⟩ := exists_ge_cast_ne_zero K n₀
  have hkpos : 0 < k := by omega
  let ψ := (GroupScheme.multiplication A.toGrp (k : ℤ)).hom.hom
  have hup : IsZero ((DerivedSections.relativeCohomology A.X.hom i).obj
      ((Scheme.Modules.pullback ψ.left).obj L.obj)) :=
    (hn₀ _ _ (le_choose_two (by omega)) (le_choose_two hk) i hi).of_iso
      ((DerivedSections.relativeCohomology A.X.hom i).mapIso
        (GroupScheme.fieldMultiplicationPullbackIsoOfCube cube K A.toGrp inferInstance
            inferInstance inferInstance L k ≪≫
          ((tensorFunctor A.X.left).mapIso ((tensorLeftUnitor _).prod (Iso.refl _))).symm))
  -- `ψ_k` is finite étale of constant rank `(k * k) ^ g`.
  have hfin : IsFinite ψ.left := multiplication_isFinite_of_ne_zero A k hkK
  have : Etale ψ.left := multiplication_etale_of_field A k hkK
  have hrank : ∀ y : A.X.left, ψ.left.finrank y = (k * k) ^ g :=
    polarizedFiniteFlatRank K A.X g hg inferInstance inferInstance ψ hfin inferInstance
      N hN (k * k) (Nat.mul_pos hkpos hkpos)
      (GroupScheme.fieldSymmetricMultiplicationPullbackOfCube cube K A.toGrp inferInstance
        inferInstance inferInstance N hNsym k hkpos)
  have hdK : (((k * k) ^ g : ℕ) : K) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ (mul_ne_zero hkK hkK)
  -- `Hⁱ(A, L)` is a retract of `Hⁱ(A, ψ_k^* L) = 0`.
  obtain ⟨ρ⟩ := finiteFlatCohomologyRetract K A.X A.X ψ hfin inferInstance inferInstance _
    hdK hrank L.obj inferInstance i
  rw [IsZero.iff_id_eq_zero, ← ρ.retract, hup.eq_of_src ρ.r 0, comp_zero]

end Langlands.AbelianScheme
