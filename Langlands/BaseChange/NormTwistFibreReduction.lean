import Langlands.BaseChange.CuspidalSigmaLiftExistenceStatement
import Langlands.BaseChange.SigmaOrbitPeriod
import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhood
import Langlands.Representation.Classification.SupercuspidalTwist

/-! # Supercuspidality from a common sigma-lift and a norm twist -/

noncomputable section

universe uK uL uV uV' uW

set_option autoImplicit false

namespace Langlands.BaseChange

section NormTwists

variable {K : Type uK} {L : Type uL} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
  [Field L] [Algebra K L] [FiniteDimensional K L] {κ : Kˣ →* ℂˣ}

/-- A character trivial on the finite extension norms has open kernel. -/
theorem IsNormTrivial.isOpen_ker (hκ : IsNormTrivial L κ) : IsOpen (κ.ker : Set Kˣ) := by
  apply κ.ker.isOpen_of_mem_nhds
  refine Filter.mem_of_superset
    (Global.AdelicFunctoriality.range_pow_mem_nhds_one
      (Module.finrank_pos (R := K) (M := L)).ne') ?_
  rintro _ ⟨u, rfl⟩
  have hn : Units.map (Algebra.norm K : L →* K)
      (Units.map (algebraMap K L).toMonoidHom u) = u ^ Module.finrank K L := by
    apply Units.ext
    exact Algebra.norm_algebraMap (u : K)
  change κ (u ^ Module.finrank K L) = 1
  rw [← hn]
  exact hκ _

/-- The original norm-trivial character, equipped with its open kernel. -/
def IsNormTrivial.toSmoothCharacter (hκ : IsNormTrivial L κ) :
    Induction.SmoothCharacter ℂ Kˣ :=
  ⟨κ, hκ.isOpen_ker⟩

/-- The determinant twist by a norm-trivial character preserves the actual
Jacquet-vanishing definition of supercuspidality. -/
theorem IsNormTrivial.isSupercuspidal_twist_iff (hκ : IsNormTrivial L κ)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n K) V) :
    GeneralLinear.IsSupercuspidal (twist (κ.comp GeneralLinear.determinant) π) ↔
      GeneralLinear.IsSupercuspidal π := by
  apply GeneralLinear.isSupercuspidal_twist_iff
  · exact hκ.toSmoothCharacter.isOpen_ker.preimage Matrix.GeneralLinearGroup.continuous_det
  · intro g hg
    change κ (GeneralLinear.determinant g) = 1
    rw [MonoidHom.mem_ker.mp hg, map_one]

end NormTwists

section OrbitLift

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private local instance (n : ℕ) : T2Space (GeneralLinear n F) :=
  LocalFieldTopology.generalLinear_t2Space F n
private local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace F n
private local instance (n : ℕ) : TotallyDisconnectedSpace (GeneralLinear n F) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n

variable {K : Type uK} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  {L : Type uL} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [IsModuleTopology K L]

/-- Given cuspidal sigma-lift existence and a norm-twist comparison with
supercuspidal representations in the given fibre, a downstairs action with
the regular upstairs orbit as sigma-lift is supercuspidal. -/
theorem isSupercuspidal_of_sigmaOrbitLift_of_fibre
    (hExist : CuspidalSigmaLiftExistenceStatement.{uK, uL, uV', uW})
    (σ : L ≃ₐ[K] L) (d m : ℕ) (hcyc : IsCyclicAlgebra σ d) (hm : 0 < m)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear m L) W)
    (hτ : GeneralLinear.IsSupercuspidal τ) (hIrred : τ.IsIrreducible)
    (hstab : HasTrivialGaloisStabilizer K τ) :
    let P := sigmaOrbitProduct σ d hm τ
    ∀ (hP : IsAdmissible P) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (d * m) K) V) (hπ : IsAdmissible π)
      (A : SigmaIntertwiner σ (d * m) P) (c : ℂ),
      IsSigmaLift σ d π hπ P hP A c →
      (∀ (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
        (π' : Representation ℂ (GeneralLinear (d * m) K) V') (hπ' : IsAdmissible π')
        (A' : SigmaIntertwiner σ (d * m) P) (c' : ℂ),
        GeneralLinear.IsSupercuspidal π' → π'.IsIrreducible →
        IsSigmaLift σ d π hπ P hP A c → IsSigmaLift σ d π' hπ' P hP A' c' →
        ∃ κ : Kˣ →* ℂˣ, IsNormTrivial L κ ∧
          Nonempty (π.Equiv (twist (κ.comp GeneralLinear.determinant) π'))) →
      GeneralLinear.IsSupercuspidal π := by
  dsimp only
  intro hP V _ _ π hπ A c hLift hFibre
  have : FiniteDimensional K L := hcyc.1
  have hper (i : ℕ) :
      Nonempty (Representation.Equiv τ (τ.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔
        d ∣ i := by
    simpa only [hcyc.2.2.2.1] using
      conjugate_equiv_iff_orderOf_dvd K L σ m W τ hstab i
  obtain ⟨_, _, V', addV', modV', π', hπ', A', c', hsc', hIrred', _, hLift'⟩ :=
    hExist K L σ d hcyc d m hm W τ hτ hIrred hper
  let := addV'
  let := modV'
  obtain ⟨κ, hκ, ⟨e⟩⟩ := hFibre V' π' hπ' A' c' hsc' hIrred' hLift hLift'
  exact (GeneralLinear.isSupercuspidal_iff_of_equiv e).mpr
    ((hκ.isSupercuspidal_twist_iff π').mpr hsc')

end OrbitLift

end Langlands.BaseChange
