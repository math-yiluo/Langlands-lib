import Langlands.Global.AdelicCuspidalAnnihilator
import Langlands.Global.AdelicStandardConstantTermTwist

/-! # Iwasawa twisting and the tests on a nested parabolic -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

variable {K : Subgroup (AdelicGroupPoints F G)}

/-- Taking a nested constant term and testing it against the norm-one cuspidal annihilator
has the same zero condition before and after twisting. Only the outer parabolic needs the
Iwasawa coverage used to define the height. -/
theorem constantTerm_parameterTwist_mem_cuspidalAnnihilator_iff
    (J I : Idx) [IsClosedImmersion (𝓕.p J).hom.hom.left]
    (hK : IsIwasawaCompact (𝓕.p J) K) (hle : I ≤ J)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (lam : ComplexCharacterParameter F (𝓕.P J)) (f : AdelicGroupPoints F G → ℂ) :
    𝓕.InCuspidalAnnihilator Kinf rho I (𝓕.constantTerm I (hK.parameterTwist f lam)) ↔
      𝓕.InCuspidalAnnihilator Kinf rho I (𝓕.constantTerm I f) := by
  rw [𝓕.constantTerm_parameterTwist J I hK hle]
  let F₀ := 𝓕.constantTerm I f
  have hpair (ψ : AdelicGroupPoints F (𝓕.M I) → ℂ)
      (g : AdelicGroupPoints F G) :
      (Integrable (𝓕.leviPairingIntegrand I (hK.parameterTwist F₀ lam) g ψ)
          (normOneRationalQuotientHaarMeasure F (𝓕.M I)) ∧
        𝓕.leviPairing I (hK.parameterTwist F₀ lam) g ψ = 0) ↔
      (Integrable (𝓕.leviPairingIntegrand I F₀ g ψ)
          (normOneRationalQuotientHaarMeasure F (𝓕.M I)) ∧
        𝓕.leviPairing I F₀ g ψ = 0) := by
    unfold leviPairing
    have heq : 𝓕.leviPairingIntegrand I (hK.parameterTwist F₀ lam) g ψ =
        hK.heightPower lam g • 𝓕.leviPairingIntegrand I F₀ g ψ :=
      by
        rw [𝓕.leviPairingIntegrand_parameterTwist J I hK hle]
        funext q
        exact mul_comm _ _
    rw [heq]
    simp only [Pi.smul_apply, integral_smul]
    have hn : hK.heightPower lam g ≠ 0 := Complex.exp_ne_zero _
    constructor
    · rintro ⟨hI, hZ⟩
      refine ⟨?_, ?_⟩
      · simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
          hI.smul (hK.heightPower lam g)⁻¹
      · exact (smul_eq_zero.mp hZ).resolve_left hn
    · rintro ⟨hI, hZ⟩
      exact ⟨hI.smul _, by rw [hZ, smul_zero]⟩
  exact ⟨fun h ψ hψ g => (hpair ψ g).mp (h ψ hψ g),
    fun h ψ hψ g => (hpair ψ g).mpr (h ψ hψ g)⟩

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- A nested constant term satisfies the norm-one Levi annihilator tests exactly when its
Iwasawa-twisted version does. -/
def CuspidalAnnihilatorIwasawaTwistStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G)
    (J I : StandardIndex F G 𝓕.i 𝓕.ν) [IsClosedImmersion (𝓕.p J).hom.hom.left],
    I ≤ J →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (𝓕.p J) K)
      (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {N : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (lam : ComplexCharacterParameter F (𝓕.P J))
      (f : AdelicGroupPoints F G → ℂ),
      𝓕.InCuspidalAnnihilator Kinf rho I (𝓕.constantTerm I (hK.parameterTwist f lam)) ↔
        𝓕.InCuspidalAnnihilator Kinf rho I (𝓕.constantTerm I f)

theorem cuspidalAnnihilatorIwasawaTwist : CuspidalAnnihilatorIwasawaTwistStatement.{u} := by
  intro F _ _ G _ _ _ family J I _ hle K hK Kinf N rho lam f
  exact family.constantTerm_parameterTwist_mem_cuspidalAnnihilator_iff J I hK hle rho Kinf lam f

end Langlands.Global
