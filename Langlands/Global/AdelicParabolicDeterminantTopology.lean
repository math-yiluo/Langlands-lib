import Langlands.Global.AdelicParabolicInductionTopology
import Langlands.Global.AdelicParabolicDeterminantTwist

/-! # Continuous determinant multiplication on actual adelic induced sections -/

noncomputable section

universe uF uV uW

namespace Langlands.Global.AdelicParabolicInduction.CompactOpenSections

open NumberField Langlands.GeneralLinear AdelicBlockParabolic
open Filter Topology
open scoped Topology

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The algebraic determinant multiplier on the dedicated compact-open copies. -/
def determinantEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) :
    CompactOpenSections F B σ ≃ₗ[ℂ]
      CompactOpenSections F B (determinantTwist F B χ σ) :=
  (toSmooth F B σ).trans ((smoothDeterminantEquiv F B χ hχ σ).trans
    (toSmooth F B (determinantTwist F B χ σ)).symm)

@[simp]
theorem toContinuousMap_determinantEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) (f : CompactOpenSections F B σ)
    (x : AdelicGL F n) :
    toContinuousMap F B (determinantTwist F B χ σ) (determinantEquiv F B χ hχ σ f) x =
      (χ.adelicDeterminant n x : ℂ) • toContinuousMap F B σ f x := rfl

@[simp]
theorem toContinuousMap_determinantEquiv_symm (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : CompactOpenSections F B (determinantTwist F B χ σ)) (x : AdelicGL F n) :
    toContinuousMap F B σ ((determinantEquiv F B χ hχ σ).symm f) x =
      ((χ.adelicDeterminant n x)⁻¹ : ℂˣ) •
        toContinuousMap F B (determinantTwist F B χ σ) f x := rfl

private theorem continuous_fixedScalarMultiplier {Y : Type*} [TopologicalSpace Y]
    (m : C(Y, ℂ)) : Continuous (fun f : C(Y, V) => m • f) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply (ContinuousMap.tendsto_compactOpen_iff_forall _ _).mpr
  intro K hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h : Continuous (fun g : C(K, V) => m.restrict K • g) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((m.restrict K).continuous.comp continuous_snd).smul
      continuous_eval
  exact (h.comp (ContinuousMap.continuous_restrict K)).continuousAt

/-- Actual multiplication is continuous in the compact-open section topology. -/
theorem continuous_determinantEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) :
    Continuous (determinantEquiv F B χ hχ σ) := by
  apply continuous_induced_rng.mpr
  let m : C(AdelicGL F n, ℂ) :=
    ⟨fun x => (χ.adelicDeterminant n x : ℂ),
      Units.continuous_val.comp (χ.adelicDeterminant n).continuous⟩
  exact (continuous_fixedScalarMultiplier m).comp
    (isEmbedding_toContinuousMap F B σ).continuous

/-- Inverse determinant multiplication is continuous in the same topology. -/
theorem continuous_determinantEquiv_symm (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V) :
    Continuous (determinantEquiv F B χ hχ σ).symm := by
  apply continuous_induced_rng.mpr
  let m : C(AdelicGL F n, ℂ) :=
    ⟨fun x => (χ⁻¹.adelicDeterminant n x : ℂ),
      Units.continuous_val.comp (χ⁻¹.adelicDeterminant n).continuous⟩
  exact (continuous_fixedScalarMultiplier m).comp
    (isEmbedding_toContinuousMap F B (determinantTwist F B χ σ)).continuous

/-- Actual determinant multiplication is a continuous complex linear equivalence. -/
def determinantMultiplier (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) :
    CompactOpenSections F B σ ≃L[ℂ]
      CompactOpenSections F B (determinantTwist F B χ σ) where
  toLinearEquiv := determinantEquiv F B χ hχ σ
  continuous_toFun := continuous_determinantEquiv F B χ hχ σ
  continuous_invFun := continuous_determinantEquiv_symm F B χ hχ σ

@[simp]
theorem toContinuousMap_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : CompactOpenSections F B σ) (x : AdelicGL F n) :
    toContinuousMap F B (determinantTwist F B χ σ)
      (determinantMultiplier F B χ hχ σ f) x =
        (χ.adelicDeterminant n x : ℂ) • toContinuousMap F B σ f x := rfl

@[simp]
theorem toContinuousMap_determinantMultiplier_symm (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : CompactOpenSections F B (determinantTwist F B χ σ)) (x : AdelicGL F n) :
    toContinuousMap F B σ ((determinantMultiplier F B χ hχ σ).symm f) x =
      ((χ.adelicDeterminant n x)⁻¹ : ℂˣ) •
        toContinuousMap F B (determinantTwist F B χ σ) f x := rfl

/-- The continuous multiplier also gives the actual ambient-to-Levi twist equivalence. -/
def determinantTwistEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) :
    (twist (χ.adelicDeterminant n).toMonoidHom (rightAction F B σ)).Equiv
      (rightAction F B (determinantTwist F B χ σ)) where
  toLinearEquiv := (determinantMultiplier F B χ hχ σ).toLinearEquiv
  isIntertwining' := (smoothDeterminantTwistEquiv F B χ hχ σ).isIntertwining'

/-- Right translation has precisely the ambient determinant scalar. -/
theorem determinantMultiplier_rightAction (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) (g : AdelicGL F n)
    (f : CompactOpenSections F B σ) :
    rightAction F B (determinantTwist F B χ σ) g
        (determinantMultiplier F B χ hχ σ f) =
      (χ.adelicDeterminant n g : ℂ) •
        determinantMultiplier F B χ hχ σ (rightAction F B σ g f) := by
  exact ((determinantTwistEquiv F B χ hχ σ).toIntertwiningMap.isIntertwining
    (twist (χ.adelicDeterminant n).toMonoidHom (rightAction F B σ))
    (rightAction F B (determinantTwist F B χ σ)) g f).symm.trans
      ((determinantMultiplier F B χ hχ σ).map_smul _ _)

/-- Continuous coefficient postcomposition commutes with the actual multiplier. -/
theorem determinantMultiplier_mapCLM (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    {σ : Representation ℂ (FullLevi F B) V} {τ : Representation ℂ (FullLevi F B) W}
    (T : σ.IntertwiningMap τ) (hT : Continuous T) (f : CompactOpenSections F B σ) :
    determinantMultiplier F B χ hχ τ (mapCLM F B T hT f) =
      mapCLM F B
        (twistIntertwining
          (AdelicBlockHeckeCharacter.leviCharacter F B (fun _ => χ)).toMonoidHom T)
        hT (determinantMultiplier F B χ hχ σ f) := by
  apply toContinuousMap_injective F B (determinantTwist F B χ τ)
  ext x
  change (χ.adelicDeterminant n x : ℂ) • T (toContinuousMap F B σ f x) =
    T ((χ.adelicDeterminant n x : ℂ) • toContinuousMap F B σ f x)
  exact (map_smul T _ _).symm

end Langlands.Global.AdelicParabolicInduction.CompactOpenSections
