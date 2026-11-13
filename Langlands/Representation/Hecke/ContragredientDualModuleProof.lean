import Langlands.Representation.Hecke.ContragredientDualModuleStatement
import Langlands.Representation.Hecke.CompactTensorGroupBalance

/-! # The smooth contragredient is the nondegenerate Hecke dual -/

noncomputable section

namespace Langlands.Hecke

open HarmonicAnalysis MeasureTheory MulOpposite

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The transpose formula for arbitrary left Haar measure. -/
theorem heckeAction_smoothDualPairing_haar (f : HeckeAlgebra μ)
    (ℓ : SmoothDual ρ) (v : V) :
    smoothDualPairing ρ
      (heckeAction μ (smoothContragredient ρ)
        (isSmooth_smoothContragredient ρ) f ℓ) v =
      smoothDualPairing ρ ℓ (heckeAction μ ρ hρ (haarInversion μ f) v) := by
  let ev : SmoothDual ρ →ₗ[ℂ] ℂ :=
    (Module.Dual.eval ℂ V v).comp (smoothDualPairing ρ)
  change ev (integratedAction μ (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) (HeckeAlgebra.toTestFunction μ f) ℓ) = _
  rw [integratedAction_dual]
  change (∫ g, f g * smoothDualPairing ρ ℓ (ρ g⁻¹ v) ∂μ) =
    smoothDualPairing ρ ℓ (integratedAction μ ρ hρ
      (HeckeAlgebra.toTestFunction μ (haarInversion μ f)) v)
  rw [integratedAction_dual]
  let b : SchwartzBruhat G :=
    ⟨fun g => f g⁻¹ * smoothDualPairing ρ ℓ (ρ g v),
      (f.locallyConstant.comp_continuous continuous_inv).mul
        ((orbitMap_locallyConstant ρ (hρ v)).comp (smoothDualPairing ρ ℓ)),
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mul_right⟩
  calc
    _ = ∫ g, b g⁻¹ ∂μ := by simp only [b, inv_inv]
    _ = ∫ g, b g * haarScale g ∂μ := integral_inv_test μ b
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with g
      change (f g⁻¹ * smoothDualPairing ρ ℓ (ρ g v)) * haarScale g =
        (haarScale g * f g⁻¹) * smoothDualPairing ρ ℓ (ρ g v)
      ring

/-- A right-invariant test operator absorbs the subgroup action on its input. -/
theorem heckeAction_group_of_rightInvariant
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : HeckeAlgebra μ)
    (hf : ∀ k : K, ∀ x, f (x * k) = f x) (k : K) (v : V) :
    heckeAction μ ρ hρ f (ρ k v) = heckeAction μ ρ hρ f v := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero]
  change L (integratedAction μ ρ hρ (HeckeAlgebra.toTestFunction μ f) (ρ k v)) =
    L (integratedAction μ ρ hρ (HeckeAlgebra.toTestFunction μ f) v)
  rw [integratedAction_dual, integratedAction_dual]
  let b : SchwartzBruhat G :=
    ⟨fun x => f x * L (ρ x v),
      f.locallyConstant.mul ((orbitMap_locallyConstant ρ (hρ v)).comp L),
      f.hasCompactSupport.mul_right⟩
  calc
    _ = ∫ x, b (x * k) ∂μ := by
      congr 1
      funext x
      simp only [b, hf k x, map_mul, Module.End.mul_apply]
      rfl
    _ = haarScale (k : G) * ∫ x, b x ∂μ := integral_mul_right_test μ b k
    _ = _ := by
      have hk : haarScale (k : G) = 1 := by
        simp [haarScale, Haar.modularCharacter_eq_one_of_mem_compactOpen K hK k.property]
      rw [hk, one_mul]
      rfl

open Langlands.Algebra

/-- Recovering complex scalars from the Hecke action does not change the
underlying full dual functionals. -/
def heckeFullDualEquiv :
    letI := heckeNonUnitalModule μ ρ hρ
    Module.Dual ℂ V ≃+
      NonUnitalModuleDual.FullDual (Homomorphism.isIdempotented μ)
        (heckeNonUnitalModule_isNondegenerate μ ρ hρ) := by
  letI := heckeNonUnitalModule μ ρ hρ
  letI : IsScalarTower ℂ (HeckeAlgebra μ) V :=
    NonUnitalModule.ofLinearEndHom_isScalarTower (heckeAction μ ρ hρ)
  let hA := Homomorphism.isIdempotented μ
  let hM := heckeNonUnitalModule_isNondegenerate μ ρ hρ
  have hc (c : ℂ) (v : V) :
      @SMul.smul ℂ V (NondegenerateScalars.complexModule hA hM).toSMul c v = c • v :=
    NondegenerateScalars.scalarMul_eq_of_compatible ℂ hM c v
  let originalModule : Module ℂ V := inferInstance
  let forward : Module.Dual ℂ V → NonUnitalModuleDual.FullDual hA hM := fun φ => by
    letI := NondegenerateScalars.complexModule hA hM
    exact
      { toFun := φ
        map_add' v w := by
          let _ := originalModule
          exact φ.map_add v w
        map_smul' c v := by
          change φ (@SMul.smul ℂ V
            (NondegenerateScalars.complexModule hA hM).toSMul c v) = c • φ v
          rw [hc]
          let _ := originalModule
          exact φ.map_smul c v }
  let backward : NonUnitalModuleDual.FullDual hA hM → Module.Dual ℂ V := fun φ =>
    { toFun := φ
      map_add' v w := by
        let _ := NondegenerateScalars.complexModule hA hM
        exact φ.map_add v w
      map_smul' c v := by
        change φ (c • v) = c • φ v
        rw [← hc]
        let _ := NondegenerateScalars.complexModule hA hM
        exact φ.map_smul c v }
  exact
    { toFun := forward
      invFun := backward
      left_inv := fun φ => LinearMap.ext (fun _ => rfl)
      right_inv := fun φ => NonUnitalModuleDual.fullDual_ext hA hM (fun _ => rfl)
      map_add' := fun φ ψ => NonUnitalModuleDual.fullDual_ext hA hM (fun _ => rfl) }

@[simp] theorem heckeFullDualEquiv_apply (φ : Module.Dual ℂ V) (v : V) :
    heckeFullDualEquiv μ ρ hρ φ v = φ v := rfl

@[simp] theorem heckeFullDualEquiv_symm_apply
    (φ : letI := heckeNonUnitalModule μ ρ hρ
      NonUnitalModuleDual.FullDual (Homomorphism.isIdempotented μ)
        (heckeNonUnitalModule_isNondegenerate μ ρ hρ)) (v : V) :
    (heckeFullDualEquiv μ ρ hρ).symm φ v = φ v := rfl

/-- The nondegenerate part of the full Hecke dual consists exactly of the
smooth functionals for the original dual group action. -/
theorem heckeFullDualEquiv_mem_iff (φ : Module.Dual ℂ V) :
    letI := heckeNonUnitalModule μ ρ hρ
    let hA := Homomorphism.isIdempotented μ
    let hM := heckeNonUnitalModule_isNondegenerate μ ρ hρ
    letI := NonUnitalModuleDual.fullAction hA hM
    heckeFullDualEquiv μ ρ hρ φ ∈
      nondegeneratePart hA.op (NonUnitalModuleDual.FullDual hA hM) ↔
        φ ∈ smoothVectors ρ.dual := by
  classical
  let _ := heckeNonUnitalModule μ ρ hρ
  let hA := Homomorphism.isIdempotented μ
  let hM := heckeNonUnitalModule_isNondegenerate μ ρ hρ
  let _ := NonUnitalModuleDual.fullAction hA hM
  constructor
  · intro hφ
    obtain ⟨e, he⟩ := (NonUnitalModuleDual.mem_dual_iff hA hM _).mp hφ
    change ∀ v, φ (heckeAction μ ρ hρ e.val v) = φ v at he
    obtain ⟨K, _, hK, hKe⟩ := TestFunction.commonCompactOpenBiInvariance G
      {HeckeAlgebra.toTestFunction μ e.val} ⊤
    have hr (k : K) (x : G) : e.val (x * k) = e.val x :=
      (hKe _ (Finset.mem_singleton_self _)).2 k x
    refine ⟨K, ?_⟩
    intro k
    apply LinearMap.ext
    intro v
    change φ (ρ (k : G)⁻¹ v) = φ v
    calc
      _ = φ (heckeAction μ ρ hρ e.val (ρ (k : G)⁻¹ v)) := (he _).symm
      _ = φ (heckeAction μ ρ hρ e.val v) :=
        congrArg φ (heckeAction_group_of_rightInvariant μ ρ hρ K hK e.val hr k⁻¹ v)
      _ = _ := he v
  · intro hφ
    let ℓ : SmoothDual ρ := ⟨φ, hφ⟩
    obtain ⟨K, hK, hℓ⟩ := exists_normalizedIndicator_fixes μ
      (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) ℓ
    apply (NonUnitalModuleDual.mem_dual_iff hA hM _).mpr
    refine ⟨⟨HeckeAlgebra.normalizedIndicator μ K hK,
      HeckeAlgebra.normalizedIndicator_idempotent μ K hK⟩, ?_⟩
    intro v
    change φ (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v) = φ v
    have hp := heckeAction_smoothDualPairing_haar μ ρ hρ
      (HeckeAlgebra.normalizedIndicator μ K hK) ℓ v
    rw [haarInversion_normalizedIndicator, hℓ] at hp
    exact hp.symm

/-- Restrict the full-dual comparison to smooth functionals and the actual
nondegenerate Hecke dual. -/
def smoothHeckeDualEquiv :
    letI := heckeNonUnitalModule μ ρ hρ
    SmoothDual ρ ≃+
      NonUnitalModuleDual.Dual (Homomorphism.isIdempotented μ)
        (heckeNonUnitalModule_isNondegenerate μ ρ hρ) := by
  letI := heckeNonUnitalModule μ ρ hρ
  let hA := Homomorphism.isIdempotented μ
  let hM := heckeNonUnitalModule_isNondegenerate μ ρ hρ
  letI := NonUnitalModuleDual.fullAction hA hM
  let E := heckeFullDualEquiv μ ρ hρ
  exact
    { toFun := fun ℓ => ⟨E ℓ.val, (heckeFullDualEquiv_mem_iff μ ρ hρ ℓ.val).mpr ℓ.property⟩
      invFun := fun φ => ⟨E.symm φ.val, (heckeFullDualEquiv_mem_iff μ ρ hρ _).mp
        (by
          change E (E.symm φ.val) ∈ _
          rw [E.apply_symm_apply]
          exact φ.property)⟩
      left_inv := fun ℓ => Subtype.ext (E.left_inv ℓ.val)
      right_inv := fun φ => Subtype.ext (E.right_inv φ.val)
      map_add' := fun ℓ ψ => Subtype.ext (E.map_add ℓ.val ψ.val) }

@[simp] theorem smoothHeckeDualEquiv_apply (ℓ : SmoothDual ρ) (v : V) :
    (smoothHeckeDualEquiv μ ρ hρ ℓ).val v = smoothDualPairing ρ ℓ v := rfl

/-- Renard III.1.6: the smooth contragredient is the I.4.1 dual Hecke module,
with arbitrary left Haar measure and independent group and carrier universes. -/
theorem contragredientHeckeDual : ContragredientHeckeDualStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ μ _ A
  let e := smoothHeckeDualEquiv μ A.representation A.isSmooth
  refine ⟨e, ?_, ?_⟩
  · intro ℓ v
    rfl
  · intro T ℓ
    apply Subtype.ext
    apply NonUnitalModuleDual.fullDual_ext (Homomorphism.isIdempotented μ)
      (heckeNondegenerateModule μ A).property
    intro v
    change smoothDualPairing A.representation
      (heckeAction μ (smoothContragredient A.representation)
        (isSmooth_smoothContragredient A.representation) T ℓ) v =
      smoothDualPairing A.representation ℓ
        (heckeAction μ A.representation A.isSmooth (haarInversion μ T) v)
    exact heckeAction_smoothDualPairing_haar μ A.representation A.isSmooth T ℓ v

end Langlands.Hecke
