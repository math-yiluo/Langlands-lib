import Langlands.Global.AdelicCompactProfileProjection
import Langlands.Representation.Unitary.IntegratedOperator
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Compact profiles of adelic Hilbert vectors -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Analysis

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : AdelicGroupPoints F G →* (H →L[ℂ] H))
  (K : Subgroup (InfiniteAdelicGroupPoints F G))

local notation "A" => AdelicGroupPoints F G
local notation "j" => (MonoidHom.comp (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) (Subgroup.subtype K))

/-- The compact profile of a Hilbert vector tested against a continuous linear form. -/
def hilbertCompactProfile (ℓ : H →L[ℂ] ℂ) : H →ₗ[ℂ] (K → ℂ) where
  toFun v k := ℓ (π (j k) v)
  map_add' v w := by funext k; simp
  map_smul' c v := by funext k; simp

/-- The vectors whose compact profiles all lie in the specified space. -/
def hilbertCompactProfileSubspace (E : Submodule ℂ (K → ℂ)) : Submodule ℂ H :=
  ⨅ ℓ : H →L[ℂ] ℂ, E.comap (hilbertCompactProfile π K ℓ)

theorem mem_hilbertCompactProfileSubspace (E : Submodule ℂ (K → ℂ)) (v : H) :
    v ∈ hilbertCompactProfileSubspace π K E ↔ ∀ ℓ : H →L[ℂ] ℂ, hilbertCompactProfile π K ℓ v ∈ E :=
  Submodule.mem_iInf _

theorem isClosed_hilbertCompactProfileSubspace (E : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ E] :
    IsClosed (hilbertCompactProfileSubspace π K E : Set H) := by
  rw [hilbertCompactProfileSubspace, Submodule.coe_iInf]
  change IsClosed (⋂ ℓ : H →L[ℂ] ℂ, (hilbertCompactProfile π K ℓ) ⁻¹' (E : Set (K → ℂ)))
  apply isClosed_iInter
  intro ℓ
  exact E.closed_of_finiteDimensional.preimage (continuous_pi fun k => ℓ.continuous.comp (π (j k)).continuous)

/-- The profile space of a single compact-finite vector can be chosen finite-dimensional,
continuous, and invariant under left translation by the compact subgroup. -/
theorem exists_hilbertCompactProfiles (hvcont : ∀ v : H, Continuous fun g : A => π g v)
    (w : H) (hw : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => π (j k) w))) :
    ∃ E : Submodule ℂ (K → ℂ), FiniteDimensional ℂ E ∧
      (∀ v : E, Continuous v.val) ∧
      (∀ (s : K) (v : E), (fun k => v.val (s⁻¹ * k)) ∈ E) ∧
      w ∈ hilbertCompactProfileSubspace π K E := by
  let W := Submodule.span ℂ (Set.range fun k : K => π (j k) w)
  let : FiniteDimensional ℂ W := hw
  let u (k : K) : W := ⟨π (j k) w, Submodule.subset_span ⟨k, rfl⟩⟩
  let L : Module.Dual ℂ W →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun ℓ k => ℓ (u k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let E := LinearMap.range L
  have hu : Continuous u := ((hvcont w).comp ((ofInfinite F G).continuous.comp continuous_subtype_val)).subtype_mk _
  have hW (s : K) (v : W) : π (j s) v ∈ W := by
    refine Submodule.span_induction (p := fun v _ => π (j s) v ∈ W) ?_
      (by simp) (fun v v' _ _ hv hv' => by simpa only [map_add] using W.add_mem hv hv')
      (fun c v _ hv => by simpa only [map_smul] using W.smul_mem c hv) v.property
    rintro _ ⟨k, rfl⟩
    rw [← mul_apply_eq_comp, ← map_mul, ← map_mul]
    exact Submodule.subset_span ⟨s * k, rfl⟩
  refine ⟨E, inferInstance, ?_, ?_, (mem_hilbertCompactProfileSubspace π K E w).mpr ?_⟩
  · rintro ⟨_, ⟨ℓ, rfl⟩⟩
    exact ℓ.toContinuousLinearMap.continuous.comp hu
  · rintro s ⟨_, ⟨ℓ, rfl⟩⟩
    let R := ((π (j s⁻¹)).toLinearMap.comp W.subtype).codRestrict W (hW s⁻¹)
    refine ⟨ℓ.comp R, ?_⟩
    funext k
    change ℓ ⟨π (j s⁻¹) (π (j k) w), _⟩ = ℓ (u (s⁻¹ * k))
    congr 1
    apply Subtype.ext
    change π (j s⁻¹) (π (j k) w) = π (j (s⁻¹ * k)) w
    rw [← mul_apply_eq_comp, ← map_mul, ← map_mul]
  · intro ℓ
    exact ⟨ℓ.toLinearMap.comp W.subtype, rfl⟩

variable [LocallyOfFiniteType G.X.hom] [CompleteSpace H] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]

include ν in
/-- Weighted compact averages fix the prescribed profile space and send every vector into it. -/
theorem exists_hilbertCompactProfileProjection (hvcont : ∀ v : H, Continuous fun g : A => π g v)
    (E : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ E]
    (hE : ∀ v : E, Continuous v.val)
    (hleft : ∀ (s : K) (v : E), (fun k => v.val (s⁻¹ * k)) ∈ E) :
    ∃ a : C(K, ℂ),
      (∀ v : H, (∫ k, a k • π (j k) v ∂ν) ∈ hilbertCompactProfileSubspace π K E) ∧
      ∀ v ∈ hilbertCompactProfileSubspace π K E, (∫ k, a k • π (j k) v ∂ν) = v := by
  obtain ⟨a, _, _, _, ha, _, haout⟩ := exists_reproducing_adelicCompactProfileWeights K ν E hE hleft
  have hint (v : H) : Integrable (fun k => a k • π (j k) v) ν :=
    (a.continuous.smul ((hvcont v).comp ((ofInfinite F G).continuous.comp continuous_subtype_val)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨a, fun v => (mem_hilbertCompactProfileSubspace π K E _).2 (fun ℓ => ?_), fun v hv => ?_⟩
  · let f : C(A, ℂ) := ⟨fun x => ℓ (π x v), ℓ.continuous.comp (hvcont v)⟩
    convert haout f 1 using 1
    funext s
    simp only [one_mul]
    change ℓ (π (j s) (∫ k, a k • π (j k) v ∂ν)) = ∫ k, a k * f (j s * j k) ∂ν
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.integral_comp_comm _ (hint v)]
    congr 1
    funext k
    simp only [ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
    change a k * ℓ (π (j s) (π (j k) v)) = a k * ℓ (π (j s * j k) v)
    rw [map_mul, mul_apply_eq_comp]
  · have hprof (ℓ : H →L[ℂ] ℂ) : HasAdelicCompactProfiles K E (fun x => ℓ (π x v)) := by
      intro x
      convert (mem_hilbertCompactProfileSubspace π K E v).mp hv (ℓ.comp (π x)) using 1
      funext k
      change ℓ (π (x * j k) v) = ℓ (π x (π (j k) v))
      rw [map_mul, mul_apply_eq_comp]
    let ℓ := innerSL ℂ ((∫ k, a k • π (j k) v ∂ν) - v)
    have heq := ha (fun x => ℓ (π x v)) (hprof ℓ) 1
    simp only [one_mul, map_one, one_apply_eq_self] at heq
    have he : ℓ (∫ k, a k • π (j k) v ∂ν) = ℓ v := by
      rw [← ℓ.integral_comp_comm (hint v)]
      simpa only [Function.comp_apply, map_smul, smul_eq_mul] using heq
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (show ℓ ((∫ k, a k • π (j k) v ∂ν) - v) = 0 by rw [map_sub, he, sub_self]))

end Langlands.Global
