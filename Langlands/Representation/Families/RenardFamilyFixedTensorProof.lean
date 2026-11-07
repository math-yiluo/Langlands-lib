import Langlands.Representation.Families.RenardFamilyStatements
import Langlands.Representation.Compact.CharZeroAverage

/-! # Coefficient-linear averaging and Renard's fixed-tensor comparison -/

noncomputable section

open TensorProduct

namespace Langlands.Renard.AlgebraicFamily

universe uB uG uV uW uE

section Averaging

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module B V]
  {W : Type uW} [AddCommGroup W] [Module B W]

private def complexAction [Module ℂ V] [IsScalarTower ℂ B V]
    (ρ : Representation B G V) : Representation ℂ G V where
  toFun g := (ρ g).restrictScalars ℂ
  map_one' := by ext v; change ρ 1 v = v; simp
  map_mul' g h := by
    ext v
    change ρ (g * h) v = ρ g (ρ h v)
    simp only [map_mul, Module.End.mul_apply]

/-- Compact averaging on the original coefficient module. -/
def coefficientAverage (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : V →ₗ[B] V := by
  letI := Module.restrictScalars ℂ B V
  letI := IsScalarTower.restrictScalars ℂ B V
  let σ := complexAction ρ
  have hσ : IsSmooth σ := hρ
  let p := Compact.CharZero.averageMap σ hσ K hK
  refine { toFun := p, map_add' := p.map_add, map_smul' := ?_ }
  intro b v
  let f : V →ₗ[ℂ] V :=
    { toFun := fun w => b • w
      map_add' := smul_add b
      map_smul' := fun c w => smul_comm b c w }
  let := Compact.CharZero.finite_orbit_of_smooth σ hσ K hK v
  let := Compact.CharZero.finite_orbit_of_smooth σ hσ K hK (b • v)
  exact (Compact.CharZero.orbitMean_map (σ.comp K.toSubgroup.subtype)
    (σ.comp K.toSubgroup.subtype) f
    (fun g w => ((ρ g.val).map_smul b w).symm) v).symm

/-- Averaging lies in the compact-open fixed submodule. -/
theorem coefficientAverage_mem (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V) :
    coefficientAverage ρ hρ K hK v ∈ fixedVectors ρ K.toSubgroup := by
  let := Module.restrictScalars ℂ B V
  let := IsScalarTower.restrictScalars ℂ B V
  exact Compact.CharZero.averageMap_mem_fixedVectors (complexAction ρ) hρ K hK v

/-- Averaging fixes the compact-open fixed submodule pointwise. -/
theorem coefficientAverage_fixed (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : V) (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    coefficientAverage ρ hρ K hK v = v := by
  let := Module.restrictScalars ℂ B V
  let := IsScalarTower.restrictScalars ℂ B V
  exact Compact.CharZero.averageMap_id (complexAction ρ) hρ K hK v hv

/-- Naturality under coefficient-linear intertwiners. -/
theorem coefficientAverage_natural (ρ : Representation B G V) (σ : Representation B G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : V →ₗ[B] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (v : V) :
    f (coefficientAverage ρ hρ K hK v) = coefficientAverage σ hσ K hK (f v) := by
  let := Module.restrictScalars ℂ B V
  let := Module.restrictScalars ℂ B W
  let := IsScalarTower.restrictScalars ℂ B V
  let := IsScalarTower.restrictScalars ℂ B W
  let := Compact.CharZero.finite_orbit_of_smooth (complexAction ρ) hρ K hK v
  let := Compact.CharZero.finite_orbit_of_smooth (complexAction σ) hσ K hK (f v)
  exact Compact.CharZero.orbitMean_map ((complexAction ρ).comp K.toSubgroup.subtype)
    ((complexAction σ).comp K.toSubgroup.subtype) (f.restrictScalars ℂ)
    (fun g w => hf g.val w) v
    (targetFinite := Compact.CharZero.finite_orbit_of_smooth
      (complexAction σ) hσ K hK (f v))

/-- The fixed vectors are a coefficient-linear retract. -/
def coefficientFixedProjection (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    V →ₗ[B] fixedVectors ρ K.toSubgroup :=
  (coefficientAverage ρ hρ K hK).codRestrict _ (coefficientAverage_mem ρ hρ K hK)

@[simp]
theorem coefficientFixedProjection_fixed (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : fixedVectors ρ K.toSubgroup) :
    coefficientFixedProjection ρ hρ K hK v.val = v := by
  apply Subtype.ext
  exact coefficientAverage_fixed ρ hρ K hK v.val v.property

@[simp]
theorem coefficientFixedProjection_comp (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    (coefficientFixedProjection ρ hρ K hK).comp
      (fixedVectors ρ K.toSubgroup).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact coefficientFixedProjection_fixed ρ hρ K hK v

end Averaging

section Tensor

variable {B : Type uB} [CommRing B]
  {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module B V]
  {E : Type uE} [AddCommGroup E] [Module B E]

/-- Tensoring with a trivial module preserves smoothness. -/
theorem trivialTensor_isSmooth (ρ : Representation B G V) (hρ : IsSmooth ρ) :
    IsSmooth ((Representation.trivial B G E).tprod ρ) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul e v =>
    obtain ⟨K, hv⟩ := hρ v
    refine ⟨K, fun g => ?_⟩
    change e ⊗ₜ[B] ρ g.val v = e ⊗ₜ[B] v
    exact congrArg (fun w : V => e ⊗ₜ[B] w) (hv g)
  | add t s ht hs =>
    obtain ⟨K, ht⟩ := ht
    obtain ⟨L, hs⟩ := hs
    refine ⟨K ⊓ L, fun g => ?_⟩
    change ((Representation.trivial B G E).tprod ρ) g.val (t + s) = t + s
    exact (map_add _ _ _).trans
      (congrArg₂ (· + ·) (ht ⟨g.val, g.property.1⟩) (hs ⟨g.val, g.property.2⟩))

end Tensor

section TensorComparison

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module B V]
  {E : Type uE} [AddCommGroup E] [Module B E]

/-- Averaging acts only on the nontrivial tensor factor. -/
theorem coefficientAverage_tensor (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : E ⊗[B] V) :
    (coefficientAverage ρ hρ K hK).lTensor E t =
      coefficientAverage ((Representation.trivial B G E).tprod ρ)
        (trivialTensor_isSmooth ρ hρ) K hK t := by
  induction t using TensorProduct.inductionOn with
  | tmul e v =>
    exact coefficientAverage_natural ρ ((Representation.trivial B G E).tprod ρ)
      hρ (trivialTensor_isSmooth ρ hρ) K hK (TensorProduct.mk B E V e)
      (fun _ _ => rfl) v
  | add t s ht hs => simp only [map_add, ht, hs]

/-- The natural tensor map is injective and has exactly the fixed-vector range. -/
theorem fixedTensorComparison_of_smooth (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Function.Injective ((fixedVectors ρ K.toSubgroup).subtype.lTensor E) ∧
      LinearMap.range ((fixedVectors ρ K.toSubgroup).subtype.lTensor E) =
        fixedVectors ((Representation.trivial B G E).tprod ρ) K.toSubgroup := by
  let N := fixedVectors ρ K.toSubgroup
  let p := coefficientFixedProjection ρ hρ K hK
  have hleft : (p.lTensor E).comp (N.subtype.lTensor E) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, coefficientFixedProjection_comp, LinearMap.lTensor_id]
  refine ⟨Function.LeftInverse.injective (fun t => LinearMap.congr_fun hleft t), ?_⟩
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩ g
    induction t using TensorProduct.inductionOn with
    | tmul e v =>
      change e ⊗ₜ[B] ρ g.val v.val = e ⊗ₜ[B] v.val
      exact congrArg (fun w : V => e ⊗ₜ[B] w) (v.property g)
    | add t s ht hs => simp only [map_add, ht, hs]
  · intro t ht
    refine ⟨p.lTensor E t, ?_⟩
    have hcomp : N.subtype.comp p = coefficientAverage ρ hρ K hK := rfl
    change ((N.subtype.lTensor E).comp (p.lTensor E)) t = t
    rw [← LinearMap.lTensor_comp, hcomp, coefficientAverage_tensor]
    exact coefficientAverage_fixed _ (trivialTensor_isSmooth ρ hρ) K hK t ht

/-- Renard VI.8.1, the fixed-tensor comparison at all four published universes. -/
theorem fixedTensorComparison : FixedTensorComparisonStatement.{uB, uG, uV, uE} := by
  intro B _ _ _ _ _ G _ _ _ _ V _ _ ρ hρ K hK E _ _
  exact fixedTensorComparison_of_smooth ρ hρ K hK

end TensorComparison

end Langlands.Renard.AlgebraicFamily
