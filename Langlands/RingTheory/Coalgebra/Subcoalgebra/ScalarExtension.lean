import Langlands.RingTheory.Coalgebra.Subcoalgebra.Basic
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Images of coalgebra maps and scalar extension of subcoalgebras

Over a field `k`, the image of a homomorphism of coalgebras `f : C →ₗc[k] E` is a
subcoalgebra `range f` of `E`, and `f` factors through it by a surjective homomorphism
`rangeRestrict f`, which is an equivalence `equivRange f hf` when `f` is injective.

For a field extension `K` of `k` and a subcoalgebra `D` of `C`, the map
`baseChangeMap K D : K ⊗[k] D →ₗc[K] K ⊗[k] C` induced by the inclusion is injective. Its
image `baseChange K D` is the scalar extension of `D`, a subcoalgebra of `K ⊗[k] C`
identified with `K ⊗[k] D` by `baseChangeEquiv K D`.
-/

open scoped TensorProduct

namespace Langlands
namespace Subcoalgebra

universe u v w x

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
variable {E : Type w} [AddCommGroup E] [Module k E] [Coalgebra k E]

/-- The image of a homomorphism of coalgebras, as a subcoalgebra of the target. It is closed
under comultiplication because `Δ (f c) = (f ⊗ f) (Δ c)`, and the range of `f ⊗ f` is the
image of the tensor square of the range of `f`. -/
def range (f : C →ₗc[k] E) : Subcoalgebra k E where
  carrier := LinearMap.range f.toLinearMap
  comul_mem' := by
    rintro _ ⟨c, rfl⟩
    have h : LinearMap.range (TensorProduct.map (LinearMap.range f.toLinearMap).subtype
        (LinearMap.range f.toLinearMap).subtype) =
        LinearMap.range (TensorProduct.map f.toLinearMap f.toLinearMap) :=
      (TensorProduct.range_mapIncl _ _).trans (TensorProduct.range_map _ _).symm
    rw [h]
    exact ⟨Coalgebra.comul c, LinearMap.congr_fun f.map_comp_comul c⟩

@[simp]
theorem range_toSubmodule (f : C →ₗc[k] E) :
    (range f).toSubmodule = LinearMap.range f.toLinearMap := rfl

@[simp]
theorem mem_range {f : C →ₗc[k] E} {e : E} :
    e ∈ range f ↔ ∃ c, f c = e := Iff.rfl

/-- A homomorphism of coalgebras with all its values in a subcoalgebra `D`, as a
homomorphism into `D`. -/
noncomputable def codRestrict (D : Subcoalgebra k E) (f : C →ₗc[k] E)
    (h : ∀ c, f c ∈ D) : C →ₗc[k] D where
  toLinearMap := f.toLinearMap.codRestrict D.toSubmodule h
  counit_comp := LinearMap.ext fun c ↦ LinearMap.congr_fun f.counit_comp c
  map_comp_comul := by
    -- Both sides are compared in `E ⊗ E`, where `D ⊗ D` embeds.
    have hg : D.carrier.subtype ∘ₗ f.toLinearMap.codRestrict D.toSubmodule h = f.toLinearMap :=
      LinearMap.subtype_comp_codRestrict _ _ _
    refine LinearMap.ext fun c ↦ D.tensorSquareInclusion_injective ?_
    calc D.tensorSquareInclusion
          (TensorProduct.map (f.toLinearMap.codRestrict D.toSubmodule h)
            (f.toLinearMap.codRestrict D.toSubmodule h) (Coalgebra.comul c))
        = TensorProduct.map (D.carrier.subtype ∘ₗ f.toLinearMap.codRestrict D.toSubmodule h)
            (D.carrier.subtype ∘ₗ f.toLinearMap.codRestrict D.toSubmodule h)
            (Coalgebra.comul c) := TensorProduct.map_map _ _ _ _ _
      _ = Coalgebra.comul (f.toLinearMap c) := by
          rw [hg]
          exact LinearMap.congr_fun f.map_comp_comul c
      _ = D.tensorSquareInclusion (Coalgebra.comul (R := k) (A := D)
            (f.toLinearMap.codRestrict D.toSubmodule h c)) :=
          (D.map_comul_subtype (f.toLinearMap.codRestrict D.toSubmodule h c)).symm

@[simp]
theorem codRestrict_apply (D : Subcoalgebra k E) (f : C →ₗc[k] E)
    (h : ∀ c, f c ∈ D) (c : C) :
    (codRestrict D f h c : E) = f c := rfl

@[simp]
theorem subtype_comp_codRestrict (D : Subcoalgebra k E) (f : C →ₗc[k] E)
    (h : ∀ c, f c ∈ D) :
    D.subtype.comp (codRestrict D f h) = f :=
  CoalgHom.ext fun _ ↦ rfl

/-- A homomorphism of coalgebras, as a homomorphism onto its image. -/
noncomputable def rangeRestrict (f : C →ₗc[k] E) : C →ₗc[k] range f :=
  codRestrict (range f) f (fun c => ⟨c, rfl⟩)

@[simp]
theorem rangeRestrict_apply (f : C →ₗc[k] E) (c : C) :
    (rangeRestrict f c : E) = f c := rfl

theorem rangeRestrict_surjective (f : C →ₗc[k] E) :
    Function.Surjective (rangeRestrict f) := by
  rintro ⟨_, c, rfl⟩
  exact ⟨c, rfl⟩

theorem rangeRestrict_injective (f : C →ₗc[k] E) (hf : Function.Injective f) :
    Function.Injective (rangeRestrict f) :=
  fun _ _ h ↦ hf (congrArg Subtype.val h)

/-- An injective homomorphism of coalgebras is an equivalence onto its image. -/
noncomputable def equivRange (f : C →ₗc[k] E) (hf : Function.Injective f) :
    C ≃ₗc[k] range f :=
  CoalgEquiv.ofBijective (f := rangeRestrict f)
    ⟨rangeRestrict_injective f hf, rangeRestrict_surjective f⟩

@[simp]
theorem equivRange_apply (f : C →ₗc[k] E) (hf : Function.Injective f) (c : C) :
    (equivRange f hf c : E) = f c := rfl

variable (K : Type x) [Field K] [Algebra k K]

/-- The inclusion of a subcoalgebra `D` of `C` after extension of scalars to `K`, as a
homomorphism of `K`-coalgebras `K ⊗[k] D → K ⊗[k] C`. -/
noncomputable def baseChangeMap (D : Subcoalgebra k C) :
    K ⊗[k] D →ₗc[K] K ⊗[k] C :=
  Coalgebra.TensorProduct.map (CoalgHom.id K K) D.subtype

@[simp]
theorem baseChangeMap_toLinearMap (D : Subcoalgebra k C) :
    (baseChangeMap K D).toLinearMap = D.toSubmodule.subtype.baseChange K := rfl

@[simp]
theorem baseChangeMap_tmul (D : Subcoalgebra k C) (a : K) (d : D) :
    baseChangeMap K D (a ⊗ₜ[k] d) = a ⊗ₜ[k] (d : C) := rfl

/-- `K` is flat over `k`, so tensoring the inclusion of `D` with `K` keeps it injective. -/
theorem baseChangeMap_injective (D : Subcoalgebra k C) :
    Function.Injective (baseChangeMap K D) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := K)
    D.toSubmodule.subtype D.toSubmodule.injective_subtype

/-- The scalar extension of a subcoalgebra `D` of `C` to `K`: the image of `K ⊗[k] D` in
`K ⊗[k] C`. -/
noncomputable def baseChange (D : Subcoalgebra k C) : Subcoalgebra K (K ⊗[k] C) :=
  range (baseChangeMap K D)

@[simp]
theorem baseChange_toSubmodule (D : Subcoalgebra k C) :
    (baseChange K D).toSubmodule = D.toSubmodule.baseChange K := rfl

theorem mem_baseChange (D : Subcoalgebra k C) (z : K ⊗[k] C) :
    z ∈ baseChange K D ↔ ∃ t : K ⊗[k] D, baseChangeMap K D t = z := Iff.rfl

theorem tmul_mem_baseChange (D : Subcoalgebra k C) (a : K) {c : C} (hc : c ∈ D) :
    a ⊗ₜ[k] c ∈ baseChange K D :=
  Submodule.tmul_mem_baseChange_of_mem a hc

/-- The homomorphism of `K`-coalgebras from `K ⊗[k] D` onto the scalar extension of `D`. -/
noncomputable def toBaseChange (D : Subcoalgebra k C) :
    K ⊗[k] D →ₗc[K] baseChange K D :=
  rangeRestrict (baseChangeMap K D)

@[simp]
theorem toBaseChange_apply (D : Subcoalgebra k C) (z : K ⊗[k] D) :
    (toBaseChange K D z : K ⊗[k] C) = baseChangeMap K D z := rfl

@[simp]
theorem toBaseChange_tmul (D : Subcoalgebra k C) (a : K) (d : D) :
    (toBaseChange K D (a ⊗ₜ[k] d) : K ⊗[k] C) = a ⊗ₜ[k] (d : C) := rfl

theorem toBaseChange_bijective (D : Subcoalgebra k C) :
    Function.Bijective (toBaseChange K D) :=
  ⟨rangeRestrict_injective _ (baseChangeMap_injective K D), rangeRestrict_surjective _⟩

/-- The scalar extension of `D` is `K ⊗[k] D`, as `K`-coalgebras. -/
noncomputable def baseChangeEquiv (D : Subcoalgebra k C) :
    K ⊗[k] D ≃ₗc[K] baseChange K D :=
  equivRange (baseChangeMap K D) (baseChangeMap_injective K D)

@[simp]
theorem baseChangeEquiv_toCoalgHom (D : Subcoalgebra k C) :
    (baseChangeEquiv K D).toCoalgHom = toBaseChange K D := rfl

@[simp]
theorem baseChangeEquiv_apply (D : Subcoalgebra k C) (z : K ⊗[k] D) :
    (baseChangeEquiv K D z : K ⊗[k] C) = baseChangeMap K D z := rfl

@[simp]
theorem baseChangeEquiv_tmul (D : Subcoalgebra k C) (a : K) (d : D) :
    (baseChangeEquiv K D (a ⊗ₜ[k] d) : K ⊗[k] C) = a ⊗ₜ[k] (d : C) := rfl

@[simp]
theorem subtype_comp_toBaseChange (D : Subcoalgebra k C) :
    (baseChange K D).subtype.comp (toBaseChange K D) = baseChangeMap K D :=
  subtype_comp_codRestrict _ _ _

@[simp]
theorem baseChange_bot :
    baseChange K (⊥ : Subcoalgebra k C) = ⊥ := by
  ext z
  rw [← mem_toSubmodule, baseChange_toSubmodule, bot_toSubmodule, Submodule.baseChange_bot,
    Submodule.mem_bot, mem_bot]

@[simp]
theorem baseChange_top :
    baseChange K (⊤ : Subcoalgebra k C) = ⊤ := by
  ext z
  rw [← mem_toSubmodule, baseChange_toSubmodule, top_toSubmodule, Submodule.baseChange_top]
  exact iff_of_true Submodule.mem_top (mem_top z)

theorem baseChange_mono {D F : Subcoalgebra k C} (h : D ≤ F) :
    baseChange K D ≤ baseChange K F :=
  toSubmodule_le_toSubmodule.mp
    (Submodule.baseChange_mono K (toSubmodule_le_toSubmodule.mpr h))

/-- The scalar extension of a finite-dimensional subcoalgebra is finite dimensional: it is
linearly equivalent to `K ⊗[k] D`. -/
noncomputable instance instFiniteDimensionalBaseChange (D : Subcoalgebra k C)
    [FiniteDimensional k D] : FiniteDimensional K (baseChange K D) :=
  Module.Finite.equiv (baseChangeEquiv K D).toLinearEquiv

end Subcoalgebra
end Langlands
