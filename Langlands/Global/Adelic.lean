import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Concrete adelic objects and continuous local maps

The arithmetic objects are Mathlib's actual completions, restricted products,
units and quotient. See `Adelic.md` for sources and the topology conventions.
-/

noncomputable section

universe u

namespace Langlands.Global

open scoped RestrictedProduct

variable (K : Type u) [Field K] [NumberField K]

/-- Finite places, indexed by the nonzero prime ideals of the ring of integers. -/
abbrev FinitePlace := IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- Archimedean places, with conjugate complex embeddings identified. -/
abbrev InfinitePlace := NumberField.InfinitePlace K

/-- The actual adic completion at a finite place. -/
abbrev FiniteCompletion (v : FinitePlace K) := v.adicCompletion K

/-- The actual completion at an archimedean place. -/
abbrev InfiniteCompletion (v : InfinitePlace K) := v.Completion

/-- The finite restricted product relative to the local valuation subrings. -/
abbrev FiniteAdeles := IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K

/-- The finite product of archimedean completions. -/
abbrev InfiniteAdeles := NumberField.InfiniteAdeleRing K

/-- The full adele ring, with its product/restricted-product topology. -/
abbrev Adeles := NumberField.AdeleRing (NumberField.RingOfIntegers K) K

/-- Finite ideles with the units topology, tracking value and inverse. -/
abbrev FiniteIdeles := (FiniteAdeles K)ˣ

/-- Full ideles with the units topology, tracking value and inverse. -/
abbrev Ideles := NumberField.IdeleGroup (NumberField.RingOfIntegers K) K

/-- The actual idele-class quotient, with quotient topology. -/
abbrev IdeleClasses := NumberField.IdeleClassGroup (NumberField.RingOfIntegers K) K

/-- The diagonal embedding of the number field in its adele ring. -/
abbrev diagonal : K →+* Adeles K := algebraMap K (Adeles K)

/-- The diagonal embedding of nonzero field elements as principal ideles. -/
abbrev diagonalUnits : Kˣ →* Ideles K :=
  NumberField.IdeleGroup.unitEmbedding (NumberField.RingOfIntegers K) K

/-- The subgroup of principal ideles; it is the actual range of `diagonalUnits`. -/
abbrev principalIdeles : Subgroup (Ideles K) :=
  NumberField.IdeleGroup.principalSubgroup (NumberField.RingOfIntegers K) K

/-- The continuous quotient map to idele classes. -/
def ideleClassMap : Ideles K →ₜ* IdeleClasses K where
  toMonoidHom := QuotientGroup.mk' (principalIdeles K)
  continuous_toFun := QuotientGroup.continuous_mk

/-- Projection of a full adele onto one finite completion. -/
def finiteProjection (v : FinitePlace K) : Adeles K →+* FiniteCompletion K v where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Projection of a full adele onto one archimedean completion. -/
def infiniteProjection (v : InfinitePlace K) : Adeles K →+* InfiniteCompletion K v where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_finiteProjection (v : FinitePlace K) :
    Continuous (finiteProjection K v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_infiniteProjection (v : InfinitePlace K) :
    Continuous (infiniteProjection K v) :=
  (continuous_apply v).comp continuous_fst

/-- The continuous local component map on ideles at a finite place. -/
def finiteIdeleProjection (v : FinitePlace K) :
    Ideles K →ₜ* (FiniteCompletion K v)ˣ where
  toMonoidHom := Units.map (finiteProjection K v).toMonoidHom
  continuous_toFun := (continuous_finiteProjection K v).units_map _

/-- The continuous local component map on ideles at an archimedean place. -/
def infiniteIdeleProjection (v : InfinitePlace K) :
    Ideles K →ₜ* (InfiniteCompletion K v)ˣ where
  toMonoidHom := Units.map (infiniteProjection K v).toMonoidHom
  continuous_toFun := (continuous_infiniteProjection K v).units_map _

private theorem continuous_finiteSingle (v : FinitePlace K) :
    Continuous (IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v) := by
  classical
  let S : Set (FinitePlace K) := {v}ᶜ
  let f : FiniteCompletion K v →
      Πʳ w : FinitePlace K, [FiniteCompletion K w, w.adicCompletionIntegers K]_[Filter.principal S] :=
    fun x ↦ ⟨Pi.mulSingle v x, fun w hw ↦ by
      have h : w ≠ v := by simpa [S] using hw
      simp [Pi.mulSingle_eq_of_ne h]⟩
  have hf : Continuous f :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  have hS : Filter.cofinite ≤ Filter.principal S := by simp [S]
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

/-- Insert a local unit at a finite place and `1` at every other place. -/
def finiteIdeleInclusion (v : FinitePlace K) :
    (FiniteCompletion K v)ˣ →ₜ* Ideles K where
  toMonoidHom :=
    NumberField.IdeleGroup.ofAdicCompletion (NumberField.RingOfIntegers K) K v
  continuous_toFun :=
    (continuous_const.prodMk (continuous_finiteSingle K v)).units_map _

/-- Insert a local unit at an infinite place and `1` at every other place. -/
def infiniteIdeleInclusion (v : InfinitePlace K) :
    (InfiniteCompletion K v)ˣ →ₜ* Ideles K where
  toMonoidHom :=
    NumberField.IdeleGroup.ofCompletion (NumberField.RingOfIntegers K) K v
  continuous_toFun := by
    classical
    exact ((continuous_mulSingle v).prodMk continuous_const).units_map _

/-- The finite local map into the actual idele-class quotient. -/
def finiteClassInclusion (v : FinitePlace K) :
    (FiniteCompletion K v)ˣ →ₜ* IdeleClasses K :=
  (ideleClassMap K).comp (finiteIdeleInclusion K v)

/-- The infinite local map into the actual idele-class quotient. -/
def infiniteClassInclusion (v : InfinitePlace K) :
    (InfiniteCompletion K v)ˣ →ₜ* IdeleClasses K :=
  (ideleClassMap K).comp (infiniteIdeleInclusion K v)

/-- Separate an idele into its infinite and finite parts, preserving topology. -/
def ideleProductEquiv : Ideles K ≃ₜ* (InfiniteAdeles K)ˣ × FiniteIdeles K where
  toMulEquiv := MulEquiv.prodUnits
  continuous_toFun := Homeomorph.prodUnits.continuous_toFun
  continuous_invFun := Homeomorph.prodUnits.continuous_invFun

/-- Insert an archimedean idele, with finite part equal to `1`. -/
def infiniteIdelesInclusion : (InfiniteAdeles K)ˣ →ₜ* Ideles K where
  toMonoidHom := (ideleProductEquiv K).symm.toMonoidHom.comp
    (MonoidHom.inl (InfiniteAdeles K)ˣ (FiniteIdeles K))
  continuous_toFun := (ideleProductEquiv K).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

/-- Insert a finite idele, with infinite part equal to `1`. -/
def finiteIdelesInclusion : FiniteIdeles K →ₜ* Ideles K where
  toMonoidHom := (ideleProductEquiv K).symm.toMonoidHom.comp
    (MonoidHom.inr (InfiniteAdeles K)ˣ (FiniteIdeles K))
  continuous_toFun := (ideleProductEquiv K).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

@[simp]
theorem finiteProjection_diagonal (v : FinitePlace K) (x : K) :
    finiteProjection K v (diagonal K x) = algebraMap K (FiniteCompletion K v) x := rfl

@[simp]
theorem infiniteProjection_diagonal (v : InfinitePlace K) (x : K) :
    infiniteProjection K v (diagonal K x) = algebraMap K (InfiniteCompletion K v) x := rfl

@[simp]
theorem finiteIdeleProjection_inclusion (v : FinitePlace K) (x : (FiniteCompletion K v)ˣ) :
    finiteIdeleProjection K v (finiteIdeleInclusion K v x) = x := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_same v x.val

@[simp]
theorem infiniteIdeleProjection_inclusion (v : InfinitePlace K)
    (x : (InfiniteCompletion K v)ˣ) :
    infiniteIdeleProjection K v (infiniteIdeleInclusion K v x) = x := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_same v x.val

@[simp]
theorem ideleClassMap_diagonalUnits (x : Kˣ) :
    ideleClassMap K (diagonalUnits K x) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩

end Langlands.Global
