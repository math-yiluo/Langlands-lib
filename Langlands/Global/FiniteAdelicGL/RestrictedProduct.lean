import Langlands.Global.FiniteAdelicGL.LocalFactor
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# The restricted product description of finite adelic general linear groups
-/

noncomputable section

universe u

namespace Langlands.Global.FiniteAdelicGL

open scoped RestrictedProduct

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : DecidableEq (FinitePlace K) := Classical.decEq _

/-- The actual restricted product of the finite local matrix groups. -/
abbrev LocalRestrictedProduct :=
  Πʳ v : FinitePlace K, [FiniteLocalGL K n v, localIntegral K n v]

/-- Outside finitely many places both a matrix and its inverse have integral entries. -/
theorem eventually_localIntegral (g : FiniteAdelicGL K n) :
    ∀ᶠ v in Filter.cofinite, localProjection K n v g ∈ localIntegral K n v := by
  have h (a : FiniteAdelicGL K n) :
      ∀ᶠ v in Filter.cofinite, ∀ i j, a i j v ∈ v.adicCompletionIntegers K :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (a i j).2
  filter_upwards [h g, h g⁻¹] with v hv hi
  exact ⟨hv, hi⟩

/-- Evaluate an adelic matrix unit at every finite place. -/
def toRestrictedProduct : FiniteAdelicGL K n →* LocalRestrictedProduct K n where
  toFun g := ⟨fun v => localProjection K n v g, eventually_localIntegral K n g⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact map_one (localProjection K n v)
  map_mul' g h := by
    apply RestrictedProduct.ext
    intro v
    exact map_mul (localProjection K n v) g h

@[simp]
theorem toRestrictedProduct_apply (g : FiniteAdelicGL K n) (v : FinitePlace K) :
    toRestrictedProduct K n g v = localProjection K n v g := rfl

private def assembleMatrix (x : LocalRestrictedProduct K n) :
    Matrix (Fin n) (Fin n) (FiniteAdeles K) := fun i j =>
  ⟨fun v => x v i j, x.2.mono fun v hv => (mem_localIntegral K n v (x v)).mp hv |>.1 i j⟩

private def entryEval (v : FinitePlace K) : FiniteAdeles K →+* FiniteCompletion K v :=
  RestrictedProduct.evalRingHom _ v

private theorem eval_assembleMatrix (x : LocalRestrictedProduct K n) (v : FinitePlace K) :
    (entryEval K v).mapMatrix (assembleMatrix K n x) = (x v).val := rfl

private theorem matrix_ext_eval {A B : Matrix (Fin n) (Fin n) (FiniteAdeles K)}
    (h : ∀ v, (entryEval K v).mapMatrix A = (entryEval K v).mapMatrix B) : A = B := by
  apply Matrix.ext
  intro i j
  apply RestrictedProduct.ext
  intro v
  exact congrArg (fun C => C i j) (h v)

/-- Assemble local matrices and their local inverse matrices into an adelic unit. -/
def fromRestrictedProduct (x : LocalRestrictedProduct K n) : FiniteAdelicGL K n where
  val := assembleMatrix K n x
  inv := assembleMatrix K n x⁻¹
  val_inv := by
    apply matrix_ext_eval K n
    intro v
    rw [map_mul, map_one, eval_assembleMatrix, eval_assembleMatrix]
    exact (x v).val_inv
  inv_val := by
    apply matrix_ext_eval K n
    intro v
    rw [map_mul, map_one, eval_assembleMatrix, eval_assembleMatrix]
    exact (x v).inv_val

@[simp]
theorem fromRestrictedProduct_apply (x : LocalRestrictedProduct K n)
    (i j : Fin n) (v : FinitePlace K) :
    fromRestrictedProduct K n x i j v = x v i j := rfl

@[simp]
theorem fromRestrictedProduct_inv_apply (x : LocalRestrictedProduct K n)
    (i j : Fin n) (v : FinitePlace K) :
    (fromRestrictedProduct K n x)⁻¹ i j v = (x v)⁻¹ i j := rfl

@[simp]
theorem localProjection_fromRestrictedProduct (x : LocalRestrictedProduct K n)
    (v : FinitePlace K) :
    localProjection K n v (fromRestrictedProduct K n x) = x v := by
  apply Units.ext
  rfl

@[simp]
theorem fromRestrictedProduct_toRestrictedProduct (g : FiniteAdelicGL K n) :
    fromRestrictedProduct K n (toRestrictedProduct K n g) = g := by
  apply ext_localProjection K n
  intro v
  simp

@[simp]
theorem toRestrictedProduct_fromRestrictedProduct (x : LocalRestrictedProduct K n) :
    toRestrictedProduct K n (fromRestrictedProduct K n x) = x := by
  apply RestrictedProduct.ext
  intro v
  exact localProjection_fromRestrictedProduct K n x v

private theorem continuous_assembleMatrix : Continuous (assembleMatrix K n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact RestrictedProduct.mapAlong_continuous
    (FiniteLocalGL K n) (FiniteCompletion K) id Filter.tendsto_id
    (fun v (g : FiniteLocalGL K n v) => g i j)
    (Filter.Eventually.of_forall fun v g hg => (mem_localIntegral K n v g).mp hg |>.1 i j)
    (fun v => (continuous_apply j).comp
      (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id i))

theorem continuous_fromRestrictedProduct : Continuous (fromRestrictedProduct K n) := by
  let : Fact (∀ v, IsOpen (localIntegral K n v : Set (FiniteLocalGL K n v))) :=
    ⟨fun v => (localIntegral K n v).isOpen⟩
  rw [Units.continuous_iff]
  exact ⟨continuous_assembleMatrix K n, (continuous_assembleMatrix K n).comp continuous_inv⟩

theorem continuous_toRestrictedProduct : Continuous (toRestrictedProduct K n) := by
  let : Fact (∀ v, IsOpen (localIntegral K n v : Set (FiniteLocalGL K n v))) :=
    ⟨fun v => (localIntegral K n v).isOpen⟩
  let f : standardIntegral K n → ∀ v, localIntegral K n v := fun g v =>
    ⟨localProjection K n v g, (mem_standardIntegral_iff_local K n g).mp g.2 v⟩
  have hf : Continuous f := continuous_pi fun v =>
    ((localProjection K n v).continuous.comp continuous_subtype_val).subtype_mk _
  have hc : Continuous (fun g : standardIntegral K n => toRestrictedProduct K n g) :=
    (RestrictedProduct.isEmbedding_structureMap
      (R := FiniteLocalGL K n) (A := fun v => (localIntegral K n v : Set _))
      (𝓕 := Filter.cofinite)).continuous.comp hf
  apply continuous_of_continuousAt_one (toRestrictedProduct K n)
  exact (standardIntegral K n).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
    (hc.continuousAt (x := (1 : standardIntegral K n)))

/-- The finite adelic matrix-unit group, with its existing topology, is the
restricted product of the actual finite local general linear groups. -/
def restrictedProductEquiv : FiniteAdelicGL K n ≃ₜ* LocalRestrictedProduct K n where
  toFun := toRestrictedProduct K n
  invFun := fromRestrictedProduct K n
  left_inv := fromRestrictedProduct_toRestrictedProduct K n
  right_inv := toRestrictedProduct_fromRestrictedProduct K n
  map_mul' := (toRestrictedProduct K n).map_mul
  continuous_toFun := continuous_toRestrictedProduct K n
  continuous_invFun := continuous_fromRestrictedProduct K n

@[simp]
theorem restrictedProductEquiv_apply (g : FiniteAdelicGL K n) (v : FinitePlace K) :
    restrictedProductEquiv K n g v = localProjection K n v g := rfl

@[simp]
theorem restrictedProductEquiv_symm_apply (x : LocalRestrictedProduct K n)
    (i j : Fin n) (v : FinitePlace K) :
    (restrictedProductEquiv K n).symm x i j v = x v i j := rfl

@[simp]
theorem restrictedProductEquiv_symm_inv_apply (x : LocalRestrictedProduct K n)
    (i j : Fin n) (v : FinitePlace K) :
    ((restrictedProductEquiv K n).symm x)⁻¹ i j v = (x v)⁻¹ i j := rfl

/-- A local inclusion corresponds to the restricted family equal to one elsewhere. -/
theorem restrictedProductEquiv_localInclusion (v : FinitePlace K)
    (g : FiniteLocalGL K n v) :
    restrictedProductEquiv K n (localInclusion K n v g) =
      RestrictedProduct.mulSingle (fun w => localIntegral K n w) v g := by
  classical
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst w
    simp only [restrictedProductEquiv_apply, localProjection_localInclusion,
      RestrictedProduct.mulSingle_eq_same]
  · rw [restrictedProductEquiv_apply, localProjection_localInclusion_of_ne K n v w hw,
      RestrictedProduct.mulSingle_eq_of_ne (fun w => localIntegral K n w) g hw]

@[simp]
theorem restrictedProductEquiv_symm_mulSingle (v : FinitePlace K)
    (g : FiniteLocalGL K n v) :
    (restrictedProductEquiv K n).symm
      (RestrictedProduct.mulSingle (fun w => localIntegral K n w) v g) =
      localInclusion K n v g := by
  rw [← restrictedProductEquiv_localInclusion, ContinuousMulEquiv.symm_apply_apply]

/-- The open subgroup of restricted families integral at every finite place. -/
def allIntegral : OpenSubgroup (LocalRestrictedProduct K n) where
  carrier := {x | ∀ v, x v ∈ localIntegral K n v}
  one_mem' v := (localIntegral K n v).one_mem
  mul_mem' hx hy v := (localIntegral K n v).mul_mem (hx v) (hy v)
  inv_mem' hx v := (localIntegral K n v).inv_mem (hx v)
  isOpen' := RestrictedProduct.isOpen_forall_mem fun v => (localIntegral K n v).isOpen

@[simp]
theorem mem_allIntegral (x : LocalRestrictedProduct K n) :
    x ∈ allIntegral K n ↔ ∀ v, x v ∈ localIntegral K n v := Iff.rfl

@[simp]
theorem restrictedProductEquiv_mem_allIntegral (g : FiniteAdelicGL K n) :
    restrictedProductEquiv K n g ∈ allIntegral K n ↔ g ∈ standardIntegral K n :=
  (mem_standardIntegral_iff_local K n g).symm

/-- The equivalence carries precisely the standard integral subgroup onto the
all-integral subgroup of the restricted product. -/
theorem map_standardIntegral_restrictedProductEquiv :
    (standardIntegral K n).toSubgroup.map (restrictedProductEquiv K n).toMonoidHom =
      (allIntegral K n).toSubgroup := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (restrictedProductEquiv_mem_allIntegral K n g).mpr hg
  · intro hx
    refine ⟨(restrictedProductEquiv K n).symm x, ?_,
      (restrictedProductEquiv K n).apply_symm_apply x⟩
    exact (restrictedProductEquiv_mem_allIntegral K n _).mp (by simpa using hx)

theorem image_standardIntegral_restrictedProductEquiv :
    restrictedProductEquiv K n '' (standardIntegral K n : Set (FiniteAdelicGL K n)) =
      (allIntegral K n : Set (LocalRestrictedProduct K n)) :=
  congrArg (fun H : Subgroup (LocalRestrictedProduct K n) =>
    (H : Set (LocalRestrictedProduct K n))) (map_standardIntegral_restrictedProductEquiv K n)

end Langlands.Global.FiniteAdelicGL
