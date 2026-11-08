import Langlands.Representation.Tensor.Finite
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Basic

/-!
# The complex conjugate of a complex vector space

`ConjSpace V` is the additive group of `V` with `c • v` acting as `conj c • v`.
Conjugate-linear maps into `V` are linear maps into `ConjSpace V`; a representation on
`V` acts linearly on `ConjSpace V`; its subrepresentations, after precomposition with a
surjective homomorphism, are those of the original representation. Conjugate-linear
maps of the factors of a finite tensor product induce a conjugate-linear map of the
tensor product, compatible with external tensor actions.
-/

noncomputable section

open scoped ComplexConjugate

namespace Langlands

universe u v

/-- The complex conjugate of a complex vector space: the same additive group,
with `c • v` acting as `conj c • v`. -/
def ConjSpace (V : Type u) : Type u := V

namespace ConjSpace

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

instance : AddCommGroup (ConjSpace V) := inferInstanceAs (AddCommGroup V)

instance : Module ℂ (ConjSpace V) := Module.compHom V (starRingEnd ℂ)

/-- The identity of the underlying additive group, conjugate-linear. -/
def equiv (V : Type u) [AddCommGroup V] [Module ℂ V] : V ≃ₗ⋆[ℂ] ConjSpace V where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' c v := by
    change c • v = (starRingEnd ℂ) ((starRingEnd ℂ) c) • v
    rw [Complex.conj_conj]
  left_inv _ := rfl
  right_inv _ := rfl

theorem smul_def (c : ℂ) (v : ConjSpace V) :
    c • v = equiv V (conj c • (equiv V).symm v) := rfl

/-- A conjugate-linear map is a linear map into the conjugate space. -/
def ofConjLinear {W : Type v} [AddCommGroup W] [Module ℂ W] (f : W →ₗ⋆[ℂ] V) :
    W →ₗ[ℂ] ConjSpace V where
  toFun w := equiv V (f w)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c w := by
    rw [map_smulₛₗ, map_smulₛₗ]
    simp

/-- A linear map into the conjugate space is a conjugate-linear map. -/
def toConjLinear {W : Type v} [AddCommGroup W] [Module ℂ W] (f : W →ₗ[ℂ] ConjSpace V) :
    W →ₗ⋆[ℂ] V :=
  (equiv V).symm.toLinearMap.comp f

@[simp]
theorem toConjLinear_apply {W : Type v} [AddCommGroup W] [Module ℂ W]
    (f : W →ₗ[ℂ] ConjSpace V) (w : W) :
    toConjLinear f w = (equiv V).symm (f w) := rfl

section Rep

variable {G : Type*} [Monoid G]

/-- The same action on the conjugate space: each operator is also linear for the
conjugated scalar action. -/
def rep (ρ : Representation ℂ G V) : Representation ℂ G (ConjSpace V) where
  toFun g := (equiv V).toLinearMap.comp ((ρ g).comp (equiv V).symm.toLinearMap)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

theorem rep_apply (ρ : Representation ℂ G V) (g : G) (v : ConjSpace V) :
    rep ρ g v = equiv V (ρ g ((equiv V).symm v)) := rfl

end Rep

end ConjSpace

section IrreducibleTransfer

variable {G : Type*} [Monoid G] {H : Type*} [Monoid H]
  {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Subrepresentations of `(ρ̄) ∘ φ` for a surjective `φ` are those of `ρ`, through the
conjugate-linear identity. -/
def conjCompSubrepOrderIso (ρ : Representation ℂ G V) (φ : H →* G)
    (hφ : Function.Surjective φ) :
    Subrepresentation ((ConjSpace.rep ρ).comp φ) ≃o Subrepresentation ρ where
  toFun W := ⟨W.toSubmodule.comap (ConjSpace.equiv V).toLinearMap, fun g v hv => by
    obtain ⟨h, rfl⟩ := hφ g
    exact W.apply_mem_toSubmodule h hv⟩
  invFun W := ⟨W.toSubmodule.comap (ConjSpace.equiv V).symm.toLinearMap, fun h v hv =>
    W.apply_mem_toSubmodule (φ h) hv⟩
  left_inv W := SetLike.ext fun _ => Iff.rfl
  right_inv W := SetLike.ext fun _ => Iff.rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_conjComp_iff (ρ : Representation ℂ G V) (φ : H →* G)
    (hφ : Function.Surjective φ) :
    Representation.IsIrreducible ((ConjSpace.rep ρ).comp φ) ↔ Representation.IsIrreducible ρ :=
  (conjCompSubrepOrderIso ρ φ hφ).isSimpleOrder_iff

end IrreducibleTransfer

section TensorConj

variable {ι : Type*}
  {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : ι → Type v} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The multilinear map `(v_i) ↦ ⊗ J_i v_i`, into the conjugate of the tensor product. -/
def tensorConjMultilinear (J : ∀ i, V i →ₗ⋆[ℂ] W i) :
    MultilinearMap ℂ V (ConjSpace (PiTensorProduct ℂ W)) where
  toFun m := ConjSpace.equiv _ (PiTensorProduct.tprod ℂ (fun i => J i (m i)))
  map_update_add' m i x y := by
    have h : ∀ z : V i, (fun j => J j (Function.update m i z j)) =
        Function.update (fun j => J j (m j)) i (J i z) := fun z => by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [h, h, h, map_add, MultilinearMap.map_update_add, map_add]
  map_update_smul' m i c x := by
    have h : ∀ z : V i, (fun j => J j (Function.update m i z j)) =
        Function.update (fun j => J j (m j)) i (J i z) := fun z => by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [h, h, map_smulₛₗ, MultilinearMap.map_update_smul, map_smulₛₗ]
    simp

/-- The conjugate-linear map `⊗ V_i → ⊗ W_i` induced by conjugate-linear `J_i`. -/
def tensorConj (J : ∀ i, V i →ₗ⋆[ℂ] W i) :
    PiTensorProduct ℂ V →ₗ⋆[ℂ] PiTensorProduct ℂ W :=
  ConjSpace.toConjLinear (PiTensorProduct.lift (tensorConjMultilinear J))

@[simp]
theorem tensorConj_tprod (J : ∀ i, V i →ₗ⋆[ℂ] W i) (v : ∀ i, V i) :
    tensorConj J (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun i => J i (v i)) := by
  simp [tensorConj, tensorConjMultilinear]

/-- The conjugate-linear equivalence `⊗ V_i ≃ ⊗ W_i` induced by conjugate-linear
equivalences `J_i`. -/
def tensorConjEquiv (J : ∀ i, V i ≃ₗ⋆[ℂ] W i) :
    PiTensorProduct ℂ V ≃ₗ⋆[ℂ] PiTensorProduct ℂ W :=
  { tensorConj (fun i => (J i).toLinearMap) with
    invFun := tensorConj (fun i => (J i).symm.toLinearMap)
    left_inv := fun x => by
      induction x using PiTensorProduct.induction_on with
      | smul_tprod c v =>
        change tensorConj _ (tensorConj _ (c • PiTensorProduct.tprod ℂ v)) = _
        rw [map_smulₛₗ, map_smulₛₗ, tensorConj_tprod, tensorConj_tprod]
        simp
      | add x y hx hy =>
        change tensorConj _ (tensorConj _ (x + y)) = x + y
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) hx hy
    right_inv := fun x => by
      induction x using PiTensorProduct.induction_on with
      | smul_tprod c v =>
        change tensorConj _ (tensorConj _ (c • PiTensorProduct.tprod ℂ v)) = _
        rw [map_smulₛₗ, map_smulₛₗ, tensorConj_tprod, tensorConj_tprod]
        simp
      | add x y hx hy =>
        change tensorConj _ (tensorConj _ (x + y)) = x + y
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) hx hy }

@[simp]
theorem tensorConjEquiv_tprod (J : ∀ i, V i ≃ₗ⋆[ℂ] W i) (v : ∀ i, V i) :
    tensorConjEquiv J (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => J i (v i)) :=
  tensorConj_tprod _ v

/-- Conjugate-linear equivariance passes to external tensor products. -/
theorem tensorConjEquiv_external {H : ι → Type*} [∀ i, Group (H i)]
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (σ : ∀ i, Representation ℂ (H i) (W i))
    (J : ∀ i, V i ≃ₗ⋆[ℂ] W i) (m : ∀ i, H i)
    (hJ : ∀ i (v : V i), J i (ρ i (m i) v) = σ i (m i) (J i v)) (x : PiTensorProduct ℂ V) :
    tensorConjEquiv J (FiniteTensor.external ρ m x) =
      FiniteTensor.external σ m (tensorConjEquiv J x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul, FiniteTensor.external_tprod,
      tensorConjEquiv_tprod, tensorConjEquiv_tprod, FiniteTensor.external_tprod]
    congr 2
    funext i
    exact hJ i (v i)
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, hx, hy]

end TensorConj

end Langlands
