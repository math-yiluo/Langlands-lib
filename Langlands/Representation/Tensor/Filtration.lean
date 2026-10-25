import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Filtration.JordanHolderTransportProof
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Actual image filtrations for binary tensor products over a field. -/

noncomputable section

open scoped TensorProduct

namespace Langlands

universe uK uG uA uB

namespace TensorFiltration

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {A : Rep.{uA} k G} (B : Rep.{uB} k G)

/-- The actual inclusion of an invariant subspace. -/
def inclusion (S : Subrepresentation A.ρ) :
    S.toRepresentation.IntertwiningMap A.ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/-- Tensor the actual subspace inclusion with the identity of the right factor. -/
def tensorInclusion (S : Subrepresentation A.ρ) :
    (Representation.tprod S.toRepresentation B.ρ).IntertwiningMap
      (Representation.tprod A.ρ B.ρ) :=
  (inclusion S).rTensor B.ρ

@[simp]
theorem tensorInclusion_tmul (S : Subrepresentation A.ρ)
    (x : S.toSubmodule) (b : B) :
    tensorInclusion B S (x ⊗ₜ[k] b) = (x : A) ⊗ₜ[k] b := rfl

/-- The canonical invariant image of `S ⊗ B` in `A ⊗ B`. -/
def tensorImage (S : Subrepresentation A.ρ) :
    Subrepresentation (Representation.tprod A.ρ B.ρ) :=
  (tensorInclusion B S).range

@[simp]
theorem tensorImage_toSubmodule (S : Subrepresentation A.ρ) :
    (tensorImage B S).toSubmodule =
      LinearMap.range (S.toSubmodule.subtype.rTensor B) := rfl

theorem mem_tensorImage (S : Subrepresentation A.ρ) (z : A ⊗[k] B) :
    z ∈ tensorImage B S ↔
      ∃ x : S.toSubmodule ⊗[k] B, tensorInclusion B S x = z := Iff.rfl

theorem tensorInclusion_injective (S : Subrepresentation A.ρ) :
    Function.Injective (tensorInclusion B S) :=
  Module.Flat.rTensor_preserves_injective_linearMap
    S.toSubmodule.subtype Subtype.val_injective

/-- The tensor product with the subspace, mapped onto its actual image. -/
def tensorImageMap (S : Subrepresentation A.ρ) :
    (Representation.tprod S.toRepresentation B.ρ).IntertwiningMap
      (tensorImage B S).toRepresentation where
  toLinearMap := (tensorInclusion B S).toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun ((tensorInclusion B S).isIntertwining' g) x

/-- Flatness over a field identifies the subspace tensor product with its image. -/
def tensorImageEquiv (S : Subrepresentation A.ρ) :
    (Representation.tprod S.toRepresentation B.ρ).Equiv
      (tensorImage B S).toRepresentation :=
  (tensorImageMap B S).ofBijective
    ⟨fun _ _ h => tensorInclusion_injective B S (congrArg Subtype.val h),
      fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

@[simp]
theorem tensorImageEquiv_val (S : Subrepresentation A.ρ)
    (x : S.toSubmodule ⊗[k] B) :
    (tensorImageEquiv B S x).val = tensorInclusion B S x := rfl

/-- Inclusion between nested actual subspaces. -/
def stepInclusion {S T : Subrepresentation A.ρ} (h : S ≤ T) :
    S.toRepresentation.IntertwiningMap T.toRepresentation where
  toLinearMap := Submodule.inclusion h
  isIntertwining' _ := rfl

theorem tensorInclusion_stepInclusion {S T : Subrepresentation A.ρ}
    (h : S ≤ T) (x : S.toSubmodule ⊗[k] B) :
    tensorInclusion B T ((stepInclusion h).rTensor B.ρ x) =
      tensorInclusion B S x := by
  change (T.toSubmodule.subtype.rTensor B)
      ((Submodule.inclusion h).rTensor B x) =
    (S.toSubmodule.subtype.rTensor B) x
  rw [← LinearMap.rTensor_comp_apply]
  rfl

theorem tensorImage_mono : Monotone (tensorImage (A := A) B) := by
  rintro S T h _ ⟨x, rfl⟩
  exact ⟨(stepInclusion h).rTensor B.ρ x,
    tensorInclusion_stepInclusion B h x⟩

@[simp]
theorem tensorImage_bot :
    tensorImage B (⊥ : Subrepresentation A.ρ) = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  change LinearMap.range
    ((⊥ : Subrepresentation A.ρ).toSubmodule.subtype.rTensor B) = ⊥
  have h : (⊥ : Subrepresentation A.ρ).toSubmodule.subtype = 0 := by
    ext x
    exact x.property
  rw [h, LinearMap.rTensor_zero, LinearMap.range_zero]

@[simp]
theorem tensorImage_top :
    tensorImage B (⊤ : Subrepresentation A.ρ) = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  apply LinearMap.range_eq_top.mpr
  exact LinearMap.rTensor_surjective B (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)

open LengthCriterionProof

/-- The projection onto the actual quotient of two nested steps. -/
def quotientProjection (S T : Subrepresentation A.ρ) :
    T.toRepresentation.IntertwiningMap (quotientRep S T) where
  toLinearMap := (lower S T).mkQ
  isIntertwining' _ := rfl

theorem step_exact {S T : Subrepresentation A.ρ} (h : S ≤ T) :
    Function.Exact (stepInclusion h).toLinearMap
      (quotientProjection S T).toLinearMap := by
  apply LinearMap.exact_iff.mpr
  change LinearMap.ker (lower S T).mkQ = LinearMap.range (Submodule.inclusion h)
  rw [Submodule.ker_mkQ]
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

theorem tensorInclusion_mem_image_iff {S T : Subrepresentation A.ρ}
    (h : S ≤ T) (x : T.toSubmodule ⊗[k] B) :
    tensorInclusion B T x ∈ tensorImage B S ↔
      x ∈ LinearMap.range ((stepInclusion h).toLinearMap.rTensor B) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, tensorInclusion_injective B T
      ((tensorInclusion_stepInclusion B h y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (tensorInclusion_stepInclusion B h y).symm⟩

/-- Undo the image inclusion, then tensor the genuine quotient projection. -/
def tensorQuotientMap (S T : Subrepresentation A.ρ) :
    (tensorImage B T).toRepresentation.IntertwiningMap
      (Representation.tprod (quotientRep S T) B.ρ) :=
  ((quotientProjection S T).rTensor B.ρ).comp
    (tensorImageEquiv B T).symm.toIntertwiningMap

theorem tensorQuotientMap_kernel {S T : Subrepresentation A.ρ}
    (h : S ≤ T) (x : (tensorImage B T).toSubmodule) :
    tensorQuotientMap B S T x = 0 ↔ x.val ∈ tensorImage B S := by
  let z := (tensorImageEquiv B T).symm x
  have hz : tensorInclusion B T z = x.val := by
    change (tensorImageEquiv B T ((tensorImageEquiv B T).symm x)).val = x.val
    rw [Representation.Equiv.apply_symm_apply]
  have hker :
      LinearMap.ker ((quotientProjection S T).toLinearMap.rTensor B) =
        LinearMap.range ((stepInclusion h).toLinearMap.rTensor B) :=
    (rTensor_exact B (step_exact h)
      (Submodule.mkQ_surjective (lower S T))).linearMap_ker_eq
  change z ∈ LinearMap.ker ((quotientProjection S T).toLinearMap.rTensor B) ↔
    x.val ∈ tensorImage B S
  rw [hker, ← tensorInclusion_mem_image_iff B h z, hz]

theorem tensorQuotientMap_surjective (S T : Subrepresentation A.ρ) :
    Function.Surjective (tensorQuotientMap B S T) :=
  (LinearMap.rTensor_surjective B
    (Submodule.mkQ_surjective (lower S T))).comp
      (tensorImageEquiv B T).symm.surjective

/-- Descend to the existing quotient of actual tensor image subspaces. -/
def quotientTensorMap {S T : Subrepresentation A.ρ} (h : S ≤ T) :
    (quotientRep (tensorImage B S) (tensorImage B T)).IntertwiningMap
      (Representation.tprod (quotientRep S T) B.ρ) where
  toLinearMap := (lower (tensorImage B S) (tensorImage B T)).liftQ
    (tensorQuotientMap B S T).toLinearMap
    (fun x hx => (tensorQuotientMap_kernel B h x).mpr hx)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun ((tensorQuotientMap B S T).isIntertwining' g) x

theorem quotientTensorMap_bijective {S T : Subrepresentation A.ρ} (h : S ≤ T) :
    Function.Bijective (quotientTensorMap B h) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _
      (fun x hx => (tensorQuotientMap_kernel B h x).mp hx)
  · intro x
    obtain ⟨y, rfl⟩ := tensorQuotientMap_surjective B S T x
    exact ⟨(lower (tensorImage B S) (tensorImage B T)).mkQ y, rfl⟩

/-- Tensor exactness identifies the actual image quotient with the tensor quotient. -/
def quotientTensorEquiv {S T : Subrepresentation A.ρ} (h : S ≤ T) :
    (quotientRep (tensorImage B S) (tensorImage B T)).Equiv
      (Representation.tprod (quotientRep S T) B.ρ) :=
  (quotientTensorMap B h).ofBijective (quotientTensorMap_bijective B h)

@[simp]
theorem quotientTensorEquiv_mk {S T : Subrepresentation A.ρ}
    (h : S ≤ T) (x : T.toSubmodule ⊗[k] B) :
    quotientTensorEquiv B h
        ((lower (tensorImage B S) (tensorImage B T)).mkQ (tensorImageEquiv B T x)) =
      (quotientProjection S T).rTensor B.ρ x := by
  change (quotientProjection S T).rTensor B.ρ
    ((tensorImageEquiv B T).symm (tensorImageEquiv B T x)) = _
  rw [Representation.Equiv.symm_apply_apply]

@[simp]
theorem quotientTensorEquiv_mk_tmul {S T : Subrepresentation A.ρ}
    (h : S ≤ T) (x : T.toSubmodule) (b : B) :
    quotientTensorEquiv B h
        ((lower (tensorImage B S) (tensorImage B T)).mkQ
          (tensorImageEquiv B T (x ⊗ₜ[k] b))) =
      (lower S T).mkQ x ⊗ₜ[k] b := by
  rw [quotientTensorEquiv_mk]
  rfl

/-- The canonical inclusion after tensoring on the left. -/
def leftTensorInclusion (S : Subrepresentation A.ρ) :
    (Representation.tprod B.ρ S.toRepresentation).IntertwiningMap
      (Representation.tprod B.ρ A.ρ) :=
  (inclusion S).lTensor B.ρ

@[simp]
theorem leftTensorInclusion_tmul (S : Subrepresentation A.ρ)
    (b : B) (x : S.toSubmodule) :
    leftTensorInclusion B S (b ⊗ₜ[k] x) = b ⊗ₜ[k] (x : A) := rfl

/-- The actual image of a subspace tensor product with a fixed left factor. -/
def leftTensorImage (S : Subrepresentation A.ρ) :
    Subrepresentation (Representation.tprod B.ρ A.ρ) :=
  (leftTensorInclusion B S).range

@[simp]
theorem leftTensorImage_toSubmodule (S : Subrepresentation A.ρ) :
    (leftTensorImage B S).toSubmodule =
      LinearMap.range (S.toSubmodule.subtype.lTensor B) := rfl

theorem mem_leftTensorImage (S : Subrepresentation A.ρ) (z : B ⊗[k] A) :
    z ∈ leftTensorImage B S ↔
      ∃ x : B ⊗[k] S.toSubmodule, leftTensorInclusion B S x = z := Iff.rfl

theorem leftTensorInclusion_comm (S : Subrepresentation A.ρ)
    (x : S.toSubmodule ⊗[k] B) :
    leftTensorInclusion B S (Representation.TensorProduct.comm S.toRepresentation B.ρ x) =
      Representation.TensorProduct.comm A.ρ B.ρ (tensorInclusion B S x) := by
  have h :
      (leftTensorInclusion B S).toLinearMap.comp
          (Representation.TensorProduct.comm S.toRepresentation B.ρ).toLinearMap =
        (Representation.TensorProduct.comm A.ρ B.ρ).toLinearMap.comp
          (tensorInclusion B S).toLinearMap := by
    ext x b
    rfl
  exact LinearMap.congr_fun h x

theorem map_tensorImage_comm (S : Subrepresentation A.ρ) :
    JordanHolderTransportProof.mapSub (Representation.TensorProduct.comm A.ρ B.ρ)
        (tensorImage B S) = leftTensorImage B S := by
  apply SetLike.ext
  intro z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨Representation.TensorProduct.comm S.toRepresentation B.ρ x,
      leftTensorInclusion_comm B S x⟩
  · rintro ⟨x, rfl⟩
    let y := (Representation.TensorProduct.comm S.toRepresentation B.ρ).symm x
    refine ⟨tensorInclusion B S y, ⟨y, rfl⟩, ?_⟩
    change Representation.TensorProduct.comm A.ρ B.ρ (tensorInclusion B S y) =
      leftTensorInclusion B S x
    have h := (leftTensorInclusion_comm B S y).symm
    simpa only [y, Representation.Equiv.apply_symm_apply] using h

theorem leftTensorImage_mono : Monotone (leftTensorImage (A := A) B) := by
  intro S T h
  rw [← map_tensorImage_comm B S, ← map_tensorImage_comm B T]
  exact (JordanHolderTransportProof.subrepOrderIso
    (Representation.TensorProduct.comm A.ρ B.ρ)).monotone (tensorImage_mono B h)

@[simp]
theorem leftTensorImage_bot :
    leftTensorImage B (⊥ : Subrepresentation A.ρ) = ⊥ := by
  rw [← map_tensorImage_comm, tensorImage_bot]
  exact (JordanHolderTransportProof.subrepOrderIso
    (Representation.TensorProduct.comm A.ρ B.ρ)).map_bot

@[simp]
theorem leftTensorImage_top :
    leftTensorImage B (⊤ : Subrepresentation A.ρ) = ⊤ := by
  rw [← map_tensorImage_comm, tensorImage_top]
  exact (JordanHolderTransportProof.subrepOrderIso
    (Representation.TensorProduct.comm A.ρ B.ρ)).map_top

/-- Restrict the ambient commutor to a tensor image and its transported subspace. -/
def commImageEquiv (S : Subrepresentation A.ρ) :
    (tensorImage B S).toRepresentation.Equiv
      (JordanHolderTransportProof.mapSub (Representation.TensorProduct.comm A.ρ B.ρ)
        (tensorImage B S)).toRepresentation :=
  Representation.Equiv.mk
    (JordanHolderTransportProof.upperEquiv
      (Representation.TensorProduct.comm A.ρ B.ρ) (tensorImage B S))
    (by
      intro g
      apply LinearMap.ext
      intro x
      exact Subtype.ext (JordanHolderTransportProof.equiv_apply_rep
        (Representation.TensorProduct.comm A.ρ B.ρ) g x))

@[simp]
theorem commImageEquiv_val (S : Subrepresentation A.ρ)
    (x : (tensorImage B S).toSubmodule) :
    (commImageEquiv B S x).val =
      Representation.TensorProduct.comm A.ρ B.ρ x.val := rfl

@[simp]
theorem commQuotientEquiv_mk (S T : Subrepresentation A.ρ)
    (x : (tensorImage B T).toSubmodule) :
    JordanHolderTransportProof.quotientEquiv
        (Representation.TensorProduct.comm A.ρ B.ρ) (tensorImage B S) (tensorImage B T)
        ((lower (tensorImage B S) (tensorImage B T)).mkQ x) =
      (lower
        (JordanHolderTransportProof.mapSub (Representation.TensorProduct.comm A.ρ B.ρ)
          (tensorImage B S))
        (JordanHolderTransportProof.mapSub (Representation.TensorProduct.comm A.ρ B.ρ)
          (tensorImage B T))).mkQ (commImageEquiv B T x) := rfl

end TensorFiltration

namespace ObjectRepFiltration

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {A : Rep.{uA} k G} {n : ℕ}

/-- Tensor every actual step on the right, retaining its image in the tensor product. -/
def tensorRight (s : ObjectRepFiltration A n) (B : Rep.{uB} k G) :
    ObjectRepFiltration (Rep.of (Representation.tprod A.ρ B.ρ)) n :=
  ofSubrepresentations (fun i => TensorFiltration.tensorImage B (s.subrepresentation i))
    ((TensorFiltration.tensorImage_mono B).comp s.monotone_subrepresentation)
    (by simp) (by simp)

@[simp]
theorem tensorRight_subrepresentation (s : ObjectRepFiltration A n)
    (B : Rep.{uB} k G) (i : Fin (n + 1)) :
    (s.tensorRight B).subrepresentation i =
      TensorFiltration.tensorImage B (s.subrepresentation i) := rfl

/-- The actual graded quotient of the right tensor filtration. -/
def tensorRightGradedEquiv (s : ObjectRepFiltration A n)
    (B : Rep.{uB} k G) (i : Fin n) :
    ((s.tensorRight B).gradedRepresentation i).ρ.Equiv
      (Representation.tprod (s.gradedRepresentation i).ρ B.ρ) :=
  TensorFiltration.quotientTensorEquiv B
    (s.monotone_subrepresentation (Nat.le_succ i.val))

@[simp]
theorem tensorRightGradedEquiv_projection_tmul (s : ObjectRepFiltration A n)
    (B : Rep.{uB} k G) (i : Fin n)
    (x : (s.subrepresentation i.succ).toSubmodule) (b : B) :
    s.tensorRightGradedEquiv B i
        (((s.tensorRight B).gradedProjection i).hom
          (TensorFiltration.tensorImageEquiv B (s.subrepresentation i.succ)
            (x ⊗ₜ[k] b))) =
      (s.gradedProjection i).hom x ⊗ₜ[k] b :=
  TensorFiltration.quotientTensorEquiv_mk_tmul B _ x b

/-- Tensor on the left by transporting the right tensor images through the commutor. -/
def tensorLeft (s : ObjectRepFiltration A n) (B : Rep.{uB} k G) :
    ObjectRepFiltration (Rep.of (Representation.tprod B.ρ A.ρ)) n :=
  let e := JordanHolderTransportProof.subrepOrderIso
    (Representation.TensorProduct.comm A.ρ B.ρ)
  ofSubrepresentations (fun i => e ((s.tensorRight B).subrepresentation i))
    (e.monotone.comp (s.tensorRight B).monotone_subrepresentation)
    (by rw [(s.tensorRight B).subrepresentation_zero]; exact e.map_bot)
    (by rw [(s.tensorRight B).subrepresentation_last]; exact e.map_top)

@[simp]
theorem tensorLeft_subrepresentation (s : ObjectRepFiltration A n)
    (B : Rep.{uB} k G) (i : Fin (n + 1)) :
    (s.tensorLeft B).subrepresentation i =
      TensorFiltration.leftTensorImage B (s.subrepresentation i) :=
  TensorFiltration.map_tensorImage_comm B (s.subrepresentation i)

/-- The tensor of an upper step is equivalent to the actual left tensor image step. -/
def tensorLeftStepEquiv (s : ObjectRepFiltration A n)
    (B : Rep.{uB} k G) (i : Fin (n + 1)) :
    (Representation.tprod B.ρ (s.subrepresentation i).toRepresentation).Equiv
      ((s.tensorLeft B).subrepresentation i).toRepresentation :=
  (Representation.TensorProduct.comm B.ρ (s.subrepresentation i).toRepresentation).trans
    ((TensorFiltration.tensorImageEquiv B (s.subrepresentation i)).trans
      (TensorFiltration.commImageEquiv B (s.subrepresentation i)))

@[simp]
theorem tensorLeftStepEquiv_tmul_val (s : ObjectRepFiltration A n)
    (B : Rep.{uB} k G) (i : Fin (n + 1))
    (b : B) (x : (s.subrepresentation i).toSubmodule) :
    (s.tensorLeftStepEquiv B i (b ⊗ₜ[k] x)).val = b ⊗ₜ[k] (x : A) := rfl

/-- The actual graded equivalence for a left tensor filtration. -/
def tensorLeftGradedEquiv (s : ObjectRepFiltration A n)
    (B : Rep.{uB} k G) (i : Fin n) :
    ((s.tensorLeft B).gradedRepresentation i).ρ.Equiv
      (Representation.tprod B.ρ (s.gradedRepresentation i).ρ) :=
  (JordanHolderTransportProof.quotientEquiv
    (Representation.TensorProduct.comm A.ρ B.ρ)
    (TensorFiltration.tensorImage B (s.subrepresentation i.castSucc))
    (TensorFiltration.tensorImage B (s.subrepresentation i.succ))).symm.trans
      ((s.tensorRightGradedEquiv B i).trans
        (Representation.TensorProduct.comm (s.gradedRepresentation i).ρ B.ρ))

@[simp]
theorem tensorLeftGradedEquiv_projection_tmul (s : ObjectRepFiltration A n)
    (B : Rep.{uB} k G) (i : Fin n)
    (b : B) (x : (s.subrepresentation i.succ).toSubmodule) :
    s.tensorLeftGradedEquiv B i
        (((s.tensorLeft B).gradedProjection i).hom
          (s.tensorLeftStepEquiv B i.succ (b ⊗ₜ[k] x))) =
      b ⊗ₜ[k] (s.gradedProjection i).hom x := by
  let e := JordanHolderTransportProof.quotientEquiv
    (Representation.TensorProduct.comm A.ρ B.ρ)
    (TensorFiltration.tensorImage B (s.subrepresentation i.castSucc))
    (TensorFiltration.tensorImage B (s.subrepresentation i.succ))
  have h :
      ((s.tensorLeft B).gradedProjection i).hom
          (s.tensorLeftStepEquiv B i.succ (b ⊗ₜ[k] x)) =
        e (((s.tensorRight B).gradedProjection i).hom
          (TensorFiltration.tensorImageEquiv B (s.subrepresentation i.succ)
            (x ⊗ₜ[k] b))) :=
    (TensorFiltration.commQuotientEquiv_mk B
      (s.subrepresentation i.castSucc) (s.subrepresentation i.succ)
      (TensorFiltration.tensorImageEquiv B (s.subrepresentation i.succ)
        (x ⊗ₜ[k] b))).symm
  rw [h]
  change Representation.TensorProduct.comm (s.gradedRepresentation i).ρ B.ρ
    (s.tensorRightGradedEquiv B i (e.symm (e _))) = _
  erw [Representation.Equiv.symm_apply_apply, tensorRightGradedEquiv_projection_tmul]
  rfl

end ObjectRepFiltration

end Langlands
