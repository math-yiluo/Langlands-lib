import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Norm.Basic
import Langlands.TauCeti.Algebra.Coalgebra.Convolution

/-! # Points of a finite commutative cocommutative Hopf algebra are killed by its rank -/

noncomputable section

open Coalgebra TensorProduct WithConv

namespace Langlands.FiniteHopfConvolutionPower

section Precomp

variable {R M N C : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Coalgebra R M]
  [AddCommGroup N] [Module R N] [Coalgebra R N] [CommRing C] [Algebra R C]

/-- Precomposition with a coalgebra morphism as a ring morphism of convolution rings. -/
def precomp (h : M →ₗc[R] N) : WithConv (N →ₗ[R] C) →+* WithConv (M →ₗ[R] C) where
  toFun f := toConv (f.ofConv ∘ₗ h.toLinearMap)
  map_one' := by
    apply WithConv.ext
    simp only [LinearMap.convOne_def, ofConv_toConv, LinearMap.comp_assoc]
    rw [h.counit_comp]
  map_mul' f g := WithConv.ext (LinearMap.convMul_comp_coalgHom_distrib f g h)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma precomp_apply (h : M →ₗc[R] N) (f : WithConv (N →ₗ[R] C)) (m : M) :
    precomp h f m = f (h m) := rfl

end Precomp

variable (k H : Type*) [Field k] [CommRing H] [HopfAlgebra k H]

/-- The coalgebra morphism `a ⊗ b ↦ ε(a) b`. -/
def sndCoalgHom : H ⊗[k] H →ₗc[k] H :=
  (Coalgebra.TensorProduct.lid k H : k ⊗[k] H →ₗc[k] H).comp
    (CoalgHom.rTensor H (counitCoalgHom k H))

/-- The coalgebra morphism `a ⊗ b ↦ ε(b) a`. -/
def fstCoalgHom : H ⊗[k] H →ₗc[k] H :=
  (Coalgebra.TensorProduct.rid k k H : H ⊗[k] k →ₗc[k] H).comp
    (CoalgHom.lTensor H (counitCoalgHom k H))

variable {k H} in
@[simp]
lemma sndCoalgHom_tmul (a b : H) : sndCoalgHom k H (a ⊗ₜ b) = counit (R := k) a • b := rfl

variable {k H} in
@[simp]
lemma fstCoalgHom_tmul (a b : H) : fstCoalgHom k H (a ⊗ₜ b) = counit (R := k) b • a := rfl

variable [IsCocomm k H]

/-- The shear coalgebra morphism `a ⊗ b ↦ ∑ a b₍₁₎ ⊗ b₍₂₎`. -/
def shearCoalgHom : H ⊗[k] H →ₗc[k] H ⊗[k] H :=
  (CoalgHom.rTensor H (Bialgebra.mulCoalgHom k H)).comp
    (((Coalgebra.TensorProduct.assoc k k H H H).symm : H ⊗[k] (H ⊗[k] H) →ₗc[k] _).comp
      (CoalgHom.lTensor H (Coalgebra.comulCoalgHom k H)))

/-- The shear map as an algebra morphism: `a ⊗ b ↦ (a ⊗ 1) Δ(b)`. -/
def shearAlgHom : H ⊗[k] H →ₐ[k] H ⊗[k] H :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (Bialgebra.comulAlgHom k H)
    (fun _ _ => Commute.all _ _)

lemma shearCoalgHom_toLinearMap :
    (shearCoalgHom k H : H ⊗[k] H →ₗ[k] H ⊗[k] H) = (shearAlgHom k H).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  change (Bialgebra.mulCoalgHom k H : H ⊗[k] H →ₗ[k] H).rTensor H
      ((TensorProduct.assoc k H H H).symm (a ⊗ₜ comul b)) =
    (a ⊗ₜ (1 : H)) * Bialgebra.comulAlgHom k H b
  rw [Bialgebra.comulAlgHom_apply]
  induction comul (R := k) b with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [tmul_add, map_add, mul_add, hx, hy]

lemma shearCoalgHom_apply (t : H ⊗[k] H) : shearCoalgHom k H t = shearAlgHom k H t :=
  LinearMap.congr_fun (shearCoalgHom_toLinearMap k H) t

omit [IsCocomm k H] in
lemma sndCoalgHom_includeLeft_mul (a : H) (t : H ⊗[k] H) :
    sndCoalgHom k H ((a ⊗ₜ (1 : H)) * t) = counit (R := k) a • sndCoalgHom k H t := by
  induction t with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, Bialgebra.counit_mul, mul_smul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy, smul_add]

omit [IsCocomm k H] in
lemma fstCoalgHom_includeLeft_mul (a : H) (t : H ⊗[k] H) :
    fstCoalgHom k H ((a ⊗ₜ (1 : H)) * t) = a * fstCoalgHom k H t := by
  induction t with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

omit [IsCocomm k H] in
lemma sndCoalgHom_comul (b : H) : sndCoalgHom k H (comul (R := k) b) = b := by
  have h := Coalgebra.rTensor_counit_comul (R := k) b
  change (Coalgebra.TensorProduct.lid k H : k ⊗[k] H →ₗc[k] H)
    ((counit (R := k) : H →ₗ[k] k).rTensor H (comul b)) = b
  rw [h]
  simp

omit [IsCocomm k H] in
lemma fstCoalgHom_comul (b : H) : fstCoalgHom k H (comul (R := k) b) = b := by
  have h := Coalgebra.lTensor_counit_comul (R := k) b
  change (Coalgebra.TensorProduct.rid k k H : H ⊗[k] k →ₗc[k] H)
    ((counit (R := k) : H →ₗ[k] k).lTensor H (comul b)) = b
  rw [h]
  simp

lemma sndCoalgHom_shear (t : H ⊗[k] H) :
    sndCoalgHom k H (shearCoalgHom k H t) = sndCoalgHom k H t := by
  rw [shearCoalgHom_apply]
  induction t with
  | tmul a b =>
    simp [shearAlgHom, sndCoalgHom_includeLeft_mul, sndCoalgHom_comul]
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

lemma fstCoalgHom_shear (a b : H) :
    fstCoalgHom k H (shearCoalgHom k H (a ⊗ₜ b)) = a * b := by
  rw [shearCoalgHom_apply]
  simp [shearAlgHom, fstCoalgHom_includeLeft_mul, fstCoalgHom_comul]

section Points

variable {k H} {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- Postcomposition with an algebra morphism, as a morphism of convolution monoids of points. -/
def postcomp (F : A →ₐ[k] B) : WithConv (H →ₐ[k] A) →* WithConv (H →ₐ[k] B) where
  toFun f := toConv (F.comp f.ofConv)
  map_one' := WithConv.ext (AlgHom.ext fun _ => F.commutes _)
  map_mul' f g := WithConv.ofConv_injective (AlgHom.comp_convMul_distrib F f g)

omit [IsCocomm k H] in
lemma postcomp_toConv (F : A →ₐ[k] B) (f : H →ₐ[k] A) :
    postcomp F (toConv f) = toConv (F.comp f) := rfl

end Points

omit [IsCocomm k H] in
lemma postcomp_inv (F : H ⊗[k] H →ₐ[k] H ⊗[k] H) (f : WithConv (H →ₐ[k] H ⊗[k] H)) :
    postcomp F f⁻¹ = (postcomp F f)⁻¹ := rfl

/-- The inverse shear `a ⊗ b ↦ (a ⊗ 1) ∑ S(b₍₁₎) ⊗ b₍₂₎`, defined through the convolution group
of points of `H` with values in `H ⊗ H`. -/
def shearInvAlgHom : H ⊗[k] H →ₐ[k] H ⊗[k] H :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    ((toConv (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H))⁻¹ *
      toConv (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H)).ofConv
    (fun _ _ => Commute.all _ _)

omit [IsCocomm k H] in
lemma shearAlgHom_comp_shearInvAlgHom :
    (shearAlgHom k H).comp (shearInvAlgHom k H) = AlgHom.id k (H ⊗[k] H) := by
  apply Algebra.TensorProduct.ext
  · rw [AlgHom.comp_assoc, shearInvAlgHom, Algebra.TensorProduct.lift_comp_includeLeft,
      shearAlgHom, Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.id_comp]
  · change (shearAlgHom k H).comp ((shearInvAlgHom k H).comp
      Algebra.TensorProduct.includeRight) = Algebra.TensorProduct.includeRight
    rw [shearInvAlgHom, Algebra.TensorProduct.lift_comp_includeRight']
    apply WithConv.toConv_injective
    change postcomp (shearAlgHom k H)
      ((toConv (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H))⁻¹ *
        toConv (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H)) = _
    rw [map_mul, postcomp_inv, postcomp_toConv, postcomp_toConv, shearAlgHom,
      Algebra.TensorProduct.lift_comp_includeLeft, Algebra.TensorProduct.lift_comp_includeRight',
      TauCeti.Bialgebra.comulPoint_eq_include_mul]
    exact inv_mul_cancel_left (G := WithConv (H →ₐ[k] H ⊗[k] H)) _ _

omit [IsCocomm k H] in
lemma shearInvAlgHom_comp_shearAlgHom :
    (shearInvAlgHom k H).comp (shearAlgHom k H) = AlgHom.id k (H ⊗[k] H) := by
  apply Algebra.TensorProduct.ext
  · rw [AlgHom.comp_assoc, shearAlgHom, Algebra.TensorProduct.lift_comp_includeLeft,
      shearInvAlgHom, Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.id_comp]
  · change (shearInvAlgHom k H).comp ((shearAlgHom k H).comp
      Algebra.TensorProduct.includeRight) = Algebra.TensorProduct.includeRight
    rw [shearAlgHom, Algebra.TensorProduct.lift_comp_includeRight']
    apply WithConv.toConv_injective
    change postcomp (shearInvAlgHom k H) (toConv (Bialgebra.comulAlgHom k H)) = _
    rw [TauCeti.Bialgebra.comulPoint_eq_include_mul, map_mul, postcomp_toConv, postcomp_toConv,
      shearInvAlgHom, Algebra.TensorProduct.lift_comp_includeLeft,
      Algebra.TensorProduct.lift_comp_includeRight', WithConv.toConv_ofConv]
    exact mul_inv_cancel_left (G := WithConv (H →ₐ[k] H ⊗[k] H)) _ _

section Rank

variable {k H} (C : Type*) [CommRing C] [Algebra k C]

/-- Precomposition with the shear, as a ring automorphism of the convolution ring of
`H ⊗ H`. -/
def shearRingEquiv : WithConv (H ⊗[k] H →ₗ[k] C) ≃+* WithConv (H ⊗[k] H →ₗ[k] C) where
  __ := precomp (C := C) (shearCoalgHom k H)
  invFun φ := toConv (φ.ofConv ∘ₗ (shearInvAlgHom k H).toLinearMap)
  left_inv φ := by
    apply WithConv.ext
    change (φ.ofConv ∘ₗ (shearCoalgHom k H).toLinearMap) ∘ₗ (shearInvAlgHom k H).toLinearMap =
      φ.ofConv
    rw [CoalgHom.toLinearMap_eq_ofClass, shearCoalgHom_toLinearMap, LinearMap.comp_assoc,
      ← AlgHom.comp_toLinearMap, shearAlgHom_comp_shearInvAlgHom]
    rfl
  right_inv φ := by
    apply WithConv.ext
    change (φ.ofConv ∘ₗ (shearInvAlgHom k H).toLinearMap) ∘ₗ (shearCoalgHom k H).toLinearMap =
      φ.ofConv
    rw [CoalgHom.toLinearMap_eq_ofClass, shearCoalgHom_toLinearMap, LinearMap.comp_assoc,
      ← AlgHom.comp_toLinearMap, shearInvAlgHom_comp_shearAlgHom]
    rfl

/-- The convolution ring of `H ⊗ H` as an algebra over the convolution ring of `H`, through
precomposition with `a ⊗ b ↦ ε(a) b`. -/
abbrev sndAlgebra : Algebra (WithConv (H →ₗ[k] C)) (WithConv (H ⊗[k] H →ₗ[k] C)) :=
  (precomp (sndCoalgHom k H)).toAlgebra

attribute [local instance] sndAlgebra

omit [IsCocomm k H] in
lemma precomp_snd_mul_apply_tmul (ψ : WithConv (H →ₗ[k] C))
    (φ : WithConv (H ⊗[k] H →ₗ[k] C)) (a b : H) :
    (precomp (sndCoalgHom k H) ψ * φ) (a ⊗ₜ b) =
      (ψ * toConv (φ.ofConv ∘ₗ TensorProduct.mk k H H a)) b := by
  rw [((ℛ k a).tmul (ℛ k b)).convMul_apply, (ℛ k b).convMul_apply]
  conv_rhs => rw [← Coalgebra.sum_counit_smul (ℛ k a)]
  simp only [Coalgebra.Repr.tmul_index, Coalgebra.Repr.tmul_left, Coalgebra.Repr.tmul_right,
    Finset.sum_product, precomp_apply, sndCoalgHom_tmul, map_smul, smul_mul_assoc,
    LinearMap.comp_apply, TensorProduct.mk_apply, map_sum, Finset.mul_sum,
    mul_smul_comm, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm

/-- Coordinates of the convolution ring of `H ⊗ H` over the convolution ring of `H`, taken in a
basis of the first tensor leg. -/
def coordEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι k H) :
    WithConv (H ⊗[k] H →ₗ[k] C) ≃ₗ[WithConv (H →ₗ[k] C)] (ι → WithConv (H →ₗ[k] C)) where
  toFun φ i := toConv (φ.ofConv ∘ₗ TensorProduct.mk k H H (e i))
  invFun v := toConv (TensorProduct.lift (e.constr k fun i => (v i).ofConv))
  map_add' φ φ' := by
    funext i
    apply WithConv.ext
    ext b
    simp
  map_smul' ψ φ := by
    funext i
    apply WithConv.ext
    ext b
    exact precomp_snd_mul_apply_tmul C ψ φ (e i) b
  left_inv φ := by
    have h : e.constr k (fun i => φ.ofConv ∘ₗ TensorProduct.mk k H H (e i)) =
        (TensorProduct.mk k H H).compr₂ φ.ofConv :=
      e.ext fun i => by rw [Module.Basis.constr_basis]; rfl
    apply WithConv.ext
    change TensorProduct.lift (e.constr k fun i => φ.ofConv ∘ₗ TensorProduct.mk k H H (e i)) =
      φ.ofConv
    rw [h, TensorProduct.lift_mk_compr₂]
  right_inv v := by
    funext i
    apply WithConv.ext
    ext b
    simp

/-- Precomposition with the shear, as an automorphism of the convolution algebra of `H ⊗ H`
over the convolution ring of `H`. -/
def shearAlgEquiv :
    WithConv (H ⊗[k] H →ₗ[k] C) ≃ₐ[WithConv (H →ₗ[k] C)] WithConv (H ⊗[k] H →ₗ[k] C) :=
  AlgEquiv.ofRingEquiv (f := shearRingEquiv C) fun ψ => by
    apply WithConv.ext
    refine LinearMap.ext fun t => ?_
    change ψ (sndCoalgHom k H (shearCoalgHom k H t)) = ψ (sndCoalgHom k H t)
    rw [sndCoalgHom_shear]

/-- **Points of a finite cocommutative Hopf algebra are killed by its rank.** For a finite
dimensional commutative and cocommutative Hopf algebra `H` over a field `k` and an algebra map
`x : H → C` to a commutative `k`-algebra, the `finrank k H`-th convolution power of `x` is the
counit point. -/
theorem convPow_finrank_eq_one [Module.Finite k H] (x : H →ₐ[k] C) :
    toConv x.toLinearMap ^ Module.finrank k H = 1 := by
  set X : WithConv (H →ₗ[k] C) := toConv x.toLinearMap with hXdef
  set z : WithConv (H ⊗[k] H →ₗ[k] C) := precomp (fstCoalgHom k H) X with hzdef
  have hXinv : X * toConv (x.toLinearMap ∘ₗ HopfAlgebra.antipode k) = 1 := by
    have h := LinearMap.algHom_comp_convMul_distrib x (toConv LinearMap.id)
      (toConv (HopfAlgebra.antipode k (A := H)))
    rw [LinearMap.id_mul_antipode] at h
    simp only [LinearMap.comp_id] at h
    apply WithConv.ext
    rw [hXdef, ← h]
    ext c
    simp
  have hz : IsUnit z := (IsUnit.of_mul_eq_one _ hXinv).map _
  have hsnd : precomp (sndCoalgHom k H) X = mulTensor 1 X :=
    WithConv.ext (TensorProduct.ext' fun a b => by simp [hXdef, Algebra.smul_def])
  have hfst : z = mulTensor X 1 :=
    WithConv.ext (TensorProduct.ext' fun a b => by
      simp [hzdef, hXdef, Algebra.smul_def, Algebra.commutes])
  have hR : algebraMap _ _ X * z = mulTensor X X := by
    rw [RingHom.algebraMap_toAlgebra, hsnd, hfst, mulTensor_convMul, one_mul, mul_one]
  have hτ : shearAlgEquiv C z = algebraMap _ _ X * z := by
    rw [hR]
    apply WithConv.ext
    refine TensorProduct.ext' fun a b => ?_
    change X (fstCoalgHom k H (shearCoalgHom k H (a ⊗ₜ b))) = _
    rw [fstCoalgHom_shear, mulTensor_apply_tmul]
    exact map_mul x a b
  let b := Module.Basis.ofEquivFun (coordEquiv C (Module.finBasis k H))
  have h1 := Algebra.norm_eq_of_algEquiv (shearAlgEquiv C) z
  rw [hτ, map_mul, Algebra.norm_algebraMap_of_basis b, Fintype.card_fin] at h1
  exact (hz.map (Algebra.norm (WithConv (H →ₗ[k] C)))).mul_eq_right.mp h1

/-- The algebra-hom form of `convPow_finrank_eq_one`, in the convolution monoid of points. -/
theorem pow_finrank_eq_one [Module.Finite k H] (x : WithConv (H →ₐ[k] C)) :
    x ^ Module.finrank k H = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convPow, convPow_finrank_eq_one C x.ofConv]
  rfl

end Rank

end Langlands.FiniteHopfConvolutionPower
