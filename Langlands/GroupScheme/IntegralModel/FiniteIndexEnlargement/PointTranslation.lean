import Mathlib.RingTheory.Bialgebra.Convolution

/-! # Translation of coordinates by integral points of a bialgebra

For a commutative bialgebra `C` over `R` and an `R`-point `f : C →ₐ[R] R`, the right translation
by `f` is the algebra endomorphism `c ↦ ∑ f (c₂) c₁` of `C`, where `∑ c₁ ⊗ c₂` is the
comultiplication of `c`. Composing an algebra map `y` with the translation by `f` gives the
convolution product `y * f`; translations compose according to the convolution product; and
translation by the counit is the identity. Consequently a group homomorphism into the
convolution monoid of `R`-points gives algebra automorphisms of `C`. -/

noncomputable section

open TensorProduct WithConv

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

section PointTrans

variable {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Bialgebra R C]

/-- Right translation by an `R`-point `f` of a bialgebra: `c ↦ ∑ f (c₂) c₁`. -/
def pointTrans (f : C →ₐ[R] R) : C →ₐ[R] C :=
  (Algebra.TensorProduct.rid R R C).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id R C) f).comp (Bialgebra.comulAlgHom R C))

theorem algebraRid_apply (x : C ⊗[R] R) :
    Algebra.TensorProduct.rid R R C x = TensorProduct.rid R C x := by
  induction x using TensorProduct.inductionOn with
  | tmul c r => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem pointTrans_apply (f : C →ₐ[R] R) (c : C) :
    pointTrans f c =
      TensorProduct.rid R C (LinearMap.lTensor C f.toLinearMap (Coalgebra.comul c)) := by
  change Algebra.TensorProduct.rid R R C
    (Algebra.TensorProduct.map (AlgHom.id R C) f (Coalgebra.comul c)) = _
  rw [algebraRid_apply]
  rfl

theorem pointTrans_toLinearMap (f : C →ₐ[R] R) :
    (pointTrans f).toLinearMap =
      (TensorProduct.rid R C).toLinearMap ∘ₗ LinearMap.lTensor C f.toLinearMap ∘ₗ
        Coalgebra.comul :=
  LinearMap.ext fun c => pointTrans_apply f c

/-- Translation by the unit of the convolution monoid is the identity. -/
theorem pointTrans_one : pointTrans (1 : WithConv (C →ₐ[R] R)).ofConv = AlgHom.id R C := by
  apply AlgHom.ext
  intro c
  have h1 : (1 : WithConv (C →ₐ[R] R)).ofConv.toLinearMap = Coalgebra.counit := by
    apply LinearMap.ext
    intro a
    change (1 : WithConv (C →ₐ[R] R)) a = Coalgebra.counit a
    rw [AlgHom.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [pointTrans_apply, h1, Coalgebra.lTensor_counit_comul]
  simp

/-- Evaluating a translate is a convolution product. -/
theorem comp_pointTrans {S : Type*} [CommRing S] [Algebra R S] (y : C →ₐ[R] S)
    (f : C →ₐ[R] R) :
    y.comp (pointTrans f) = (toConv y * toConv ((Algebra.ofId R S).comp f)).ofConv := by
  apply AlgHom.ext
  intro c
  rw [AlgHom.comp_apply, pointTrans_apply, AlgHom.convMul_apply]
  generalize Coalgebra.comul (R := R) c = w
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
    simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem pointTrans_pointTrans_apply (f g : C →ₐ[R] R) (c : C) :
    pointTrans f (pointTrans g c) = pointTrans (toConv f * toConv g).ofConv c := by
  have stepA : ∀ w : C ⊗[R] C,
      Coalgebra.comul (R := R) (TensorProduct.rid R C (LinearMap.lTensor C g.toLinearMap w)) =
        TensorProduct.rid R (C ⊗[R] C) (LinearMap.lTensor (C ⊗[R] C) g.toLinearMap
          (LinearMap.rTensor C Coalgebra.comul w)) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have stepB : ∀ v : (C ⊗[R] C) ⊗[R] C,
      TensorProduct.rid R C (LinearMap.lTensor C f.toLinearMap
          (TensorProduct.rid R (C ⊗[R] C) (LinearMap.lTensor (C ⊗[R] C) g.toLinearMap v))) =
        TensorProduct.rid R C (LinearMap.lTensor C
          (LinearMap.mul' R R ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap)
            (TensorProduct.assoc R C C C v)) := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul p d =>
      induction p using TensorProduct.inductionOn with
      | tmul a b => simp [smul_smul, mul_comm]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hfg : (toConv f * toConv g).ofConv.toLinearMap =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ
        Coalgebra.comul := by
    apply LinearMap.ext
    intro a
    rw [AlgHom.convMul_def]
    simp only [AlgHom.toLinearMap_apply, AlgHom.coe_comp, Function.comp_apply,
      Bialgebra.comulAlgHom_apply, LinearMap.coe_comp]
    rw [← Algebra.TensorProduct.lmul'_toLinearMap]
    rfl
  rw [pointTrans_apply, pointTrans_apply, stepA, stepB, pointTrans_apply, hfg,
    LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.coassoc_apply]
  simp only [LinearMap.lTensor_comp, LinearMap.comp_apply]

/-- Translations compose according to the convolution product. -/
theorem pointTrans_comp (f g : C →ₐ[R] R) :
    (pointTrans f).comp (pointTrans g) = pointTrans (toConv f * toConv g).ofConv :=
  AlgHom.ext fun c => pointTrans_pointTrans_apply f g c

/-- Translations are natural along bialgebra homomorphisms. -/
theorem map_pointTrans {D : Type*} [CommRing D] [Bialgebra R D] (φ : C →ₐc[R] D)
    (f : D →ₐ[R] R) (c : C) :
    φ (pointTrans (f.comp (φ : C →ₐ[R] D)) c) = pointTrans f (φ c) := by
  rw [pointTrans_apply, pointTrans_apply, ← CoalgHomClass.map_comp_comul_apply φ c]
  generalize Coalgebra.comul (R := R) c = w
  induction w using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

variable {Γ : Type*} [Group Γ] (σ : Γ →* WithConv (C →ₐ[R] R))

/-- The algebra automorphism of `C` given by translation by `σ z`, for a group homomorphism
`σ` into the convolution monoid of `R`-points. -/
def transEquiv (z : Γ) : C ≃ₐ[R] C :=
  AlgEquiv.ofAlgHom (pointTrans (σ z).ofConv) (pointTrans (σ z⁻¹).ofConv)
    (by rw [pointTrans_comp, toConv_ofConv, toConv_ofConv, ← map_mul, mul_inv_cancel, map_one,
      pointTrans_one])
    (by rw [pointTrans_comp, toConv_ofConv, toConv_ofConv, ← map_mul, inv_mul_cancel, map_one,
      pointTrans_one])

theorem transEquiv_apply (z : Γ) (c : C) : transEquiv σ z c = pointTrans (σ z).ofConv c :=
  rfl

end PointTrans

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
