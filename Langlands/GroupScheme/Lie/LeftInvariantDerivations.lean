import Langlands.GroupScheme.Lie.AffineBracket
import Langlands.GroupScheme.IntegralLinearEmbedding.Comodule
import Mathlib.RingTheory.Derivation.Lie

/-! # The left-invariant derivation model of the affine Lie bracket -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Coalgebra WithConv
open scoped TensorProduct

namespace Langlands.GroupScheme.Lie

open IntegralLinearEmbedding

attribute [local instance 100] LieRing.ofAssociativeRing

section Bialgebra

variable {R B : Type*} [CommRing R] [CommRing B] [Bialgebra R B]

local notation "C" => WithConv (Module.Dual R B)
local notation "Δ" => (comul (R := R) : B →ₗ[R] B ⊗[R] B)
local notation "ε" => (counit (R := R) : B →ₗ[R] R)
local notation "D₀" => counitDerivationLie R B R

private abbrev contract (f : Module.Dual R B) : B ⊗[R] B →ₗ[R] B :=
  (TensorProduct.rid R B).toLinearMap ∘ₗ f.lTensor B

private theorem contract_tmul (f : Module.Dual R B) (x y : B) :
    contract f (x ⊗ₜ[R] y) = f y • x := by
  simp [contract]

private theorem contract_mul (f : C) (hf : IsCounitDerivation f) (x y : B ⊗[R] B) :
    contract f.ofConv (x * y) =
      contract ε x * contract f.ofConv y + contract f.ofConv x * contract ε y := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | tmul c d =>
      have h : f (b * d) = f b * ε d + ε b * f d := by simpa using hf b d
      rw [Algebra.TensorProduct.tmul_mul_tmul, contract_tmul, h]
      simp only [contract_tmul, Algebra.smul_def, map_add, map_mul]
      ring
    | add x y hx hy =>
      simp only [mul_add, map_add, hx, hy]
      abel
  | add x z hx hz =>
    simp only [add_mul, map_add, hx, hz]
    abel

/-- Extend a counit derivation by contracting the second factor of the coproduct. -/
def extendLeftInvariant (f : D₀) : Derivation R B B :=
  Derivation.mk' (rightAct f.val.ofConv) fun x y => by
    change contract f.val.ofConv (Δ (x * y)) =
      x * contract f.val.ofConv (Δ y) + y * contract f.val.ofConv (Δ x)
    have h : Δ (x * y) = Δ x * Δ y := map_mul (Bialgebra.comulAlgHom R B) x y
    rw [h, contract_mul _ f.property]
    change rightAct ε x * rightAct f.val.ofConv y + rightAct f.val.ofConv x * rightAct ε y = _
    rw [rightAct_counit, rightAct_counit, mul_comm (rightAct f.val.ofConv x)]
    rfl

@[simp] theorem extendLeftInvariant_apply (f : D₀) (b : B) :
    extendLeftInvariant f b = rightAct f.val.ofConv b := rfl

private theorem comp_rightAct (f g : C) :
    f.ofConv ∘ₗ rightAct g.ofConv = (f * g).ofConv := by
  have h : f.ofConv ∘ₗ contract g.ofConv =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f.ofConv g.ofConv := by
    apply TensorProduct.ext'
    intro x y
    simp [mul_comm]
  rw [LinearMap.convMul_def]
  change f.ofConv ∘ₗ (contract g.ofConv ∘ₗ Δ) =
    LinearMap.mul' R R ∘ₗ TensorProduct.map f.ofConv g.ofConv ∘ₗ Δ
  simpa only [LinearMap.comp_assoc] using
    congrArg (fun q : B ⊗[R] B →ₗ[R] R => q ∘ₗ Δ) h

private theorem comp_extend (f g : C) (b : B) :
    rightAct f.ofConv (rightAct g.ofConv b) = rightAct (f * g).ofConv b := by
  rw [rightAct_rightAct, comp_rightAct]

/-- Extension takes the convolution commutator to the commutator of derivations. -/
def extendLeftInvariantLieHom : D₀ →ₗ⁅R⁆ Derivation R B B where
  toFun := extendLeftInvariant
  map_add' f g := by
    ext b
    simp [rightAct_apply, ofConv_add, LinearMap.lTensor_add]
  map_smul' r f := by
    ext b
    simp [rightAct_apply, ofConv_smul, LinearMap.lTensor_smul]
  map_lie' {f g} := by
    ext b
    rw [Derivation.commutator_apply]
    simp only [extendLeftInvariant_apply, comp_extend, counitDerivationLie_coe_lie]
    simp only [rightAct_apply, ofConv_sub, LinearMap.lTensor_sub, LinearMap.sub_apply, map_sub]

/-- Evaluation at the identity recovers the original counit derivation. -/
theorem counit_comp_extendLeftInvariant (f : D₀) :
    ε ∘ₗ (extendLeftInvariant f).toLinearMap = f.val.ofConv := by
  have h : toConv ε = (1 : C) := by
    apply ofConv_injective
    ext b
    change ε b = (1 : C) b
    simp
  change (toConv ε).ofConv ∘ₗ rightAct f.val.ofConv = _
  rw [comp_rightAct, h, one_mul]

private theorem extendLeftInvariantLieHom_injective :
    Function.Injective (extendLeftInvariantLieHom : D₀ →ₗ⁅R⁆ Derivation R B B) := by
  intro f g h
  change extendLeftInvariant f = extendLeftInvariant g at h
  apply Subtype.ext
  apply ofConv_injective
  rw [← counit_comp_extendLeftInvariant, ← counit_comp_extendLeftInvariant, h]

/-- Invariance under left translations, expressed in coproduct coordinates. -/
def IsLeftInvariant (D : Derivation R B B) : Prop :=
  ∀ b, Δ (D b) = D.toLinearMap.lTensor B (Δ b)

private theorem comul_rightAct (f : Module.Dual R B) (b : B) :
    Δ (rightAct f b) = (rightAct f).lTensor B (Δ b) := by
  let α := (TensorProduct.rid R (B ⊗[R] B)).toLinearMap ∘ₗ f.lTensor (B ⊗[R] B)
  have h₁ : Δ ∘ₗ contract f = α ∘ₗ (Δ).rTensor B := by
    apply TensorProduct.ext'
    intro x y
    simp [α]
  have h₂ : α ∘ₗ (TensorProduct.assoc R B B B).symm.toLinearMap = (contract f).lTensor B := by
    apply TensorProduct.ext_threefold'
    intro x y z
    simp [α]
  calc
    _ = (Δ ∘ₗ contract f) (Δ b) := rfl
    _ = α ((Δ).rTensor B (Δ b)) := LinearMap.congr_fun h₁ _
    _ = α ((TensorProduct.assoc R B B B).symm ((Δ).lTensor B (Δ b))) := by rw [coassoc_symm_apply]
    _ = (contract f).lTensor B ((Δ).lTensor B (Δ b)) := LinearMap.congr_fun h₂ _
    _ = _ := by rw [← LinearMap.lTensor_comp_apply]; rfl

private theorem isCounitDerivation_comp_counit (D : Derivation R B B) :
    IsCounitDerivation (toConv (ε ∘ₗ D.toLinearMap)) := by
  intro x y
  simp only [LinearMap.comp_apply, Derivation.coeFn_coe, LinearMap.convOne_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [D.leibniz, smul_eq_mul, smul_eq_mul]
  change Bialgebra.counitAlgHom R B (x * D y + y * D x) =
    Bialgebra.counitAlgHom R B (D x) * Bialgebra.counitAlgHom R B y +
      Bialgebra.counitAlgHom R B x * Bialgebra.counitAlgHom R B (D y)
  rw [map_add, map_mul, map_mul, add_comm, mul_comm (Bialgebra.counitAlgHom R B y)]

variable (R B) in
/-- The Lie subalgebra of the left-invariant derivations of a commutative bialgebra. -/
def leftInvariantDerivations : LieSubalgebra R (Derivation R B B) :=
  extendLeftInvariantLieHom.range

@[simp] theorem mem_leftInvariantDerivations (D : Derivation R B B) :
    D ∈ leftInvariantDerivations R B ↔ IsLeftInvariant D := by
  change D ∈ extendLeftInvariantLieHom.range ↔ _
  rw [LieHom.mem_range]
  constructor
  · rintro ⟨f, rfl⟩ b
    exact comul_rightAct f.val.ofConv b
  · intro h
    refine ⟨⟨toConv (ε ∘ₗ D.toLinearMap), isCounitDerivation_comp_counit D⟩, ?_⟩
    apply Derivation.ext
    intro b
    change rightAct (ε ∘ₗ D.toLinearMap) b = D b
    rw [rightAct_apply, LinearMap.lTensor_comp_apply, ← h b, lTensor_counit_comul,
      TensorProduct.rid_tmul, one_smul]

/-- Counit derivations with convolution bracket are exactly left-invariant derivations. -/
def counitLeftInvariantLieEquiv : D₀ ≃ₗ⁅R⁆ leftInvariantDerivations R B :=
  extendLeftInvariantLieHom.equivRangeOfInjective extendLeftInvariantLieHom_injective

@[simp] theorem counitLeftInvariantLieEquiv_val (f : D₀) :
    (counitLeftInvariantLieEquiv f).val = extendLeftInvariant f := rfl

/-- The inverse comparison is composition with the counit, as a linear map. -/
theorem counitLeftInvariantLieEquiv_symm_ofConv (D : leftInvariantDerivations R B) :
    (counitLeftInvariantLieEquiv.symm D).val.ofConv = ε ∘ₗ D.val.toLinearMap := by
  have h : extendLeftInvariant (counitLeftInvariantLieEquiv.symm D) = D.val :=
    congrArg Subtype.val (counitLeftInvariantLieEquiv.apply_symm_apply D)
  rw [← counit_comp_extendLeftInvariant, h]

end Bialgebra

section GroupScheme

open AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

private local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- At the base ring, the actual tangent Lie algebra is the Lie algebra of
left-invariant derivations of its Hopf coordinate ring. -/
def kernelLeftInvariantLieEquiv : Additive (lieKernel G R) ≃ₗ⁅R⁆
    leftInvariantDerivations R (hopfAlgebra G) :=
  (kernelCounitDerivationLieEquiv G (A := R)).trans counitLeftInvariantLieEquiv

@[simp] theorem kernelLeftInvariantLieEquiv_val (x : Additive (lieKernel G R)) :
    (kernelLeftInvariantLieEquiv G x).val = extendLeftInvariant (kernelCounitDerivationLieEquiv G x) :=
  rfl

end GroupScheme

end Langlands.GroupScheme.Lie
