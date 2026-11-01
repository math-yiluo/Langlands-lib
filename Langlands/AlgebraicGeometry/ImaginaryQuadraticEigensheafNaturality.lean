import Langlands.AlgebraicGeometry.ImaginaryQuadraticEigensheaf

/-! # Naturality of the actual imaginary quadratic eigensheaf splitting -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField Algebra
open Langlands.Shimura.ImaginaryQuadratic
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

namespace Langlands.Scheme.Modules

variable (L : Type u) [Field L] [NumberField L] [IsCMField L]
  (K : Type v) [Field K] [CharZero K] [Algebra L K]
  [IsQuadraticExtension ℚ L]
  {S : AlgebraicGeometry.Scheme.{w}}
  [Algebra K Γ(S, ⊤)] [Algebra ℚ Γ(S, ⊤)] [IsScalarTower ℚ K Γ(S, ⊤)]
  {M N : S.Modules} (ρ : L →+* End M) (τ : L →+* End N)
  (f : M ⟶ N) (hf : ∀ t : L, ρ t ≫ f = f ≫ τ t)

omit [IsCMField L] [IsQuadraticExtension ℚ L] in
include hf in
/-- An actual field-action intertwiner also intertwines the constructed global tensor action. -/
theorem sheafTensorAction_naturality (a : Γ(S, ⊤) ⊗[ℚ] L) :
    sheafTensorAction L M ρ a ≫ f = f ≫ sheafTensorAction L N τ a := by
  induction a using TensorProduct.inductionOn with
  | tmul r t =>
    rw [sheafTensorAction_tmul, sheafTensorAction_tmul,
      Linear.smul_comp, Linear.comp_smul, hf t]
  | add a b ha hb =>
    rw [map_add, map_add]
    change ((sheafTensorAction L M ρ a : M ⟶ M) +
      sheafTensorAction L M ρ b) ≫ f =
      f ≫ ((sheafTensorAction L N τ a : N ⟶ N) + sheafTensorAction L N τ b)
    rw [Preadditive.add_comp, Preadditive.comp_add, ha, hb]

include hf in
/-- Field-action intertwiners commute with the actual complementary sheaf projectors. -/
theorem sheafProjector_naturality (conjugate : Bool) :
    sheafProjector L K M ρ conjugate ≫ f =
      f ≫ sheafProjector L K N τ conjugate :=
  sheafTensorAction_naturality L ρ τ f hf _

/-- The actual eigenprojections commute with an equivariant sheaf map and its restriction. -/
theorem sheafEigenProjection_naturality (conjugate : Bool) :
    f ≫ sheafEigenProjection L K N τ conjugate =
      sheafEigenProjection L K M ρ conjugate ≫
        scalarEigensheafMap (S := S) (R := L) (M := M) (N := N) (ρ := ρ) (χ := sheafFactorCharacter L K conjugate) τ f hf := by
  apply (cancel_mono (scalarEigensheafι τ (sheafFactorCharacter L K conjugate))).mp
  rw [Category.assoc, sheafEigenProjection_ι, Category.assoc,
    scalarEigensheafMap_ι, ← Category.assoc, sheafEigenProjection_ι]
  exact (sheafProjector_naturality L K ρ τ f hf conjugate).symm

/-- The actual map of the ordered natural and conjugate eigensheaf products. -/
def sheafEigenProductMap :
    scalarEigensheaf ρ (sheafFactorCharacter L K false) ⨯
        scalarEigensheaf ρ (sheafFactorCharacter L K true) ⟶
      scalarEigensheaf τ (sheafFactorCharacter L K false) ⨯
        scalarEigensheaf τ (sheafFactorCharacter L K true) :=
  prod.map
    (scalarEigensheafMap (S := S) (R := L) (M := M) (N := N) (ρ := ρ)
      (χ := sheafFactorCharacter L K false) τ f hf)
    (scalarEigensheafMap (S := S) (R := L) (M := M) (N := N) (ρ := ρ)
      (χ := sheafFactorCharacter L K true) τ f hf)

/-- The constructed product splitting is natural for actual field-action intertwiners. -/
theorem sheafEigenIso_naturality :
    f ≫ (sheafEigenIso L K N τ).hom =
      (sheafEigenIso L K M ρ).hom ≫ sheafEigenProductMap L K ρ τ f hf := by
  apply prod.hom_ext
  · simpa only [sheafEigenIso, sheafEigenProductMap, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc] using
      sheafEigenProjection_naturality L K ρ τ f hf false
  · simpa only [sheafEigenIso, sheafEigenProductMap, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc] using
      sheafEigenProjection_naturality L K ρ τ f hf true

end Langlands.Scheme.Modules
