import Langlands.AlgebraicGeometry.ScalarEigensheaf
import Langlands.Shimura.Unitary.ImaginaryQuadraticProjectors

/-! # Actual imaginary quadratic projectors on module sheaves -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite NumberField Algebra
open Langlands.Scheme.Modules
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
  (M : S.Modules) (ρ : L →+* End M)

/-- Extend the actual field action to the tensor algebra of global regular functions. -/
def sheafTensorAction : Γ(S, ⊤) ⊗[ℚ] L →+* End M := by
  letI := endAlgebra (RingHom.id Γ(S, ⊤)) M
  letI := Algebra.compHom (End M) (algebraMap ℚ Γ(S, ⊤))
  letI : IsScalarTower ℚ Γ(S, ⊤) (End M) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (AlgHom.liftEquiv ℚ Γ(S, ⊤) L (End M) ρ.toRatAlgHom).toRingHom

omit [IsCMField L] [IsQuadraticExtension ℚ L] in
@[simp]
theorem sheafTensorAction_tmul (r : Γ(S, ⊤)) (t : L) :
    sheafTensorAction L M ρ (r ⊗ₜ[ℚ] t) = r • ρ t := rfl

omit [IsCMField L] [IsQuadraticExtension ℚ L] in
/-- The global tensor action is linear for the actual global scalar multiplication. -/
theorem sheafTensorAction_smul (r : Γ(S, ⊤)) (a : Γ(S, ⊤) ⊗[ℚ] L) :
    sheafTensorAction L M ρ (r • a) = r • sheafTensorAction L M ρ a := by
  let := endAlgebra (RingHom.id Γ(S, ⊤)) M
  let := Algebra.compHom (End M) (algebraMap ℚ Γ(S, ⊤))
  let : IsScalarTower ℚ Γ(S, ⊤) (End M) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact map_smul (AlgHom.liftEquiv ℚ Γ(S, ⊤) L (End M) ρ.toRatAlgHom) r a

/-- The actual natural or conjugate global character. -/
def sheafFactorCharacter (conjugate : Bool) : L →+* Γ(S, ⊤) :=
  factorCharacter L K Γ(S, ⊤) conjugate

/-- The actual complementary projector endomorphism of the module sheaf. -/
def sheafProjector (conjugate : Bool) : End M :=
  sheafTensorAction L M ρ (factorIdempotent L K Γ(S, ⊤) conjugate)

/-- The two sheaf projectors are idempotent. -/
theorem sheafProjector_mul_self (conjugate : Bool) :
    sheafProjector L K M ρ conjugate * sheafProjector L K M ρ conjugate =
      sheafProjector L K M ρ conjugate := by
  simpa only [sheafProjector, map_mul] using
    congrArg (sheafTensorAction L M ρ) (factorIdempotent_mul_self L K Γ(S, ⊤) conjugate)

/-- The two sheaf projectors are orthogonal in both orders. -/
theorem sheafProjector_mul_other (conjugate : Bool) :
    sheafProjector L K M ρ conjugate * sheafProjector L K M ρ (!conjugate) = 0 := by
  simpa only [sheafProjector, map_mul, map_zero] using
    congrArg (sheafTensorAction L M ρ) (factorIdempotent_mul_other L K Γ(S, ⊤) conjugate)

/-- The two sheaf projectors sum to the identity. -/
theorem sheafProjector_add_other (conjugate : Bool) :
    sheafProjector L K M ρ conjugate + sheafProjector L K M ρ (!conjugate) = 1 := by
  simpa only [sheafProjector, map_add, map_one] using
    congrArg (sheafTensorAction L M ρ) (factorIdempotent_add_other L K Γ(S, ⊤) conjugate)

/-- The image of the actual projector satisfies every scalar eigen equation on every open. -/
theorem sheafProjector_mem (conjugate : Bool) (U : S.Opens) (x : Γ(M, U)) :
    (sheafProjector L K M ρ conjugate).app U x ∈
      scalarEigenSections ρ (sheafFactorCharacter L K conjugate) U := by
  intro t
  have h := congrArg (fun a => (sheafTensorAction L M ρ a).app U x)
    (tmul_mul_factorIdempotent L K Γ(S, ⊤) conjugate t)
  rw [map_mul, sheafTensorAction_tmul, one_smul, sheafTensorAction_smul] at h
  exact h

/-- Every tensor element acts on an eigensection through its selected scalar evaluation. -/
theorem sheafTensorAction_apply_of_mem (conjugate : Bool) (U : S.Opens)
    {x : Γ(M, U)} (hx : x ∈ scalarEigenSections ρ (sheafFactorCharacter L K conjugate) U)
    (a : Γ(S, ⊤) ⊗[ℚ] L) :
    (sheafTensorAction L M ρ a).app U x =
      restrictScalar U (factorEvaluation L K Γ(S, ⊤) conjugate a) • x := by
  induction a using TensorProduct.inductionOn with
  | tmul r t =>
    rw [sheafTensorAction_tmul, factorEvaluation_tmul, map_mul, mul_smul]
    change restrictScalar U r • (ρ t).app U x = _
    rw [hx t]
    rfl
  | add a b ha hb =>
    rw [map_add, map_add, map_add, add_smul]
    change (sheafTensorAction L M ρ a).app U x +
      (sheafTensorAction L M ρ b).app U x = _
    rw [ha, hb]

/-- An eigensection is fixed by its corresponding actual sheaf projector. -/
theorem sheafProjector_apply_of_mem (conjugate : Bool) (U : S.Opens)
    {x : Γ(M, U)} (hx : x ∈ scalarEigenSections ρ (sheafFactorCharacter L K conjugate) U) :
    (sheafProjector L K M ρ conjugate).app U x = x := by
  rw [sheafProjector, sheafTensorAction_apply_of_mem L K M ρ conjugate U hx]
  cases conjugate <;> simp [factorEvaluation]

/-- An eigensection is killed by the other actual sheaf projector. -/
theorem sheafProjector_other_apply_of_mem (conjugate : Bool) (U : S.Opens)
    {x : Γ(M, U)} (hx : x ∈ scalarEigenSections ρ (sheafFactorCharacter L K conjugate) U) :
    (sheafProjector L K M ρ (!conjugate)).app U x = 0 := by
  rw [sheafProjector, sheafTensorAction_apply_of_mem L K M ρ conjugate U hx]
  cases conjugate <;> simp [factorEvaluation]

/-- The actual projection morphism to the already constructed scalar eigensubsheaf. -/
def sheafEigenProjection (conjugate : Bool) :
    M ⟶ scalarEigensheaf ρ (sheafFactorCharacter L K conjugate) where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => ⟨(sheafProjector L K M ρ conjugate).app U.unop x,
            sheafProjector_mem L K M ρ conjugate U.unop x⟩
          map_add' := fun x y => Subtype.ext (map_add _ x y)
          map_smul' := fun r x =>
            Subtype.ext (Scheme.Modules.Hom.app_smul _ r x) }
      naturality := by
        intro U V j
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply
          (sheafProjector L K M ρ conjugate).val j x }

@[simp]
theorem sheafEigenProjection_app (conjugate : Bool) (U : S.Opens) (x : Γ(M, U)) :
    ((sheafEigenProjection L K M ρ conjugate).app U x).val =
      (sheafProjector L K M ρ conjugate).app U x := rfl

@[simp]
theorem sheafEigenProjection_ι (conjugate : Bool) :
    sheafEigenProjection L K M ρ conjugate ≫
        scalarEigensheafι ρ (sheafFactorCharacter L K conjugate) =
      sheafProjector L K M ρ conjugate := rfl

@[simp]
theorem ι_sheafEigenProjection (conjugate : Bool) :
    scalarEigensheafι ρ (sheafFactorCharacter L K conjugate) ≫
        sheafEigenProjection L K M ρ conjugate = 𝟙 _ := by
  ext U x
  apply Subtype.ext
  exact sheafProjector_apply_of_mem L K M ρ conjugate U x.property

@[simp]
theorem ι_sheafEigenProjection_other (conjugate : Bool) :
    scalarEigensheafι ρ (sheafFactorCharacter L K conjugate) ≫
        sheafEigenProjection L K M ρ (!conjugate) = 0 := by
  ext U x
  apply Subtype.ext
  exact sheafProjector_other_apply_of_mem L K M ρ conjugate U x.property

/-- The actual module sheaf is isomorphic to the product of its two full scalar eigensubsheaves. -/
def sheafEigenIso :
    M ≅ scalarEigensheaf ρ (sheafFactorCharacter L K false) ⨯
      scalarEigensheaf ρ (sheafFactorCharacter L K true) where
  hom := prod.lift (sheafEigenProjection L K M ρ false) (sheafEigenProjection L K M ρ true)
  inv := prod.fst ≫ scalarEigensheafι ρ (sheafFactorCharacter L K false) +
    prod.snd ≫ scalarEigensheafι ρ (sheafFactorCharacter L K true)
  hom_inv_id := by
    simp only [Preadditive.comp_add, ← Category.assoc, prod.lift_fst, prod.lift_snd,
      sheafEigenProjection_ι]
    exact sheafProjector_add_other L K M ρ false
  inv_hom_id := by
    apply prod.hom_ext
    · simp only [Preadditive.add_comp, Category.assoc, prod.lift_fst,
        ι_sheafEigenProjection, Category.comp_id]
      have h : scalarEigensheafι ρ (sheafFactorCharacter L K true) ≫
          sheafEigenProjection L K M ρ false = 0 :=
        ι_sheafEigenProjection_other L K M ρ true
      rw [h, comp_zero, add_zero, Category.id_comp]
    · simp only [Preadditive.add_comp, Category.assoc, prod.lift_snd,
        ι_sheafEigenProjection, Category.comp_id]
      have h : scalarEigensheafι ρ (sheafFactorCharacter L K false) ≫
          sheafEigenProjection L K M ρ true = 0 :=
        ι_sheafEigenProjection_other L K M ρ false
      rw [h, comp_zero, zero_add, Category.id_comp]

end Langlands.Scheme.Modules
