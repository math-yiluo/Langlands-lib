import Langlands.Global.ArchimedeanPlaceLie

/-! # Actual place enveloping algebras as retracts of the global enveloping algebra -/

noncomputable section
universe u

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] (n : ℕ)

/-- The enveloping algebra of the complexified real matrix Lie algebra at a real place. -/
abbrev RealPlaceEnvelopingAlgebra :=
  UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)

/-- The enveloping algebra retains the full underlying real matrix Lie algebra at a complex place. -/
abbrev ComplexPlaceEnvelopingAlgebra :=
  UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)

def realPlaceEnvelopingGenerator :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ RealPlaceEnvelopingAlgebra n :=
  UniversalEnvelopingAlgebra.ι ℂ

def complexPlaceEnvelopingGenerator :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ ComplexPlaceEnvelopingAlgebra n :=
  UniversalEnvelopingAlgebra.ι ℂ


local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- Complex scalar extension of the actual real-place Lie projection. -/
def realPlaceComplexLieProjection (v : RP) :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] RM) :=
  { (realPlaceLieProjection F n v).toLinearMap.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (realPlaceLieProjection F n v)).map_lie X Y }

/-- Complex scalar extension of the full underlying real complex-place projection. -/
def complexPlaceComplexLieProjection (v : CP) :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] CM) :=
  { (complexPlaceLieProjection F n v).toLinearMap.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (complexPlaceLieProjection F n v)).map_lie X Y }

@[simp] theorem realPlaceComplexLieProjection_tmul (v : RP) (z : ℂ)
    (X : RealLieAlgebra F n) :
    realPlaceComplexLieProjection F n v (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] realPlaceLieProjection F n v X := rfl

@[simp] theorem complexPlaceComplexLieProjection_tmul (v : CP) (z : ℂ)
    (X : RealLieAlgebra F n) :
    complexPlaceComplexLieProjection F n v (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] complexPlaceLieProjection F n v X := rfl

@[simp] theorem realPlaceComplexLieProjection_inclusion (v : RP) (X : ℂ ⊗[ℝ] RM) :
    realPlaceComplexLieProjection F n v (realPlaceComplexLieInclusion F n v X) = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [realPlaceComplexLieInclusion_tmul, realPlaceComplexLieProjection_tmul,
      realProjection_realInclusion, Pi.single_eq_same]
  | add X Y hX hY => simp only [map_add, hX, hY]

@[simp] theorem complexPlaceComplexLieProjection_inclusion (v : CP) (X : ℂ ⊗[ℝ] CM) :
    complexPlaceComplexLieProjection F n v (complexPlaceComplexLieInclusion F n v X) = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexPlaceComplexLieInclusion_tmul, complexPlaceComplexLieProjection_tmul,
      complexProjection_complexInclusion, Pi.single_eq_same]
  | add X Y hX hY => simp only [map_add, hX, hY]

/-- The actual universal enveloping lift of the real-place Lie inclusion. -/
def realPlaceEnvelopingInclusion (v : RP) :
    RealPlaceEnvelopingAlgebra n →ₐ[ℂ] EnvelopingAlgebra F n :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((envelopingGenerator F n).comp (realPlaceComplexLieInclusion F n v))

/-- The actual universal enveloping lift of the complex-place Lie inclusion. -/
def complexPlaceEnvelopingInclusion (v : CP) :
    ComplexPlaceEnvelopingAlgebra n →ₐ[ℂ] EnvelopingAlgebra F n :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((envelopingGenerator F n).comp (complexPlaceComplexLieInclusion F n v))

/-- The enveloping retraction induced by actual real-place evaluation. -/
def realPlaceEnvelopingProjection (v : RP) :
    EnvelopingAlgebra F n →ₐ[ℂ] RealPlaceEnvelopingAlgebra n :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((realPlaceEnvelopingGenerator n).comp (realPlaceComplexLieProjection F n v))

def complexPlaceEnvelopingProjection (v : CP) :
    EnvelopingAlgebra F n →ₐ[ℂ] ComplexPlaceEnvelopingAlgebra n :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((complexPlaceEnvelopingGenerator n).comp (complexPlaceComplexLieProjection F n v))

@[simp] theorem realPlaceEnvelopingInclusion_generator (v : RP) (X : ℂ ⊗[ℝ] RM) :
    realPlaceEnvelopingInclusion F n v (realPlaceEnvelopingGenerator n X) =
      envelopingGenerator F n (realPlaceComplexLieInclusion F n v X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ X

@[simp] theorem complexPlaceEnvelopingInclusion_generator (v : CP) (X : ℂ ⊗[ℝ] CM) :
    complexPlaceEnvelopingInclusion F n v (complexPlaceEnvelopingGenerator n X) =
      envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ X

@[simp] theorem realPlaceEnvelopingProjection_generator (v : RP)
    (X : ComplexLieAlgebra F n) :
    realPlaceEnvelopingProjection F n v (envelopingGenerator F n X) =
      realPlaceEnvelopingGenerator n (realPlaceComplexLieProjection F n v X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ X

@[simp] theorem complexPlaceEnvelopingProjection_generator (v : CP)
    (X : ComplexLieAlgebra F n) :
    complexPlaceEnvelopingProjection F n v (envelopingGenerator F n X) =
      complexPlaceEnvelopingGenerator n (complexPlaceComplexLieProjection F n v X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ X

/-- The actual enveloping projection retracts the actual place inclusion. -/
theorem realPlaceEnvelopingProjection_comp_inclusion (v : RP) :
    (realPlaceEnvelopingProjection F n v).comp (realPlaceEnvelopingInclusion F n v) =
      AlgHom.id ℂ (RealPlaceEnvelopingAlgebra n) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change realPlaceEnvelopingProjection F n v
    (realPlaceEnvelopingInclusion F n v (realPlaceEnvelopingGenerator n X)) =
      realPlaceEnvelopingGenerator n X
  rw [realPlaceEnvelopingInclusion_generator, realPlaceEnvelopingProjection_generator,
    realPlaceComplexLieProjection_inclusion]

theorem complexPlaceEnvelopingProjection_comp_inclusion (v : CP) :
    (complexPlaceEnvelopingProjection F n v).comp (complexPlaceEnvelopingInclusion F n v) =
      AlgHom.id ℂ (ComplexPlaceEnvelopingAlgebra n) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change complexPlaceEnvelopingProjection F n v
    (complexPlaceEnvelopingInclusion F n v (complexPlaceEnvelopingGenerator n X)) =
      complexPlaceEnvelopingGenerator n X
  rw [complexPlaceEnvelopingInclusion_generator, complexPlaceEnvelopingProjection_generator,
    complexPlaceComplexLieProjection_inclusion]

@[simp] theorem realPlaceEnvelopingProjection_inclusion (v : RP)
    (a : RealPlaceEnvelopingAlgebra n) :
    realPlaceEnvelopingProjection F n v (realPlaceEnvelopingInclusion F n v a) = a :=
  AlgHom.congr_fun (realPlaceEnvelopingProjection_comp_inclusion F n v) a

@[simp] theorem complexPlaceEnvelopingProjection_inclusion (v : CP)
    (a : ComplexPlaceEnvelopingAlgebra n) :
    complexPlaceEnvelopingProjection F n v (complexPlaceEnvelopingInclusion F n v a) = a :=
  AlgHom.congr_fun (complexPlaceEnvelopingProjection_comp_inclusion F n v) a

theorem realPlaceEnvelopingInclusion_injective (v : RP) :
    Function.Injective (realPlaceEnvelopingInclusion F n v) := by
  intro a b h
  simpa only [realPlaceEnvelopingProjection_inclusion] using
    congrArg (realPlaceEnvelopingProjection F n v) h

theorem complexPlaceEnvelopingInclusion_injective (v : CP) :
    Function.Injective (complexPlaceEnvelopingInclusion F n v) := by
  intro a b h
  simpa only [complexPlaceEnvelopingProjection_inclusion] using
    congrArg (complexPlaceEnvelopingProjection F n v) h

theorem realPlaceEnvelopingProjection_surjective (v : RP) :
    Function.Surjective (realPlaceEnvelopingProjection F n v) :=
  fun a => ⟨realPlaceEnvelopingInclusion F n v a,
    realPlaceEnvelopingProjection_inclusion F n v a⟩

theorem complexPlaceEnvelopingProjection_surjective (v : CP) :
    Function.Surjective (complexPlaceEnvelopingProjection F n v) :=
  fun a => ⟨complexPlaceEnvelopingInclusion F n v a,
    complexPlaceEnvelopingProjection_inclusion F n v a⟩

end Langlands.Global.ArchimedeanGL
