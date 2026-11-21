import Langlands.Global.AdelicBlockScalarLieAction
import Langlands.Global.ArchimedeanCovarianceProof
import Langlands.Global.ArchimedeanOrbitDerivativeInterchange

/-! # The enveloping action on realized adelic block sections -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear NumberField
open ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "W" => smoothCompactFiniteSections F B S

local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
local instance : AddCommGroup W := Submodule.addCommGroup (smoothCompactFiniteSections F B S)

private theorem section_ext_of_slices {f g : W}
    (h : ∀ d, smoothScalarSlice F B S d f = smoothScalarSlice F B S d g) : f = g :=
  smoothScalarSlice_injective F B S (funext h)

private def realSectionDifferential : RealLieAlgebra F n →ₗ[ℝ] Module.End ℂ W where
  toFun := sectionDifferential F B S
  map_add' X Y := by
    apply LinearMap.ext
    intro f
    apply section_ext_of_slices F B S
    intro d
    simp only [LinearMap.add_apply, map_add, smoothScalarSlice_sectionDifferential,
      ← realSmoothLieAction_apply]
  map_smul' c X := by
    apply LinearMap.ext
    intro f
    apply section_ext_of_slices F B S
    intro d
    simp only [LinearMap.smul_apply, RingHom.id_apply, LinearMap.map_smul_of_tower,
      smoothScalarSlice_sectionDifferential, ← realSmoothLieAction_apply, map_smul]

private def complexSectionDifferential : ComplexLieAlgebra F n →ₗ[ℂ] Module.End ℂ W :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (realSectionDifferential F B S))

private theorem complexSectionDifferential_tmul (z : ℂ) (X : RealLieAlgebra F n) :
    complexSectionDifferential F B S (z ⊗ₜ[ℝ] X) = z • sectionDifferential F B S X :=
  rfl

private theorem smoothScalarSlice_complexSectionDifferential
    (X : ComplexLieAlgebra F n) (f : W) (d : FiniteAdelicGL F n) :
    smoothScalarSlice F B S d (complexSectionDifferential F B S X f) =
      complexSmoothLieAction F n X (smoothScalarSlice F B S d f) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexSectionDifferential_tmul, complexSmoothLieAction_tmul,
      LinearMap.smul_apply, map_smul, smoothScalarSlice_sectionDifferential]
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply, hX, hY]

private def complexSectionLieAction : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ W where
  __ := complexSectionDifferential F B S
  map_lie' := by
    intro X Y
    apply LinearMap.ext
    intro f
    apply section_ext_of_slices F B S
    intro d
    change smoothScalarSlice F B S d (complexSectionDifferential F B S ⁅X, Y⁆ f) =
      smoothScalarSlice F B S d
        (complexSectionDifferential F B S X (complexSectionDifferential F B S Y f) -
          complexSectionDifferential F B S Y (complexSectionDifferential F B S X f))
    simp only [map_sub, smoothScalarSlice_complexSectionDifferential]
    exact DFunLike.congr_fun ((complexSmoothLieAction F n).map_lie X Y) _

/-- The actual complex enveloping algebra acts on the smooth compact-finite scalar sections. -/
def sectionEnvelopingAction : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ W :=
  UniversalEnvelopingAlgebra.lift ℂ (complexSectionLieAction F B S)

@[simp]
theorem sectionEnvelopingAction_real_generator (X : RealLieAlgebra F n) :
    sectionEnvelopingAction F B S (envelopingGenerator F n (complexify F n X)) =
      sectionDifferential F B S X := by
  change UniversalEnvelopingAlgebra.lift ℂ (complexSectionLieAction F B S)
    (UniversalEnvelopingAlgebra.ι ℂ (complexify F n X)) = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change complexSectionDifferential F B S (complexify F n X) = _
  rw [complexify_apply, complexSectionDifferential_tmul, one_smul]

/-- Every fixed finite slice intertwines the enveloping action with smooth differentiation. -/
@[simp]
theorem smoothScalarSlice_sectionEnvelopingAction
    (a : EnvelopingAlgebra F n) (f : W) (d : FiniteAdelicGL F n) :
    smoothScalarSlice F B S d (sectionEnvelopingAction F B S a f) =
      ArchimedeanGL.envelopingAction F n a (smoothScalarSlice F B S d f) := by
  induction a using enveloping_real_left_induction F n with
  | h1 => simp only [map_one, Module.End.one_apply]
  | hadd a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | hsmul z a ha => simp only [map_smul, LinearMap.smul_apply, ha]
  | hgen X a ha =>
    simp only [map_mul, Module.End.mul_apply, sectionEnvelopingAction_real_generator,
      smoothScalarSlice_sectionDifferential, ArchimedeanGL.envelopingAction_real_generator, ha]

/-- Finite right translation commutes with the enveloping differential. -/
theorem smoothCompactFiniteAction_sectionEnvelopingAction
    (d : FiniteAdelicGL F n) (a : EnvelopingAlgebra F n) (f : W) :
    smoothCompactFiniteAction F B S d (sectionEnvelopingAction F B S a f) =
      sectionEnvelopingAction F B S a (smoothCompactFiniteAction F B S d f) := by
  apply section_ext_of_slices F B S
  intro b
  simp only [smoothScalarSlice_finiteAction, smoothScalarSlice_sectionEnvelopingAction]

/-- Infinite compact translation carries the differential to its adjoint conjugate. -/
theorem smoothCompactAction_sectionEnvelopingAction
    (k : standardInfiniteCompact F n) (a : EnvelopingAlgebra F n) (f : W) :
    smoothCompactAction F B S k (sectionEnvelopingAction F B S a f) =
      sectionEnvelopingAction F B S (envelopingConjugation F n k.val a)
        (smoothCompactAction F B S k f) := by
  apply section_ext_of_slices F B S
  intro d
  simp only [smoothScalarSlice_compactAction, smoothScalarSlice_sectionEnvelopingAction]
  exact envelopingRightCovariance F n k.val a (smoothScalarSlice F B S d f)

end Langlands.Global.AdelicBlockScalarSections
