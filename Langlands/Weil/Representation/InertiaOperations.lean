import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.SumsTensor
import Langlands.Weil.Representation.Dual
import Langlands.Weil.Representation.Twist
import Langlands.Weil.Representation.Determinant
import Langlands.Weil.Representation.Invariants
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Intrinsic open-inertia certificates for representation constructions -/

noncomputable section

universe uG uV uW

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (I : Subgroup G)

/-- An injective intertwiner transports an open inertia kernel to its source. -/
theorem hasOpenInertiaKernel_of_injective
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uW} ℂ G}
    (f : B.representation.IntertwiningMap A.representation) (hf : Function.Injective f)
    (hA : A.HasOpenInertiaKernel I) : B.HasOpenInertiaKernel I := by
  apply Subgroup.isOpen_mono (H₁ := A.inertiaKernel I) (H₂ := B.inertiaKernel I) _ hA
  intro i hi
  change A.representation (i : G) = 1 at hi
  change B.representation (i : G) = 1
  apply LinearMap.ext
  intro v
  apply hf
  have h := Representation.IntertwiningMap.isIntertwining _ _ f (i : G) v
  simpa [hi] using h

/-- Direct sum has an open inertia kernel containing the intersection of the two kernels. -/
theorem hasOpenInertiaKernel_sum
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uW} ℂ G}
    (hA : A.HasOpenInertiaKernel I) (hB : B.HasOpenInertiaKernel I) :
    (sum A B).HasOpenInertiaKernel I := by
  apply Subgroup.isOpen_mono
    (H₁ := A.inertiaKernel I ⊓ B.inertiaKernel I) (H₂ := (sum A B).inertiaKernel I) _
    (hA.inter hB)
  intro i hi
  have ha : A.representation (i : G) = 1 := hi.1
  have hb : B.representation (i : G) = 1 := hi.2
  change (A.representation (i : G)).prodMap (B.representation (i : G)) = 1
  rw [ha, hb]
  rfl

/-- Tensor product has an open inertia kernel containing the intersection of the two kernels. -/
theorem hasOpenInertiaKernel_tensor
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uW} ℂ G}
    (hA : A.HasOpenInertiaKernel I) (hB : B.HasOpenInertiaKernel I) :
    (tensor A B).HasOpenInertiaKernel I := by
  apply Subgroup.isOpen_mono
    (H₁ := A.inertiaKernel I ⊓ B.inertiaKernel I) (H₂ := (tensor A B).inertiaKernel I) _
    (hA.inter hB)
  intro i hi
  have ha : A.representation (i : G) = 1 := hi.1
  have hb : B.representation (i : G) = 1 := hi.2
  change TensorProduct.map (A.representation (i : G)) (B.representation (i : G)) = 1
  rw [ha, hb]
  exact TensorProduct.map_one

/-- The full algebraic dual has open inertia kernel. -/
theorem hasOpenInertiaKernel_dual
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (hA : A.HasOpenInertiaKernel I) : A.dual.HasOpenInertiaKernel I := by
  apply Subgroup.isOpen_mono (H₁ := A.inertiaKernel I) (H₂ := A.dual.inertiaKernel I) _ hA
  intro i hi
  have hi' : A.representation ((i : G)⁻¹) = 1 := (A.inertiaKernel I).inv_mem hi
  change A.representation.dual (i : G) = 1
  apply LinearMap.ext
  intro ℓ
  apply LinearMap.ext
  intro v
  change ℓ (A.representation ((i : G)⁻¹) v) = ℓ v
  rw [hi']
  rfl

/-- Twisting preserves the algebraic inertia convention when the character kernel on inertia is open. -/
theorem hasOpenInertiaKernel_twist (χ : G →* ℂˣ)
    (hχ : IsOpen ((χ.comp I.subtype).ker : Set I))
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (hA : A.HasOpenInertiaKernel I) : (twist χ A).HasOpenInertiaKernel I := by
  apply Subgroup.isOpen_mono
    (H₁ := A.inertiaKernel I ⊓ (χ.comp I.subtype).ker)
    (H₂ := (twist χ A).inertiaKernel I) _ (hA.inter hχ)
  intro i hi
  have ha : A.representation (i : G) = 1 := hi.1
  have hc : χ (i : G) = 1 := hi.2
  change (χ (i : G) : ℂ) • A.representation (i : G) = 1
  rw [ha, hc, Units.val_one, one_smul]

/-- The scalar determinant representation has open inertia kernel. -/
theorem hasOpenInertiaKernel_determinant
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (hA : A.HasOpenInertiaKernel I) : A.determinant.HasOpenInertiaKernel I := by
  apply Subgroup.isOpen_mono
    (H₁ := A.inertiaKernel I) (H₂ := A.determinant.inertiaKernel I) _ hA
  intro i hi
  have ha : A.representation (i : G) = 1 := hi
  change A.determinant.representation (i : G) = 1
  apply LinearMap.ext
  intro x
  change LinearMap.det (A.representation (i : G)) * (show ℂ from x) = (show ℂ from x)
  rw [ha, map_one]
  exact one_mul (show ℂ from x)

/-- Direct sum on actual open-inertia objects, including the preservation certificate. -/
def openInertiaSum (A : OpenInertiaObjects.{uG, uV} I)
    (B : OpenInertiaObjects.{uG, uW} I) : OpenInertiaObjects.{uG, max uV uW} I :=
  ⟨sum A.val B.val, hasOpenInertiaKernel_sum I A.property B.property⟩

/-- Tensor product on actual open-inertia objects. -/
def openInertiaTensor (A : OpenInertiaObjects.{uG, uV} I)
    (B : OpenInertiaObjects.{uG, uW} I) : OpenInertiaObjects.{uG, max uV uW} I :=
  ⟨tensor A.val B.val, hasOpenInertiaKernel_tensor I A.property B.property⟩

/-- Algebraic dual on actual open-inertia objects. -/
def openInertiaDual (A : OpenInertiaObjects.{uG, uV} I) : OpenInertiaObjects.{uG, uV} I :=
  ⟨dual A.val, hasOpenInertiaKernel_dual I A.property⟩

/-- A twist on actual open-inertia objects with an explicit inertia-character hypothesis. -/
def openInertiaTwist (χ : G →* ℂˣ) (hχ : IsOpen ((χ.comp I.subtype).ker : Set I))
    (A : OpenInertiaObjects.{uG, uV} I) : OpenInertiaObjects.{uG, uV} I :=
  ⟨twist χ A.val, hasOpenInertiaKernel_twist I χ hχ A.property⟩

/-- Scalar determinant on actual open-inertia objects. -/
def openInertiaDeterminant (A : OpenInertiaObjects.{uG, uV} I) : OpenInertiaObjects.{uG, 0} I :=
  ⟨determinant A.val, hasOpenInertiaKernel_determinant I A.property⟩

/-- Normal-subgroup invariant spaces remain open-inertia objects. -/
def openInertiaInvariants (J : Subgroup G) [J.Normal]
    (A : OpenInertiaObjects.{uG, uV} I) : OpenInertiaObjects.{uG, uV} I :=
  ⟨invariants J A.val,
    hasOpenInertiaKernel_of_injective I (invariantsInclusion J A.val)
      Subtype.val_injective A.property⟩

end Langlands.FiniteRepresentation
