import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.Weil.Local.ExtensionGalois
import Langlands.Weil.Local.ExtensionResidue
import Langlands.LocalField.Normalization.Proof
import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Canonical field transport to the common algebraic closure

The existing image-field equivalence is upgraded to the canonical topological
algebra and unit-group equivalences, preserving normalized absolute values.
-/

noncomputable section

namespace Langlands.LocalClassField

open Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The actual image of the extension in the chosen closure, with its finiteness certificate. -/
def extensionFiniteIntermediate : FiniteIntermediateExtension F.Carrier :=
  ⟨extensionIntermediateField F E f, extensionIntermediateField_finiteDimensional F E f⟩

/-- Restrict the existing image-field equivalence to the specified p-adic base. -/
def extensionIntermediatePadicEquiv :
    letI := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
    E.Carrier ≃ₐ[Padic p] ((extensionFiniteIntermediate F E f).asPadicField (p := p)).Carrier := by
  letI := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  letI := extensionAlgebra F E f
  refine { (extensionIntermediateFieldEquiv F E f).toRingEquiv with commutes' := ?_ }
  intro a
  change extensionIntermediateFieldEquiv F E f (algebraMap (Padic p) E.Carrier a) =
    algebraMap F.Carrier (extensionIntermediateField F E f)
      (algebraMap (Padic p) F.Carrier a)
  rw [← f.commutes a]
  exact (extensionIntermediateFieldEquiv F E f).commutes _

@[simp] theorem extensionIntermediatePadicEquiv_coe (x : E.Carrier) :
    ((extensionIntermediatePadicEquiv F E f x :
      (extensionFiniteIntermediate F E f).field) : AlgebraicClosure F.Carrier) =
        extensionFieldEmbedding F E f x := rfl

/-- The image-field equivalence preserves the canonical spectral norm. -/
theorem extensionIntermediate_canonicalNorm (x : E.Carrier) :
    ((extensionFiniteIntermediate F E f).asPadicField (p := p)).canonicalNorm
      (extensionIntermediatePadicEquiv F E f x) = E.canonicalNorm x := by
  let := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  exact canonicalNorm_map E ((extensionFiniteIntermediate F E f).asPadicField (p := p))
    (extensionIntermediatePadicEquiv F E f).toAlgHom x

/-- The actual field isomorphism is a homeomorphism for the canonical topologies. -/
def extensionIntermediateContinuousAlgEquiv :
    letI := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
    letI := E.canonicalTopologicalData.topology
    letI := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
    E.Carrier ≃A[Padic p] ((extensionFiniteIntermediate F E f).asPadicField (p := p)).Carrier := by
  letI := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  letI := E.canonicalNormedField
  letI := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).canonicalNormedField
  exact
    { toAlgEquiv := extensionIntermediatePadicEquiv F E f
      continuous_toFun := (extension_isometry E
        ((extensionFiniteIntermediate F E f).asPadicField (p := p))
        (extensionIntermediatePadicEquiv F E f).toAlgHom).continuous
      continuous_invFun := (extension_isometry
        ((extensionFiniteIntermediate F E f).asPadicField (p := p)) E
        (extensionIntermediatePadicEquiv F E f).symm.toAlgHom).continuous }

/-- The actual topological group isomorphism on multiplicative units. -/
def extensionIntermediateUnitsEquiv :
    letI := E.canonicalTopologicalData.topology
    letI := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
    E.Carrierˣ ≃ₜ* (extensionFiniteIntermediate F E f).fieldˣ := by
  letI := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  letI := E.canonicalTopologicalData.topology
  letI := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
  exact
    { toMulEquiv := Units.mapEquiv (extensionIntermediatePadicEquiv F E f).toMulEquiv
      continuous_toFun := (extensionIntermediateContinuousAlgEquiv F E f).continuous.units_map _
      continuous_invFun :=
        (extensionIntermediateContinuousAlgEquiv F E f).symm.continuous.units_map _ }

/-- Preservation of the residue-cardinality normalized absolute value. -/
theorem extensionIntermediate_normalizedAbs (x : E.Carrier) :
    (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).normalizedAbs
      (extensionIntermediatePadicEquiv F E f x) =
        E.canonicalTopologicalData.normalizedAbs x := by
  let := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  let : Module (Padic p) ((extensionFiniteIntermediate F E f).asPadicField (p := p)).Carrier :=
    @Algebra.toModule _ _ _ _ ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  rw [PadicField.TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree,
    PadicField.TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree,
    extensionIntermediate_canonicalNorm]
  rw [(extensionIntermediatePadicEquiv F E f).toLinearEquiv.finrank_eq]

/-- The unit equivalence is induced by the existing field embedding. -/
@[simp] theorem extensionIntermediateUnitsEquiv_apply (x : E.Carrierˣ) :
    letI := E.canonicalTopologicalData.topology
    letI := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
    ((extensionIntermediateUnitsEquiv F E f x :
      (extensionFiniteIntermediate F E f).fieldˣ) :
      (extensionFiniteIntermediate F E f).field) =
        extensionIntermediatePadicEquiv F E f (x : E.Carrier) := rfl

/-- Inverse normalized absolute-value compatibility on the actual unit groups. -/
theorem extensionIntermediateUnitsEquiv_symm_normalizedAbs
    (x : (extensionFiniteIntermediate F E f).fieldˣ) :
    letI := E.canonicalTopologicalData.topology
    letI := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
    E.canonicalTopologicalData.normalizedAbs
      ((extensionIntermediateUnitsEquiv F E f).symm x : E.Carrier) =
        (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).normalizedAbs
          (x : (extensionFiniteIntermediate F E f).field) := by
  let := E.canonicalTopologicalData.topology
  let := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
  rw [← extensionIntermediate_normalizedAbs F E f]
  change (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).normalizedAbs
    ((extensionIntermediateUnitsEquiv F E f
      ((extensionIntermediateUnitsEquiv F E f).symm x) :
        (extensionFiniteIntermediate F E f).fieldˣ) :
        (extensionFiniteIntermediate F E f).field) = _
  rw [ContinuousMulEquiv.apply_symm_apply]

/-- Forward normalized absolute-value compatibility on the actual unit groups. -/
theorem extensionIntermediateUnitsEquiv_normalizedAbs (x : E.Carrierˣ) :
    letI := E.canonicalTopologicalData.topology
    letI := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
    (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).normalizedAbs
      ((extensionIntermediateUnitsEquiv F E f x :
        (extensionFiniteIntermediate F E f).fieldˣ) :
        (extensionFiniteIntermediate F E f).field) =
          E.canonicalTopologicalData.normalizedAbs (x : E.Carrier) :=
  extensionIntermediate_normalizedAbs F E f (x : E.Carrier)

end Langlands.LocalClassField

