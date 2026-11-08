import Langlands.Weil.Local.FiniteGaloisEquivariance
import Langlands.ClassFieldTheory.Local.Cohomology

/-! # The actual finite Galois Weil pushout cocycle -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

open LocalClassField LocalFactor.RankOne GroupExtensionPushout
open ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (hGal : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)

/-- A normalized section of the actual finite Galois Weil quotient. -/
def finiteGaloisSection :
    letI := extensionAlgebra F E f
    Section (finiteGaloisQuotient F E f hGal).toMonoidHom := by
  letI := extensionAlgebra F E f
  exact Section.ofSurjective (finiteGaloisQuotient_surjective F E f hGal)

variable (e : ReciprocityCandidate E)
  (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)

/-- The normalized factor cocycle obtained from the actual Weil quotient and inverse reciprocity. -/
def finiteGaloisCocycle :
    letI := extensionAlgebra F E f
    NormalizedTwoCocycle Gal(E.Carrier/F.Carrier) E.Carrierˣ := by
  letI := extensionAlgebra F E f
  letI := E.canonicalTopologicalData.topology
  exact (finiteGaloisSection F E f hGal).cocycle
    (finiteGaloisKernelReciprocity F E f hGal e).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he)

/-- The class of the actual Weil pushout in the existing relative cohomology group. -/
def finiteGaloisClass :
    letI := extensionAlgebra F E f
    relativeCohomology F.Carrier E.Carrier 2 := by
  letI := extensionAlgebra F E f
  exact NormalizedTwoCocycle.cohomologyClass (finiteGaloisCocycle F E f hGal e he)

/-- The continuous map from the actual local Weil group to its factor-cocycle extension. -/
def finiteGaloisPushout :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    localWeilGroup F →ₜ* (finiteGaloisCocycle F E f hGal e he).Extension := by
  letI := extensionAlgebra F E f
  letI := extensionAlgebra_finiteDimensional F E f
  letI := E.canonicalTopologicalData.topology
  exact (finiteGaloisSection F E f hGal).toContinuousMonoidHom
    (finiteGaloisKernelReciprocity F E f hGal e).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he)
    (finiteGaloisQuotient F E f hGal).continuous
    (finiteGaloisKernelReciprocity F E f hGal e).continuous

/-- Projection of the pushout is the actual finite Galois Weil quotient. -/
@[simp] theorem projection_finiteGaloisPushout (g : localWeilGroup F) :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    NormalizedTwoCocycle.Extension.projection (finiteGaloisCocycle F E f hGal e he)
      (finiteGaloisPushout F E f hGal e he g) = finiteGaloisQuotient F E f hGal g := rfl

/-- The projection acts through the specified embedding into the base algebraic closure. -/
theorem finiteGaloisPushout_projection_apply (g : localWeilGroup F) (x : E.Carrier) :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    extensionFieldEmbedding F E f
      (NormalizedTwoCocycle.Extension.projection (finiteGaloisCocycle F E f hGal e he)
        (finiteGaloisPushout F E f hGal e he g) x) =
      AlgEquiv.toAlgHom (localProjection F g) (extensionFieldEmbedding F E f x) :=
  finiteGaloisQuotient_apply F E f hGal g x

/-- On the extension Weil group the pushout is the unit inclusion after inverse reciprocity. -/
theorem finiteGaloisPushout_extensionWeilMap (y : localWeilGroup E) :
    let := extensionAlgebra F E f
    let := E.canonicalTopologicalData.topology
    finiteGaloisPushout F E f hGal e he (extensionWeilMap F E f y) =
      (NormalizedTwoCocycle.Extension.inl (finiteGaloisCocycle F E f hGal e he)
        (reciprocityUnits E e y))⁻¹ := by
  let := extensionAlgebra F E f
  let := extensionAlgebra_finiteDimensional F E f
  let := E.canonicalTopologicalData.topology
  have h := (finiteGaloisSection F E f hGal).toContinuousMonoidHom_kernel
    (finiteGaloisKernelReciprocity F E f hGal e).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he)
    (finiteGaloisQuotient F E f hGal).continuous
    (finiteGaloisKernelReciprocity F E f hGal e).continuous
    (finiteGaloisQuotientKernelEquiv F E f hGal y)
  change finiteGaloisPushout F E f hGal e he (extensionWeilMap F E f y) =
    NormalizedTwoCocycle.Extension.inl (finiteGaloisCocycle F E f hGal e he)
      (finiteGaloisKernelReciprocity F E f hGal e
        (finiteGaloisQuotientKernelEquiv F E f hGal y)) at h
  rw [finiteGaloisKernelReciprocity_apply, map_inv] at h
  exact h

/-- The actual cohomology class is independent of the choice of normalized section. -/
theorem finiteGaloisClass_eq_of_section
    (s : letI := extensionAlgebra F E f
      Section (finiteGaloisQuotient F E f hGal).toMonoidHom) :
    let := extensionAlgebra F E f
    let := E.canonicalTopologicalData.topology
    finiteGaloisClass F E f hGal e he =
      NormalizedTwoCocycle.cohomologyClass
        (s.cocycle (finiteGaloisKernelReciprocity F E f hGal e).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he)) := by
  let := extensionAlgebra F E f
  let := E.canonicalTopologicalData.topology
  exact (finiteGaloisSection F E f hGal).cohomologyClass_eq
    (finiteGaloisKernelReciprocity F E f hGal e).toMonoidHom
    (finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he) s

end Langlands.Weil.Local
