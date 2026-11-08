import Langlands.Weil.Local.FiniteGaloisReciprocity
import Langlands.ClassFieldTheory.Local.WeilReciprocityConjugation
import Langlands.LocalField.CanonicalTransport

/-! # Galois equivariance of geometric reciprocity on a finite Galois Weil kernel -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

open LocalClassField LocalFactor.RankOne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (hGal : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)

/-- The automorphism of the algebraic closure of `E` obtained by transporting the
Galois image of `g` through the chosen closure isomorphism. -/
def closureConjugation (g : localWeilGroup F) :
    AlgebraicClosure E.Carrier ≃+* AlgebraicClosure E.Carrier :=
  ((extensionClosureEquiv F E f).symm.trans
    (localProjection F g).toRingEquiv).trans (extensionClosureEquiv F E f)

/-- The closure automorphism evaluated through the closure isomorphism. -/
theorem closureConjugation_apply (g : localWeilGroup F) (x : AlgebraicClosure F.Carrier) :
    closureConjugation F E f g (extensionClosureEquiv F E f x) =
      extensionClosureEquiv F E f (AlgEquiv.toAlgHom (localProjection F g) x) := by
  change extensionClosureEquiv F E f (AlgEquiv.toAlgHom (localProjection F g)
    ((extensionClosureEquiv F E f).symm (extensionClosureEquiv F E f x))) = _
  rw [RingEquiv.symm_apply_apply]

/-- Its inverse is given by the inverse Galois image. -/
theorem closureConjugation_symm_apply (g : localWeilGroup F) (x : AlgebraicClosure F.Carrier) :
    (closureConjugation F E f g).symm (extensionClosureEquiv F E f x) =
      extensionClosureEquiv F E f (AlgEquiv.toAlgHom (localProjection F g)⁻¹ x) := by
  apply (closureConjugation F E f g).injective
  rw [RingEquiv.apply_symm_apply, closureConjugation_apply]
  congr 1
  change x = AlgEquiv.toAlgHom (localProjection F g * (localProjection F g)⁻¹) x
  rw [mul_inv_cancel]
  rfl

/-- On `E`, the closure automorphism is the finite Galois image of `g`. -/
theorem closureConjugation_algebraMap (g : localWeilGroup F) (x : E.Carrier) :
    closureConjugation F E f g (algebraMap E.Carrier (AlgebraicClosure E.Carrier) x) =
      algebraMap E.Carrier (AlgebraicClosure E.Carrier)
        (letI := extensionAlgebra F E f; finiteGaloisQuotient F E f hGal g x) := by
  let := extensionAlgebra F E f
  rw [← extensionClosureLift_fieldEmbedding F E f x, ← extensionClosureEquiv_apply,
    closureConjugation_apply, ← extensionClosureLift_fieldEmbedding F E f,
    ← extensionClosureEquiv_apply]
  congr 1
  exact (finiteGaloisQuotient_apply F E f hGal g x).symm

/-- The Galois image of a transported conjugate is conjugation by the closure automorphism. -/
theorem localProjection_finiteGaloisWeilConjugation (g : localWeilGroup F)
    (w : localWeilGroup E) (y : AlgebraicClosure E.Carrier) :
    AlgEquiv.toAlgHom (localProjection E (finiteGaloisWeilConjugation F E f hGal g w)) y =
      closureConjugation F E f g
        (AlgEquiv.toAlgHom (localProjection E w) ((closureConjugation F E f g).symm y)) := by
  obtain ⟨x, rfl⟩ := (extensionClosureEquiv F E f).surjective y
  have hc := congrArg (localProjection F)
    (extensionWeilMap_finiteGaloisWeilConjugation F E f hGal g w)
  rw [localProjection_extensionWeilMap, map_mul, map_mul, map_inv,
    localProjection_extensionWeilMap] at hc
  rw [closureConjugation_symm_apply]
  calc AlgEquiv.toAlgHom (localProjection E (finiteGaloisWeilConjugation F E f hGal g w))
        (extensionClosureEquiv F E f x)
      = extensionClosureLift F E f (AlgEquiv.toAlgHom (extensionGaloisMap F E f
          (localProjection E (finiteGaloisWeilConjugation F E f hGal g w))) x) :=
        (extensionClosureLift_galoisMap F E f _ x).symm
    _ = extensionClosureEquiv F E f (AlgEquiv.toAlgHom (localProjection F g)
          (AlgEquiv.toAlgHom (extensionGaloisMap F E f (localProjection E w))
            (AlgEquiv.toAlgHom (localProjection F g)⁻¹ x))) := by
        rw [hc]
        rfl
    _ = closureConjugation F E f g (extensionClosureLift F E f
          (AlgEquiv.toAlgHom (extensionGaloisMap F E f (localProjection E w))
            (AlgEquiv.toAlgHom (localProjection F g)⁻¹ x))) :=
        (closureConjugation_apply F E f g _).symm
    _ = _ := by
        rw [extensionClosureLift_galoisMap]
        rfl

/-- The base ring automorphism of `E` attached to `g` by the finite Galois quotient. -/
def baseConjugation (g : localWeilGroup F) : E.Carrier ≃+* E.Carrier :=
  letI := extensionAlgebra F E f
  (finiteGaloisQuotient F E f hGal g).toRingEquiv

/-- The base automorphism and the closure automorphism form a compatible pair. -/
theorem baseConjugation_compatible (g : localWeilGroup F) :
    (algebraMap E.Carrier (AlgebraicClosure E.Carrier)).comp
        (baseConjugation F E f hGal g).toRingHom =
      (closureConjugation F E f g).toRingHom.comp
        (algebraMap E.Carrier (AlgebraicClosure E.Carrier)) := by
  ext x
  exact (closureConjugation_algebraMap F E f hGal g x).symm

/-- The compatibility of Weil projections with the closure automorphism, in the
form `projection(c y)(θ x) = θ(projection(y)(x))`. -/
theorem localProjection_finiteGaloisWeilConjugation_closure (g : localWeilGroup F)
    (w : localWeilGroup E) (x : AlgebraicClosure E.Carrier) :
    AlgEquiv.toAlgHom (localProjection E (finiteGaloisWeilConjugation F E f hGal g w))
        (closureConjugation F E f g x) =
      closureConjugation F E f g (AlgEquiv.toAlgHom (localProjection E w) x) := by
  rw [localProjection_finiteGaloisWeilConjugation, RingEquiv.symm_apply_apply]

/-- The finite Galois automorphism, regarded as an automorphism over `Padic p`. -/
def padicGaloisEquiv (g : localWeilGroup F) : E.Carrier ≃ₐ[Padic p] E.Carrier :=
  letI := extensionAlgebra F E f
  haveI := extensionAlgebra_isScalarTower F E f
  (finiteGaloisQuotient F E f hGal g).restrictScalars (Padic p)

/-- The base automorphism is continuous for the canonical topology. -/
theorem continuous_baseConjugation (g : localWeilGroup F) :
    letI := E.canonicalTopologicalData.topology
    Continuous (baseConjugation F E f hGal g) := by
  let := E.canonicalNormedField
  exact (extension_isometry E E (padicGaloisEquiv F E f hGal g).toAlgHom).continuous

/-- Its inverse is continuous for the canonical topology. -/
theorem continuous_baseConjugation_symm (g : localWeilGroup F) :
    letI := E.canonicalTopologicalData.topology
    Continuous (baseConjugation F E f hGal g).symm := by
  let := E.canonicalNormedField
  exact (extension_isometry E E (padicGaloisEquiv F E f hGal g).symm.toAlgHom).continuous

/-- The base automorphism preserves the canonical integer order of units. -/
theorem orderHom_baseConjugation (g : localWeilGroup F) (a : E.Carrierˣ) :
    E.canonicalTopologicalData.orderHom
        (Units.mapEquiv (baseConjugation F E f hGal g).toMulEquiv a) =
      E.canonicalTopologicalData.orderHom a := by
  change Multiplicative.ofAdd (E.canonicalTopologicalData.ord
      (padicGaloisEquiv F E f hGal g a)) =
    Multiplicative.ofAdd (E.canonicalTopologicalData.ord a)
  rw [PadicField.CanonicalTransport.ord_map E E (padicGaloisEquiv F E f hGal g)]

/-- Geometric reciprocity is Galois equivariant for conjugation by `W_F`:
`e(g y g⁻¹) = σ_g(e(y))`, where `σ_g` is the finite Galois image of `g`. -/
theorem reciprocityUnits_finiteGaloisWeilConjugation (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    (g : localWeilGroup F) (w : localWeilGroup E) :
    letI := E.canonicalTopologicalData.topology
    reciprocityUnits E e (finiteGaloisWeilConjugation F E f hGal g w) =
      Units.mapEquiv (baseConjugation F E f hGal g).toMulEquiv (reciprocityUnits E e w) :=
  WeilReciprocityTransport.reciprocity_conjugation E (baseConjugation F E f hGal g)
    (closureConjugation F E f g) (baseConjugation_compatible F E f hGal g)
    (finiteGaloisWeilConjugation F E f hGal g)
    (localProjection_finiteGaloisWeilConjugation_closure F E f hGal g)
    E.canonicalTopologicalData (continuous_baseConjugation F E f hGal g)
    (continuous_baseConjugation_symm F E f hGal g) (orderHom_baseConjugation F E f hGal g)
    (localDegree_finiteGaloisWeilConjugation F E f hGal g) e ⟨he.1, he.2.1⟩ w

/-- The Galois action on units acts on the underlying field element. -/
theorem smul_units_val (σ : letI := extensionAlgebra F E f; Gal(E.Carrier/F.Carrier))
    (a : E.Carrierˣ) :
    letI := extensionAlgebra F E f
    ((σ • a : E.Carrierˣ) : E.Carrier) = σ (a : E.Carrier) := by
  let := extensionAlgebra F E f
  rfl

/-- The inverse reciprocity map on the finite Galois kernel is equivariant for
conjugation by `W_F` and the Galois action on `Eˣ`. This is the equivariance
premise of `GroupExtensionPushout.Section.cocycle`. -/
theorem finiteGaloisKernelReciprocity_conjugateKernel (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    (x : localWeilGroup F)
    (n : letI := extensionAlgebra F E f; (finiteGaloisQuotient F E f hGal).toMonoidHom.ker) :
    letI := extensionAlgebra F E f
    finiteGaloisKernelReciprocity F E f hGal e
        (GroupExtensionPushout.conjugateKernel (finiteGaloisQuotient F E f hGal).toMonoidHom x n) =
      finiteGaloisQuotient F E f hGal x • finiteGaloisKernelReciprocity F E f hGal e n := by
  let := extensionAlgebra F E f
  let := E.canonicalTopologicalData.topology
  let j := finiteGaloisQuotientKernelEquiv F E f hGal
  obtain ⟨y, rfl⟩ := j.surjective n
  have hconj : GroupExtensionPushout.conjugateKernel (finiteGaloisQuotient F E f hGal).toMonoidHom
      x (j y) = j (finiteGaloisWeilConjugation F E f hGal x y) := by
    apply Subtype.ext
    rw [finiteGaloisQuotientKernelEquiv_apply, extensionWeilMap_finiteGaloisWeilConjugation]
    rfl
  rw [hconj, finiteGaloisKernelReciprocity_apply, finiteGaloisKernelReciprocity_apply,
    reciprocityUnits_finiteGaloisWeilConjugation F E f hGal e he x y]
  apply Units.ext
  rw [smul_units_val, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀]
  rfl

end Langlands.Weil.Local
